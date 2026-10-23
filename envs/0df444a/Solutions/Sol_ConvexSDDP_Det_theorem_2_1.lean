-- Prove2me | solution 1 for ConvexSDDP.Det.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T04:14:07.956994+00:00
-- url     : https://prove2.me/submissions/598206f6-f7b1-448a-a0ae-c44c86a0ae39

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model

set_option autoImplicit false

open Filter Topology

namespace SDDPAux

open ConvexSDDP.Det
open Classical

variable {d p : ℕ}

/-! ### Unfolding lemmas -/

lemma V_lt (M : Model d p) {t : ℕ} (ht : t < M.T) (y : EuclideanSpace ℝ (Fin d)) :
    M.V t y = if y ∈ M.X t then ⨅ u ∈ M.U t y, (M.C t y u + M.V (t + 1) (M.f t (y, u)))
      else ⊤ := by
  rw [Model.V, if_pos ht]

lemma V_ge (M : Model d p) {t : ℕ} (ht : M.T ≤ t) (y : EuclideanSpace ℝ (Fin d)) :
    M.V t y = if y ∈ M.X M.T then M.VT y else ⊤ := by
  rw [Model.V, if_neg (not_lt.2 ht)]

lemma V_eq_T (M : Model d p) {t : ℕ} (ht : M.T ≤ t) (y : EuclideanSpace ℝ (Fin d)) :
    M.V t y = M.V M.T y := by
  rw [V_ge M ht, V_ge M le_rfl]

lemma V_off (M : Model d p) {t : ℕ} (ht : t ≤ M.T) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∉ M.X t) : M.V t y = ⊤ := by
  rcases lt_or_eq_of_le ht with h | h
  · rw [V_lt M h, if_neg hy]
  · subst h; rw [V_ge M le_rfl, if_neg hy]

lemma V_mem_lt (M : Model d p) {t : ℕ} (ht : t < M.T) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ M.X t) : M.V t y = ⨅ u ∈ M.U t y, M.W t y u := by
  rw [V_lt M ht, if_pos hy] <;> rfl

section approxLemmas

variable (M : Model d p) (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d))

lemma approx_ge (k : ℕ) {t : ℕ} (ht : M.T ≤ t) (y : EuclideanSpace ℝ (Fin d)) :
    M.approx θ β x k t y = M.V M.T y := by
  cases k <;> simp [Model.approx, ht]

lemma approx_zero_lt {t : ℕ} (ht : t < M.T) (y : EuclideanSpace ℝ (Fin d)) :
    M.approx θ β x 0 t y = ⊥ := by
  simp [Model.approx, not_le.2 ht]

lemma approx_succ_lt (k : ℕ) {t : ℕ} (ht : t < M.T) (y : EuclideanSpace ℝ (Fin d)) :
    M.approx θ β x (k + 1) t y = max (M.approx θ β x k t y)
      (θ (k + 1) t + ((inner ℝ (β (k + 1) t) (y - x (k + 1) t) : ℝ) : EReal)) := by
  simp only [Model.approx, if_neg (not_le.2 ht)]

lemma approx_le_succ (k t : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    M.approx θ β x k t y ≤ M.approx θ β x (k + 1) t y := by
  by_cases ht : M.T ≤ t
  · rw [approx_ge M θ β x k ht, approx_ge M θ β x (k + 1) ht]
  · rw [approx_succ_lt M θ β x k (not_le.1 ht)]; exact le_max_left _ _

lemma approx_mono {k k' : ℕ} (h : k ≤ k') (t : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    M.approx θ β x k t y ≤ M.approx θ β x k' t y :=
  (monotone_nat_of_le_succ (fun n => approx_le_succ M θ β x n t y)) h

lemma stage_mono {k k' : ℕ} (h : k ≤ k') (t : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    M.stageValue θ β x k t y ≤ M.stageValue θ β x k' t y := by
  unfold Model.stageValue
  exact iInf₂_mono fun v _ => add_le_add le_rfl (approx_mono M θ β x h _ _)

end approxLemmas

/-- The extended value `inf_{u ∈ U_t(y)} W_t(y,u)`. -/
noncomputable def G (M : Model d p) (t : ℕ) (y : EuclideanSpace ℝ (Fin d)) : EReal :=
  ⨅ u ∈ M.U t y, M.W t y u

/-- Two-point convexity of an extended-valued function, stated with real upper bounds. -/
def EpiCvx (φ : EuclideanSpace ℝ (Fin d) → EReal) : Prop :=
  ∀ y₁ y₂ : EuclideanSpace ℝ (Fin d), ∀ r₁ r₂ : ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    φ y₁ ≤ (r₁ : EReal) → φ y₂ ≤ (r₂ : EReal) →
      φ (a • y₁ + b • y₂) ≤ ((a * r₁ + b * r₂ : ℝ) : EReal)

lemma ereal_le_of_eps {z : EReal} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → z ≤ ((c + ε : ℝ) : EReal)) : z ≤ (c : EReal) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨w, hcw, hwz⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hcw' : c < w := EReal.coe_lt_coe_iff.1 hcw
  have h1 := h (w - c) (sub_pos.2 hcw')
  have e : c + (w - c) = w := by ring
  rw [e] at h1
  exact absurd (h1.trans_lt hwz) (lt_irrefl _)

lemma split_lt {p' q : EReal} {r : ℝ} (hp : p' ≠ ⊥) (hq : q ≠ ⊥) (h : p' + q < (r : EReal)) :
    ∃ a b : ℝ, p' = a ∧ q = b ∧ a + b < r := by
  have hpt : p' ≠ ⊤ := by
    intro h'
    rw [h', EReal.top_add_of_ne_bot hq] at h
    exact absurd h (not_lt.2 le_top)
  have hqt : q ≠ ⊤ := by
    intro h'
    rw [h', EReal.add_top_of_ne_bot hp] at h
    exact absurd h (not_lt.2 le_top)
  refine ⟨p'.toReal, q.toReal, (EReal.coe_toReal hpt hp).symm, (EReal.coe_toReal hqt hq).symm, ?_⟩
  rw [← EReal.coe_lt_coe_iff, EReal.coe_add, EReal.coe_toReal hpt hp, EReal.coe_toReal hqt hq]
  exact h

section H1Lemmas

variable {M : Model d p}

lemma C_ne_bot (hH1 : M.H1) {t : ℕ} (ht : t < M.T) (y : EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin p)) : M.C t y v ≠ ⊥ :=
  (hH1.2.2.2.2.1 t ht).1.1 (y, v)

lemma V_T_ne_bot (hH1 : M.H1) (y : EuclideanSpace ℝ (Fin d)) : M.V M.T y ≠ ⊥ := by
  rw [V_ge M le_rfl]
  split_ifs
  · exact hH1.2.2.2.2.2.1.1.1 y
  · exact top_ne_bot

lemma mem_Xp (hH1 : M.H1) {t : ℕ} (ht : t < M.T) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ M.X t) : y ∈ M.Xp t := by
  have hδ : 0 < M.δ t := (hH1.2.2.2.2.2.2.2.2 t ht).1
  show ∃ a ∈ M.X t, ∃ b, (b ∈ vectorSpan ℝ (M.X t) ∧ ‖b‖ < M.δ t) ∧ y = a + b
  exact ⟨y, hy, 0, ⟨Submodule.zero_mem _, by rw [norm_zero]; exact hδ⟩, (add_zero y).symm⟩

lemma V_ne_top (hH1 : M.H1) : ∀ n t, t + n = M.T → ∀ y ∈ M.X t, M.V t y ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
    intro t ht y hy
    simp only [add_zero] at ht
    subst ht
    rw [V_ge M le_rfl, if_pos hy]
    exact hH1.2.2.2.2.2.2.1 y hy
  | succ n ih =>
    intro t ht y hy
    have htT : t < M.T := by omega
    obtain ⟨v, hv, hf⟩ := (hH1.2.2.2.2.2.2.2.2 t htT).2.2 y (mem_Xp hH1 htT hy)
    have hCv := (hH1.2.2.2.2.2.2.2.2 t htT).2.1 y (mem_Xp hH1 htT hy) v hv
    have hV1 := ih (t + 1) (by omega) _ hf
    rw [V_mem_lt M htT hy]
    refine ne_top_of_le_ne_top ?_ (iInf₂_le v hv)
    exact (EReal.add_lt_top hCv.ne hV1).ne

lemma V_ne_top' (hH1 : M.H1) {t : ℕ} (ht : t ≤ M.T) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ M.X t) : M.V t y ≠ ⊤ :=
  V_ne_top hH1 (M.T - t) t (by omega) y hy

lemma Xp_convex (hH1 : M.H1) {t : ℕ} (ht : t < M.T) : Convex ℝ (M.Xp t) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  obtain ⟨p₁, hp₁, q₁, hq₁, rfl⟩ := hz₁
  obtain ⟨p₂, hp₂, q₂, hq₂, rfl⟩ := hz₂
  have hq₁' : q₁ ∈ vectorSpan ℝ (M.X t) ∧ ‖q₁‖ < M.δ t := hq₁
  have hq₂' : q₂ ∈ vectorSpan ℝ (M.X t) ∧ ‖q₂‖ < M.δ t := hq₂
  show ∃ a' ∈ M.X t, ∃ b', (b' ∈ vectorSpan ℝ (M.X t) ∧ ‖b'‖ < M.δ t) ∧
    a • (p₁ + q₁) + b • (p₂ + q₂) = a' + b'
  refine ⟨a • p₁ + b • p₂, (hH1.2.1 t ht.le).1 hp₁ hp₂ ha hb hab, a • q₁ + b • q₂, ⟨?_, ?_⟩,
    by rw [smul_add, smul_add]; abel⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hq₁'.1) (Submodule.smul_mem _ _ hq₂'.1)
  · have hn : ‖a • q₁ + b • q₂‖ ≤ a * ‖q₁‖ + b * ‖q₂‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have hm := max_lt hq₁'.2 hq₂'.2
    have h1 : a * ‖q₁‖ ≤ a * max ‖q₁‖ ‖q₂‖ := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h2 : b * ‖q₂‖ ≤ b * max ‖q₁‖ ‖q₂‖ := mul_le_mul_of_nonneg_left (le_max_right _ _) hb
    have h3 : a * max ‖q₁‖ ‖q₂‖ + b * max ‖q₁‖ ‖q₂‖ = max ‖q₁‖ ‖q₂‖ := by
      rw [← add_mul, hab, one_mul]
    linarith

lemma VT_cvx (hH1 : M.H1) : EpiCvx (M.V M.T) := by
  intro y₁ y₂ r₁ r₂ a b ha hb hab h₁ h₂
  have mem : ∀ {y : EuclideanSpace ℝ (Fin d)} {r : ℝ}, M.V M.T y ≤ (r : EReal) →
      y ∈ M.X M.T ∧ M.VT y ≤ (r : EReal) := by
    intro y r h
    by_cases hy : y ∈ M.X M.T
    · rw [V_ge M le_rfl, if_pos hy] at h; exact ⟨hy, h⟩
    · rw [V_ge M le_rfl, if_neg hy] at h; exact absurd h (not_le.2 (EReal.coe_lt_top r))
  obtain ⟨hy₁, h₁'⟩ := mem h₁
  obtain ⟨hy₂, h₂'⟩ := mem h₂
  have hc := (hH1.2.1 M.T le_rfl).1 hy₁ hy₂ ha hb hab
  rw [V_ge M le_rfl, if_pos hc]
  have := hH1.2.2.2.2.2.1.2.2 (x := (y₁, r₁)) (y := (y₂, r₂)) h₁' h₂' ha hb hab
  simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
  exact this

set_option maxHeartbeats 1000000 in
lemma G_cvx (hH1 : M.H1) {t : ℕ} (ht : t < M.T) (hV : EpiCvx (M.V (t + 1)))
    (hVb : ∀ z, M.V (t + 1) z ≠ ⊥) : EpiCvx (G M t) := by
  intro y₁ y₂ r₁ r₂ a b ha hb hab h₁ h₂
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using h₂
  rcases hb.eq_or_lt with hb0 | hb0
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using h₁
  apply ereal_le_of_eps
  intro ε hε
  have hCp := hH1.2.2.2.2.1 t ht
  have hUp := hH1.2.2.2.1 t ht
  have pick : ∀ {y : EuclideanSpace ℝ (Fin d)} {r : ℝ}, G M t y ≤ (r : EReal) →
      ∃ v ∈ M.U t y, ∃ c w : ℝ, M.C t y v = c ∧ M.V (t + 1) (M.f t (y, v)) = w ∧
        c + w < r + ε := by
    intro y r h
    have hlt : G M t y < ((r + ε : ℝ) : EReal) :=
      lt_of_le_of_lt h (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨v, hv⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hvU, hW⟩ := iInf_lt_iff.1 hv
    obtain ⟨c, w, hc, hw, hcw⟩ := split_lt (C_ne_bot hH1 ht y v) (hVb _) hW
    exact ⟨v, hvU, c, w, hc, hw, hcw⟩
  obtain ⟨v₁, hv₁, c₁, w₁, hc₁, hw₁, hcw₁⟩ := pick h₁
  obtain ⟨v₂, hv₂, c₂, w₂, hc₂, hw₂, hcw₂⟩ := pick h₂
  have hvmem : a • v₁ + b • v₂ ∈ M.U t (a • y₁ + b • y₂) := by
    have := hUp.1 y₁ y₂ v₁ hv₁ v₂ hv₂ b hb0 (by linarith)
    rwa [show 1 - b = a by linarith] at this
  have hCc : M.C t (a • y₁ + b • y₂) (a • v₁ + b • v₂) ≤ ((a * c₁ + b * c₂ : ℝ) : EReal) := by
    have m₁ : ((y₁, v₁), c₁) ∈ {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p)) × ℝ |
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C t z.1 z.2) q.1 ≤
          (q.2 : EReal)} := by
      show M.C t y₁ v₁ ≤ (c₁ : EReal); rw [hc₁]
    have m₂ : ((y₂, v₂), c₂) ∈ {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p)) × ℝ |
        (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C t z.1 z.2) q.1 ≤
          (q.2 : EReal)} := by
      show M.C t y₂ v₂ ≤ (c₂ : EReal); rw [hc₂]
    have := hCp.2.2 m₁ m₂ ha hb hab
    simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
    exact this
  have hfeq : M.f t (a • y₁ + b • y₂, a • v₁ + b • v₂) =
      a • M.f t (y₁, v₁) + b • M.f t (y₂, v₂) := by
    rw [show (a • y₁ + b • y₂, a • v₁ + b • v₂) = a • (y₁, v₁) + b • (y₂, v₂) by simp,
      map_add, map_smul, map_smul]
  have hVc : M.V (t + 1) (M.f t (a • y₁ + b • y₂, a • v₁ + b • v₂)) ≤
      ((a * w₁ + b * w₂ : ℝ) : EReal) := by
    rw [hfeq]; exact hV _ _ w₁ w₂ a b ha hb hab hw₁.le hw₂.le
  have hε2 : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  calc G M t (a • y₁ + b • y₂) ≤ M.W t (a • y₁ + b • y₂) (a • v₁ + b • v₂) := iInf₂_le _ hvmem
    _ ≤ ((a * c₁ + b * c₂ : ℝ) : EReal) + ((a * w₁ + b * w₂ : ℝ) : EReal) := add_le_add hCc hVc
    _ = ((a * (c₁ + w₁) + b * (c₂ + w₂) : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
    _ ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        have h1 := mul_le_mul_of_nonneg_left hcw₁.le ha
        have h2 := mul_le_mul_of_nonneg_left hcw₂.le hb
        nlinarith

lemma V_cvx_of_G (hH1 : M.H1) {t : ℕ} (ht : t < M.T) (hG : EpiCvx (G M t)) :
    EpiCvx (M.V t) := by
  intro y₁ y₂ r₁ r₂ a b ha hb hab h₁ h₂
  have mem : ∀ {y : EuclideanSpace ℝ (Fin d)} {r : ℝ}, M.V t y ≤ (r : EReal) → y ∈ M.X t := by
    intro y r h
    by_contra hy
    rw [V_off M ht.le hy] at h
    exact absurd h (not_le.2 (EReal.coe_lt_top r))
  have hy₁ := mem h₁
  have hy₂ := mem h₂
  rw [V_mem_lt M ht hy₁] at h₁
  rw [V_mem_lt M ht hy₂] at h₂
  rw [V_mem_lt M ht ((hH1.2.1 t ht.le).1 hy₁ hy₂ ha hb hab)]
  exact hG y₁ y₂ r₁ r₂ a b ha hb hab h₁ h₂

end H1Lemmas

section RunLemmas

variable {M : Model d p} {θ : ℕ → ℕ → EReal} {β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)}
  {u : ℕ → ℕ → EuclideanSpace ℝ (Fin p)}

lemma run_mem (hH1 : M.H1) (hrun : M.IsRun x u θ β) (k : ℕ) :
    ∀ t ≤ M.T, x (k + 1) t ∈ M.X t := by
  intro t
  induction t with
  | zero => intro _; rw [(hrun k).1]; exact hH1.2.2.1
  | succ t ih =>
    intro ht
    have htT : t < M.T := by omega
    obtain ⟨⟨hu, -⟩, -, hx, -⟩ := (hrun k).2 t htT
    rw [hx]; exact hu.2

lemma theta_eq (hrun : M.IsRun x u θ β) (k : ℕ) {t : ℕ} (ht : t < M.T) :
    θ (k + 1) t = M.stageValue θ β x k t (x (k + 1) t) := by
  obtain ⟨⟨hu, hmin⟩, hθ, -, -⟩ := (hrun k).2 t ht
  rw [hθ]
  unfold Model.stageValue
  apply le_antisymm
  · exact le_iInf₂ (fun v hv => hmin v hv)
  · exact iInf₂_le _ hu

lemma stage_le_G (hH1 : M.H1) {k t : ℕ} (ht : t < M.T)
    (hA : ∀ z, M.approx θ β x k (t + 1) z ≤ M.V (t + 1) z) (y : EuclideanSpace ℝ (Fin d)) :
    M.stageValue θ β x k t y ≤ G M t y := by
  unfold Model.stageValue G
  refine le_iInf₂ (fun v hv => ?_)
  by_cases hf : M.f t (y, v) ∈ M.X (t + 1)
  · have hvU : v ∈ M.Ut t y := by
      simp only [Model.Ut, Set.mem_setOf_eq]; exact ⟨hv, hf⟩
    exact (iInf₂_le v hvU).trans (add_le_add le_rfl (hA _))
  · have hW : M.W t y v = ⊤ := by
      show M.C t y v + M.V (t + 1) (M.f t (y, v)) = ⊤
      rw [V_off M (by omega) hf]
      exact EReal.add_top_of_ne_bot (C_ne_bot hH1 ht y v)
    rw [hW]; exact le_top

lemma approx_le_V (hH1 : M.H1) (hrun : M.IsRun x u θ β) :
    ∀ k t y, M.approx θ β x k t y ≤ M.V t y := by
  intro k
  induction k with
  | zero =>
    intro t y
    by_cases ht : M.T ≤ t
    · rw [approx_ge M θ β x 0 ht, V_eq_T M ht]
    · rw [approx_zero_lt M θ β x (not_le.1 ht)]; exact bot_le
  | succ k ih =>
    intro t y
    by_cases ht : M.T ≤ t
    · rw [approx_ge M θ β x _ ht, V_eq_T M ht]
    · have ht' := not_le.1 ht
      rw [approx_succ_lt M θ β x k ht']
      refine max_le (ih t y) ?_
      by_cases hy : y ∈ M.X t
      · have hya : y ∈ affineSpan ℝ (M.X t) := mem_affineSpan ℝ hy
        exact ((((hrun k).2 t ht').2.2.2.2 y hya).trans (stage_le_G hH1 ht' (ih (t + 1)) y)).trans
          (le_of_eq (V_mem_lt M ht' hy).symm)
      · rw [V_off M ht'.le hy]; exact le_top

lemma approx_ne_bot (hH1 : M.H1) (hrun : M.IsRun x u θ β) :
    ∀ n t, t + n = M.T → ∃ K, ∀ k ≥ K, ∀ y, M.approx θ β x k t y ≠ ⊥ := by
  intro n
  induction n with
  | zero =>
    intro t ht
    refine ⟨0, fun k _ y => ?_⟩
    simp only [add_zero] at ht
    subst ht
    rw [approx_ge M θ β x k le_rfl]
    exact V_T_ne_bot hH1 y
  | succ n ih =>
    intro t ht
    have htT : t < M.T := by omega
    obtain ⟨K, hK⟩ := ih (t + 1) (by omega)
    refine ⟨K + 1, fun k hk y => ?_⟩
    have hθ : θ (K + 1) t ≠ ⊥ := by
      obtain ⟨-, hθ, hx, -⟩ := (hrun K).2 t htT
      rw [hθ]
      unfold Model.Wapprox
      rw [← hx]
      exact EReal.add_ne_bot_iff.2 ⟨C_ne_bot hH1 htT _ _, hK K le_rfl _⟩
    refine ne_bot_of_le_ne_bot ?_ (approx_mono M θ β x hk t y)
    rw [approx_succ_lt M θ β x K htT]
    refine ne_bot_of_le_ne_bot ?_ (le_max_right _ _)
    exact EReal.add_ne_bot_iff.2 ⟨hθ, EReal.coe_ne_bot _⟩

lemma approx_ne_bot' (hH1 : M.H1) (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t ≤ M.T) :
    ∃ K, ∀ k ≥ K, ∀ y, M.approx θ β x k t y ≠ ⊥ :=
  approx_ne_bot hH1 hrun (M.T - t) t (by omega)

lemma V_ne_bot (hH1 : M.H1) (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t ≤ M.T)
    (y : EuclideanSpace ℝ (Fin d)) : M.V t y ≠ ⊥ := by
  obtain ⟨K, hK⟩ := approx_ne_bot' hH1 hrun ht
  exact ne_bot_of_le_ne_bot (hK K le_rfl y) (approx_le_V hH1 hrun K t y)

lemma approx_le_stage (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t < M.T) :
    ∀ k {y}, y ∈ affineSpan ℝ (M.X t) → M.approx θ β x k t y ≤ M.stageValue θ β x k t y := by
  intro k
  induction k with
  | zero => intro y _; rw [approx_zero_lt M θ β x ht]; exact bot_le
  | succ k ih =>
    intro y hy
    rw [approx_succ_lt M θ β x k ht]
    exact max_le ((ih hy).trans (stage_mono M θ β x (Nat.le_succ k) t y))
      ((((hrun k).2 t ht).2.2.2.2 y hy).trans (stage_mono M θ β x (Nat.le_succ k) t y))

lemma V_cvx_all (hH1 : M.H1) (hrun : M.IsRun x u θ β) :
    ∀ n s, s + n = M.T → EpiCvx (M.V s) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    simp only [add_zero] at hs
    subst hs
    exact VT_cvx hH1
  | succ n ih =>
    intro s hs
    have hsT : s < M.T := by omega
    exact V_cvx_of_G hH1 hsT
      (G_cvx hH1 hsT (ih (s + 1) (by omega)) (V_ne_bot hH1 hrun (t := s + 1) (by omega)))

set_option maxHeartbeats 1000000 in
open Pointwise in
lemma G_bdd (hH1 : M.H1) (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t < M.T) :
    ∃ S : ℝ, ∀ y ∈ M.X t, ∀ b ∈ vectorSpan ℝ (M.X t), ‖b‖ ≤ M.δ t / 2 →
      G M t (y + b) ≤ (S : EReal) := by
  have hδ : 0 < M.δ t := (hH1.2.2.2.2.2.2.2.2 t ht).1
  have hXc := hH1.2.1 t ht.le
  have hcvx : EpiCvx (G M t) :=
    G_cvx hH1 ht (V_cvx_all hH1 hrun (M.T - (t + 1)) (t + 1) (by omega))
      (V_ne_bot hH1 hrun (t := t + 1) ht)
  have hfin_top : ∀ z ∈ M.Xp t, G M t z ≠ ⊤ := by
    intro z hz
    obtain ⟨v, hv, hf⟩ := (hH1.2.2.2.2.2.2.2.2 t ht).2.2 z hz
    have hCv := (hH1.2.2.2.2.2.2.2.2 t ht).2.1 z hz v hv
    refine ne_top_of_le_ne_top ?_ (iInf₂_le v hv)
    exact (EReal.add_lt_top hCv.ne (V_ne_top' hH1 (t := t + 1) ht hf)).ne
  obtain ⟨K, hK⟩ := approx_ne_bot' hH1 hrun ht.le
  have hfin_bot : ∀ z ∈ affineSpan ℝ (M.X t), G M t z ≠ ⊥ := by
    intro z hz
    refine ne_bot_of_le_ne_bot (hK K le_rfl z) ?_
    exact (approx_le_stage hrun ht K hz).trans
      (stage_le_G hH1 ht (fun w => approx_le_V hH1 hrun K (t + 1) w) z)
  have hXp_aff : ∀ z ∈ M.Xp t, z ∈ affineSpan ℝ (M.X t) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    have hb' : b ∈ (affineSpan ℝ (M.X t)).direction := by
      rw [direction_affineSpan]; exact hb.1
    have := AffineSubspace.vadd_mem_of_mem_direction hb' (mem_affineSpan ℝ ha)
    rwa [vadd_eq_add, add_comm] at this
  have hx1 : x 1 t ∈ M.X t := run_mem hH1 hrun 0 t ht.le
  let D : Set (vectorSpan ℝ (M.X t)) :=
    {w | x 1 t + (w : EuclideanSpace ℝ (Fin d)) ∈ M.Xp t}
  let Gr : vectorSpan ℝ (M.X t) → ℝ := fun w => (G M t (x 1 t + (w : EuclideanSpace ℝ (Fin d)))).toReal
  have hGr : ∀ w ∈ D, G M t (x 1 t + (w : EuclideanSpace ℝ (Fin d))) = (Gr w : EReal) :=
    fun w hw => (EReal.coe_toReal (hfin_top _ hw) (hfin_bot _ (hXp_aff _ hw))).symm
  have hcomb : ∀ (w₁ w₂ : vectorSpan ℝ (M.X t)) (a b : ℝ), a + b = 1 →
      a • (x 1 t + (w₁ : EuclideanSpace ℝ (Fin d))) + b • (x 1 t + (w₂ : EuclideanSpace ℝ (Fin d)))
        = x 1 t + ((a • w₁ + b • w₂ : vectorSpan ℝ (M.X t)) : EuclideanSpace ℝ (Fin d)) := by
    intro w₁ w₂ a b hab
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, smul_add, smul_add,
      show a • x 1 t + a • (w₁ : EuclideanSpace ℝ (Fin d)) + (b • x 1 t + b • (w₂ : EuclideanSpace ℝ (Fin d)))
        = (a + b) • x 1 t + (a • (w₁ : EuclideanSpace ℝ (Fin d)) + b • (w₂ : EuclideanSpace ℝ (Fin d)))
        by rw [add_smul]; abel, hab, one_smul]
  have hDconv : Convex ℝ D := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    show x 1 t + _ ∈ M.Xp t
    rw [← hcomb w₁ w₂ a b hab]
    exact Xp_convex hH1 ht hw₁ hw₂ ha hb hab
  have hconvOn : ConvexOn ℝ D Gr := by
    refine ⟨hDconv, fun w₁ hw₁ w₂ hw₂ a b ha hb hab => ?_⟩
    have h := hcvx _ _ (Gr w₁) (Gr w₂) a b ha hb hab (hGr w₁ hw₁).le (hGr w₂ hw₂).le
    rw [hcomb w₁ w₂ a b hab] at h
    have hmem : a • w₁ + b • w₂ ∈ D := hDconv hw₁ hw₂ ha hb hab
    rw [hGr _ hmem] at h
    simpa [smul_eq_mul] using EReal.coe_le_coe_iff.1 h
  have hDopen : IsOpen D := by
    rw [Metric.isOpen_iff]
    intro w hw
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    have hb' : b ∈ vectorSpan ℝ (M.X t) ∧ ‖b‖ < M.δ t := hb
    refine ⟨M.δ t - ‖b‖, sub_pos.2 hb'.2, fun w' hw' => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hw'
    have hn : ‖((w' : EuclideanSpace ℝ (Fin d)) - w)‖ = ‖w' - w‖ := rfl
    show ∃ a' ∈ M.X t, ∃ b', (b' ∈ vectorSpan ℝ (M.X t) ∧ ‖b'‖ < M.δ t) ∧
      x 1 t + (w' : EuclideanSpace ℝ (Fin d)) = a' + b'
    refine ⟨a, ha, b + ((w' : EuclideanSpace ℝ (Fin d)) - w), ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.add_mem _ hb'.1 (Submodule.sub_mem _ w'.2 w.2)
    · have := norm_add_le b ((w' : EuclideanSpace ℝ (Fin d)) - w)
      linarith
    · calc x 1 t + (w' : EuclideanSpace ℝ (Fin d))
          = (x 1 t + w) + ((w' : EuclideanSpace ℝ (Fin d)) - w) := by abel
        _ = a + (b + ((w' : EuclideanSpace ℝ (Fin d)) - w)) := by rw [hab, add_assoc]
  have hcont : ContinuousOn Gr D := hconvOn.continuousOn hDopen
  obtain ⟨R, hR⟩ := hXc.2.isBounded.exists_norm_le
  let Kx : Set (vectorSpan ℝ (M.X t)) := {w | x 1 t + (w : EuclideanSpace ℝ (Fin d)) ∈ M.X t}
  have hKx : IsCompact Kx := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact IsClosed.preimage (continuous_const.add continuous_subtype_val) hXc.2.isClosed
    · refine isBounded_iff_forall_norm_le.2 ⟨R + ‖x 1 t‖, fun w hw => ?_⟩
      have h1 := hR _ hw
      have h2 : ‖w‖ = ‖(x 1 t + (w : EuclideanSpace ℝ (Fin d))) - x 1 t‖ := by
        rw [add_sub_cancel_left]; rfl
      have h3 := norm_sub_le (x 1 t + (w : EuclideanSpace ℝ (Fin d))) (x 1 t)
      linarith
  have hKc : IsCompact (Kx + Metric.closedBall (0 : vectorSpan ℝ (M.X t)) (M.δ t / 2)) :=
    hKx.add (isCompact_closedBall _ _)
  have hKD : Kx + Metric.closedBall (0 : vectorSpan ℝ (M.X t)) (M.δ t / 2) ⊆ D := by
    intro w hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Set.mem_add.1 hw
    rw [mem_closedBall_zero_iff] at hw₂
    have hn : ‖(w₂ : EuclideanSpace ℝ (Fin d))‖ = ‖w₂‖ := rfl
    show ∃ a' ∈ M.X t, ∃ b', (b' ∈ vectorSpan ℝ (M.X t) ∧ ‖b'‖ < M.δ t) ∧
      x 1 t + ((w₁ + w₂ : vectorSpan ℝ (M.X t)) : EuclideanSpace ℝ (Fin d)) = a' + b'
    refine ⟨x 1 t + (w₁ : EuclideanSpace ℝ (Fin d)), hw₁, (w₂ : EuclideanSpace ℝ (Fin d)),
      ⟨w₂.2, by linarith⟩, ?_⟩
    rw [Submodule.coe_add, add_assoc]
  obtain ⟨S, hS⟩ := hKc.bddAbove_image (hcont.mono hKD)
  refine ⟨S, fun y hy b hb hbn => ?_⟩
  have hyx : y - x 1 t ∈ vectorSpan ℝ (M.X t) := by
    rw [← vsub_eq_sub]; exact vsub_mem_vectorSpan ℝ hy hx1
  have hwK : (⟨y - x 1 t, hyx⟩ + ⟨b, hb⟩ : vectorSpan ℝ (M.X t)) ∈
      Kx + Metric.closedBall (0 : vectorSpan ℝ (M.X t)) (M.δ t / 2) := by
    refine Set.mem_add.2 ⟨⟨y - x 1 t, hyx⟩, ?_, ⟨b, hb⟩, ?_, rfl⟩
    · show x 1 t + (y - x 1 t) ∈ M.X t
      rw [add_sub_cancel]; exact hy
    · rw [mem_closedBall_zero_iff]; exact hbn
  have hyb : y + b = x 1 t + (((⟨y - x 1 t, hyx⟩ + ⟨b, hb⟩ : vectorSpan ℝ (M.X t))) :
      EuclideanSpace ℝ (Fin d)) := by
    rw [Submodule.coe_add]
    show y + b = x 1 t + ((y - x 1 t) + b)
    abel
  rw [hyb, hGr _ (hKD hwK)]
  exact EReal.coe_le_coe_iff.2 (hS ⟨_, hwK, rfl⟩)

set_option maxHeartbeats 1000000 in
lemma beta_bdd (hH1 : M.H1) (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t < M.T) :
    ∃ L : ℝ, ∀ j, ‖β j t‖ ≤ L := by
  have hδ : 0 < M.δ t := (hH1.2.2.2.2.2.2.2.2 t ht).1
  obtain ⟨S, hS⟩ := G_bdd hH1 hrun ht
  obtain ⟨K, hK⟩ := approx_ne_bot' hH1 hrun (t := t + 1) ht
  obtain ⟨R, hR⟩ := (hH1.2.1 t ht.le).2.isBounded.exists_norm_le
  have hθfin : ∀ k ≥ K, θ (k + 1) t ≠ ⊥ ∧ θ (k + 1) t ≠ ⊤ := by
    intro k hk
    obtain ⟨-, hθ, hxs, -⟩ := (hrun k).2 t ht
    constructor
    · rw [hθ]
      unfold Model.Wapprox
      rw [← hxs]
      exact EReal.add_ne_bot_iff.2 ⟨C_ne_bot hH1 ht _ _, hK k hk _⟩
    · refine ne_top_of_le_ne_top (V_ne_top' hH1 ht.le (run_mem hH1 hrun k t ht.le)) ?_
      rw [theta_eq hrun k ht]
      exact (stage_le_G hH1 ht (fun w => approx_le_V hH1 hrun k (t + 1) w) _).trans
        (le_of_eq (V_mem_lt M ht (run_mem hH1 hrun k t ht.le)).symm)
  have hθ0e : θ (K + 1) t = (((θ (K + 1) t).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (hθfin K le_rfl).2 (hθfin K le_rfl).1).symm
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (θ (K + 1) t).toReal - ‖β (K + 1) t‖ * (2 * R) := ⟨_, rfl⟩
  have hlow : ∀ k ≥ K + 1, (m : EReal) ≤ θ (k + 1) t := by
    intro k hk
    have hxk := run_mem hH1 hrun k t ht.le
    rw [theta_eq hrun k ht]
    refine le_trans ?_ (approx_le_stage hrun ht k (mem_affineSpan ℝ hxk))
    refine le_trans ?_ (approx_mono M θ β x hk t _)
    rw [approx_succ_lt M θ β x K ht]
    refine le_trans ?_ (le_max_right _ _)
    rw [hθ0e, ← EReal.coe_add, EReal.coe_le_coe_iff, hm]
    have h1 := abs_real_inner_le_norm (β (K + 1) t) (x (k + 1) t - x (K + 1) t)
    have h2 : ‖x (k + 1) t - x (K + 1) t‖ ≤ 2 * R := by
      have := norm_sub_le (x (k + 1) t) (x (K + 1) t)
      have := hR _ hxk
      have := hR _ (run_mem hH1 hrun K t ht.le)
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (β (K + 1) t))
    have h4 := (abs_le.1 h1).1
    linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (S - m) * 2 / M.δ t := ⟨_, rfl⟩
  have hup : ∀ k ≥ K + 1, ‖β (k + 1) t‖ ≤ max B 0 := by
    intro k hk
    by_cases hβ : β (k + 1) t = 0
    · rw [hβ, norm_zero]; exact le_max_right _ _
    refine le_trans ?_ (le_max_left _ _)
    have hβn : 0 < ‖β (k + 1) t‖ := norm_pos_iff.2 hβ
    have hβne : ‖β (k + 1) t‖ ≠ 0 := hβn.ne'
    obtain ⟨-, -, -, hβs, hcut⟩ := (hrun k).2 t ht
    have hxk := run_mem hH1 hrun k t ht.le
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = M.δ t / (2 * ‖β (k + 1) t‖) := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hbmem : c • β (k + 1) t ∈ vectorSpan ℝ (M.X t) := Submodule.smul_mem _ _ hβs
    have hbn : ‖c • β (k + 1) t‖ = M.δ t / 2 := by
      rw [norm_smul, Real.norm_of_nonneg hc0, hc]; field_simp
    have hyaff : x (k + 1) t + c • β (k + 1) t ∈ affineSpan ℝ (M.X t) := by
      have hb' : c • β (k + 1) t ∈ (affineSpan ℝ (M.X t)).direction := by
        rw [direction_affineSpan]; exact hbmem
      have := AffineSubspace.vadd_mem_of_mem_direction hb' (mem_affineSpan ℝ hxk)
      rwa [vadd_eq_add, add_comm] at this
    have h1 := hcut _ hyaff
    rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h2 := (stage_le_G hH1 ht (fun w => approx_le_V hH1 hrun k (t + 1) w) _).trans
      (hS _ hxk _ hbmem hbn.le)
    have h3 := (add_le_add (hlow k hk)
      (le_refl (((c * ‖β (k + 1) t‖ ^ 2 : ℝ)) : EReal))).trans (h1.trans h2)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have h4 : c * ‖β (k + 1) t‖ ^ 2 = M.δ t / 2 * ‖β (k + 1) t‖ := by
      rw [hc]; field_simp
    rw [h4] at h3
    rw [hB, le_div_iff₀ hδ]
    nlinarith
  refine ⟨max B 0 + ∑ j ∈ Finset.range (K + 2), ‖β j t‖, fun j => ?_⟩
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (K + 2), ‖β j t‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  by_cases hj : j < K + 2
  · have h1 := Finset.single_le_sum (f := fun j => ‖β j t‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.2 hj)
    have h2 := le_max_right B 0
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have := hup k (by omega)
    linarith

lemma approx_lip {t : ℕ} (ht : t < M.T) {L : ℝ} (hL : ∀ j, ‖β j t‖ ≤ L) :
    ∀ k (y z : EuclideanSpace ℝ (Fin d)),
      M.approx θ β x k t y ≤ M.approx θ β x k t z + ((L * ‖y - z‖ : ℝ) : EReal) := by
  intro k
  induction k with
  | zero => intro y z; rw [approx_zero_lt M θ β x ht]; exact bot_le
  | succ k ih =>
    intro y z
    rw [approx_succ_lt M θ β x k ht, approx_succ_lt M θ β x k ht]
    refine max_le ((ih y z).trans (add_le_add (le_max_left _ _) le_rfl)) ?_
    refine le_trans ?_ (add_le_add (le_max_right _ _) le_rfl)
    rw [add_assoc, ← EReal.coe_add]
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
    have e : inner ℝ (β (k + 1) t) (y - x (k + 1) t) =
        inner ℝ (β (k + 1) t) (z - x (k + 1) t) + inner ℝ (β (k + 1) t) (y - z) := by
      rw [← inner_add_right]; congr 1; abel
    rw [e]
    have h1 := real_inner_le_norm (β (k + 1) t) (y - z)
    have h2 : ‖β (k + 1) t‖ * ‖y - z‖ ≤ L * ‖y - z‖ :=
      mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)
    linarith

end RunLemmas

lemma incr_point {a : ℕ → EReal} (hmono : Monotone a) {B : EReal} (hB : ∀ k, a k ≤ B)
    (hBt : B ≠ ⊤) {K : ℕ} (hK : a K ≠ ⊥) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, a (k + 1) ≤ a k + (ε : EReal) := by
  have hlim := tendsto_atTop_iSup hmono
  have hlt : (⨆ k, a k) ≠ ⊤ := ne_top_of_le_ne_top hBt (iSup_le hB)
  have hlb : (⨆ k, a k) ≠ ⊥ := ne_bot_of_le_ne_bot hK (le_iSup a K)
  have hco := EReal.coe_toReal hlt hlb
  have hlt' : (((⨆ k, a k).toReal - ε : ℝ) : EReal) < ⨆ k, a k := by
    calc (((⨆ k, a k).toReal - ε : ℝ) : EReal) < (((⨆ k, a k).toReal : ℝ) : EReal) :=
          EReal.coe_lt_coe_iff.2 (by linarith)
      _ = ⨆ k, a k := hco
  filter_upwards [hlim.eventually (lt_mem_nhds hlt')] with k hk
  calc a (k + 1) ≤ ⨆ k, a k := le_iSup a (k + 1)
    _ = (((⨆ k, a k).toReal - ε : ℝ) : EReal) + (ε : EReal) := by
        rw [← EReal.coe_add, sub_add_cancel, hco]
    _ ≤ a k + (ε : EReal) := add_le_add hk.le le_rfl

section RunLemmas2

variable {M : Model d p} {θ : ℕ → ℕ → EReal} {β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)}
  {u : ℕ → ℕ → EuclideanSpace ℝ (Fin p)}

set_option maxHeartbeats 1000000 in
lemma approx_incr (hH1 : M.H1) (hrun : M.IsRun x u θ β) {s : ℕ} (hs : s < M.T) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ y ∈ M.X s,
      M.approx θ β x (k + 1) s y ≤ M.approx θ β x k s y + (ε : EReal) := by
  obtain ⟨L0, hL0⟩ := beta_bdd hH1 hrun hs
  have hL : ∀ j, ‖β j s‖ ≤ max L0 0 + 1 := fun j => by
    have := hL0 j; have := le_max_left L0 0; linarith
  have hLpos : 0 < max L0 0 + 1 := by have := le_max_right L0 0; linarith
  have hlip := approx_lip (M := M) (θ := θ) (x := x) hs hL
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ε / (3 * (max L0 0 + 1)) := ⟨_, rfl⟩
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hLρ : (max L0 0 + 1) * ρ = ε / 3 := by rw [hρ]; field_simp
  obtain ⟨c, hcX, hcfin, hcover⟩ := finite_cover_balls_of_compact (hH1.2.1 s hs.le).2 hρpos
  obtain ⟨K, hK⟩ := approx_ne_bot' hH1 hrun hs.le
  have hpt : ∀ y ∈ M.X s, ∀ᶠ k in atTop,
      M.approx θ β x (k + 1) s y ≤ M.approx θ β x k s y + ((ε / 3 : ℝ) : EReal) := by
    intro y hy
    exact incr_point (a := fun k => M.approx θ β x k s y)
      (fun _ _ h => approx_mono M θ β x h s y) (fun k => approx_le_V hH1 hrun k s y)
      (V_ne_top' hH1 hs.le hy) (hK K le_rfl y) (by positivity)
  have hall := (Filter.eventually_all_finite hcfin).2 (fun c' hc' => hpt c' (hcX hc'))
  filter_upwards [hall] with k hk y hy
  obtain ⟨c', hc', hyc⟩ := Set.mem_iUnion₂.1 (hcover hy)
  have hd : ‖y - c'‖ < ρ := by rw [← dist_eq_norm]; exact hyc
  have hd' : ‖c' - y‖ < ρ := by rw [norm_sub_rev]; exact hd
  have e1 := mul_le_mul_of_nonneg_left hd.le hLpos.le
  have e2 := mul_le_mul_of_nonneg_left hd'.le hLpos.le
  calc M.approx θ β x (k + 1) s y
      ≤ M.approx θ β x (k + 1) s c' + (((max L0 0 + 1) * ‖y - c'‖ : ℝ) : EReal) := hlip _ y c'
    _ ≤ (M.approx θ β x k s c' + ((ε / 3 : ℝ) : EReal)) +
          (((max L0 0 + 1) * ‖y - c'‖ : ℝ) : EReal) := add_le_add (hk c' hc') le_rfl
    _ ≤ ((M.approx θ β x k s y + (((max L0 0 + 1) * ‖c' - y‖ : ℝ) : EReal)) +
          ((ε / 3 : ℝ) : EReal)) + (((max L0 0 + 1) * ‖y - c'‖ : ℝ) : EReal) :=
        add_le_add (add_le_add (hlip k c' y) le_rfl) le_rfl
    _ = M.approx θ β x k s y + (((max L0 0 + 1) * ‖c' - y‖ + ε / 3 +
          (max L0 0 + 1) * ‖y - c'‖ : ℝ) : EReal) := by
        simp only [EReal.coe_add, add_assoc]
    _ ≤ M.approx θ β x k s y + (ε : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))

set_option maxHeartbeats 1000000 in
lemma step (hH1 : M.H1) (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t < M.T)
    (hprev : Tendsto (fun k => (M.V (t + 1) (x (k + 1) (t + 1))).toReal -
      (M.approx θ β x k (t + 1) (x (k + 1) (t + 1))).toReal) atTop (𝓝 0)) :
    Tendsto (fun k => (M.W t (x (k + 1) t) (u (k + 1) t)).toReal -
      (M.V t (x (k + 1) t)).toReal) atTop (𝓝 0) ∧
    Tendsto (fun k => (M.V t (x (k + 1) t)).toReal -
      (M.approx θ β x (k + 1) t (x (k + 1) t)).toReal) atTop (𝓝 0) ∧
    (∀ᶠ k in atTop, M.W t (x (k + 1) t) (u (k + 1) t) ≠ ⊤ ∧
      M.W t (x (k + 1) t) (u (k + 1) t) ≠ ⊥ ∧
      M.approx θ β x (k + 1) t (x (k + 1) t) ≠ ⊥ ∧
      M.approx θ β x (k + 1) t (x (k + 1) t) ≠ ⊤) := by
  obtain ⟨K, hK⟩ := approx_ne_bot' hH1 hrun (t := t + 1) ht
  have key : ∀ k ≥ K,
      (M.W t (x (k + 1) t) (u (k + 1) t) ≠ ⊤ ∧ M.W t (x (k + 1) t) (u (k + 1) t) ≠ ⊥ ∧
        M.approx θ β x (k + 1) t (x (k + 1) t) ≠ ⊥ ∧
        M.approx θ β x (k + 1) t (x (k + 1) t) ≠ ⊤) ∧
      (0 ≤ (M.W t (x (k + 1) t) (u (k + 1) t)).toReal - (M.V t (x (k + 1) t)).toReal ∧
       (M.W t (x (k + 1) t) (u (k + 1) t)).toReal - (M.V t (x (k + 1) t)).toReal ≤
         (M.V (t + 1) (x (k + 1) (t + 1))).toReal -
           (M.approx θ β x k (t + 1) (x (k + 1) (t + 1))).toReal ∧
       0 ≤ (M.V t (x (k + 1) t)).toReal - (M.approx θ β x (k + 1) t (x (k + 1) t)).toReal ∧
       (M.V t (x (k + 1) t)).toReal - (M.approx θ β x (k + 1) t (x (k + 1) t)).toReal ≤
         (M.V (t + 1) (x (k + 1) (t + 1))).toReal -
           (M.approx θ β x k (t + 1) (x (k + 1) (t + 1))).toReal) := by
    intro k hk
    obtain ⟨⟨hu, -⟩, hθ, hxs, -, -⟩ := (hrun k).2 t ht
    have hxX := run_mem hH1 hrun k t ht.le
    have hx'X := run_mem hH1 hrun k (t + 1) ht
    have hc_bot := C_ne_bot hH1 ht (x (k + 1) t) (u (k + 1) t)
    have han_bot := hK k hk (x (k + 1) (t + 1))
    have hvn_top := V_ne_top' hH1 (t := t + 1) ht hx'X
    have hvn_bot := V_ne_bot hH1 hrun (t := t + 1) ht (x (k + 1) (t + 1))
    have han_le := approx_le_V hH1 hrun k (t + 1) (x (k + 1) (t + 1))
    have han_top := ne_top_of_le_ne_top hvn_top han_le
    have ha_top := V_ne_top' hH1 ht.le hxX
    have ha_bot := V_ne_bot hH1 hrun ht.le (x (k + 1) t)
    have hθeq : θ (k + 1) t = M.C t (x (k + 1) t) (u (k + 1) t) +
        M.approx θ β x k (t + 1) (x (k + 1) (t + 1)) := by
      rw [hθ, hxs]; rfl
    have hWeq : M.W t (x (k + 1) t) (u (k + 1) t) = M.C t (x (k + 1) t) (u (k + 1) t) +
        M.V (t + 1) (x (k + 1) (t + 1)) := by
      rw [hxs]; rfl
    have hθa : θ (k + 1) t ≤ M.V t (x (k + 1) t) := by
      rw [theta_eq hrun k ht]
      exact (stage_le_G hH1 ht (fun w => approx_le_V hH1 hrun k (t + 1) w) _).trans
        (le_of_eq (V_mem_lt M ht hxX).symm)
    have hc_top : M.C t (x (k + 1) t) (u (k + 1) t) ≠ ⊤ := by
      intro h
      rw [hθeq, h, EReal.top_add_of_ne_bot han_bot] at hθa
      exact ha_top (top_le_iff.1 hθa)
    have hθA : θ (k + 1) t ≤ M.approx θ β x (k + 1) t (x (k + 1) t) := by
      rw [approx_succ_lt M θ β x k ht]
      refine le_trans (le_of_eq ?_) (le_max_right _ _)
      rw [sub_self, inner_zero_right, EReal.coe_zero, add_zero]
    have hAa := approx_le_V hH1 hrun (k + 1) t (x (k + 1) t)
    have haW : M.V t (x (k + 1) t) ≤ M.W t (x (k + 1) t) (u (k + 1) t) := by
      rw [V_mem_lt M ht hxX]; exact iInf₂_le _ hu.1
    have hθ_bot : θ (k + 1) t ≠ ⊥ := by
      rw [hθeq]; exact EReal.add_ne_bot_iff.2 ⟨hc_bot, han_bot⟩
    have hA_bot := ne_bot_of_le_ne_bot hθ_bot hθA
    have hA_top := ne_top_of_le_ne_top ha_top hAa
    have hW_top : M.W t (x (k + 1) t) (u (k + 1) t) ≠ ⊤ := by
      rw [hWeq]; exact (EReal.add_lt_top hc_top hvn_top).ne
    have hW_bot : M.W t (x (k + 1) t) (u (k + 1) t) ≠ ⊥ := by
      rw [hWeq]; exact EReal.add_ne_bot_iff.2 ⟨hc_bot, hvn_bot⟩
    have hθ_top : θ (k + 1) t ≠ ⊤ := ne_top_of_le_ne_top ha_top hθa
    have r1 := EReal.toReal_le_toReal hθA hθ_bot hA_top
    have r2 := EReal.toReal_le_toReal hAa hA_bot ha_top
    have r3 := EReal.toReal_le_toReal haW ha_bot hW_top
    have e1 : (θ (k + 1) t).toReal = (M.C t (x (k + 1) t) (u (k + 1) t)).toReal +
        (M.approx θ β x k (t + 1) (x (k + 1) (t + 1))).toReal := by
      rw [hθeq, EReal.toReal_add hc_top hc_bot han_top han_bot]
    have e2 : (M.W t (x (k + 1) t) (u (k + 1) t)).toReal =
        (M.C t (x (k + 1) t) (u (k + 1) t)).toReal + (M.V (t + 1) (x (k + 1) (t + 1))).toReal := by
      rw [hWeq, EReal.toReal_add hc_top hc_bot hvn_top hvn_bot]
    refine ⟨⟨hW_top, hW_bot, hA_bot, hA_top⟩, ?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · exact squeeze_zero' (eventually_atTop.2 ⟨K, fun k hk => (key k hk).2.1⟩)
      (eventually_atTop.2 ⟨K, fun k hk => (key k hk).2.2.1⟩) hprev
  · exact squeeze_zero' (eventually_atTop.2 ⟨K, fun k hk => (key k hk).2.2.2.1⟩)
      (eventually_atTop.2 ⟨K, fun k hk => (key k hk).2.2.2.2⟩) hprev
  · exact eventually_atTop.2 ⟨K, fun k hk => (key k hk).1⟩

lemma gap_step (hH1 : M.H1) (hrun : M.IsRun x u θ β) {t : ℕ} (ht : t < M.T)
    (hprev : Tendsto (fun k => (M.V (t + 1) (x (k + 1) (t + 1))).toReal -
      (M.approx θ β x k (t + 1) (x (k + 1) (t + 1))).toReal) atTop (𝓝 0)) :
    Tendsto (fun k => (M.V t (x (k + 1) t)).toReal -
      (M.approx θ β x k t (x (k + 1) t)).toReal) atTop (𝓝 0) := by
  obtain ⟨-, h2, -⟩ := step hH1 hrun ht hprev
  obtain ⟨K, hK⟩ := approx_ne_bot' hH1 hrun ht.le
  have hinc : Tendsto (fun k => (M.approx θ β x (k + 1) t (x (k + 1) t)).toReal -
      (M.approx θ β x k t (x (k + 1) t)).toReal) atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
      have hxX := run_mem hH1 hrun k t ht.le
      have h1 := approx_le_succ M θ β x k t (x (k + 1) t)
      have hb := hK k hk (x (k + 1) t)
      have htop := ne_top_of_le_ne_top (V_ne_top' hH1 ht.le hxX)
        (approx_le_V hH1 hrun (k + 1) t (x (k + 1) t))
      have := EReal.toReal_le_toReal h1 hb htop
      linarith
    · filter_upwards [approx_incr hH1 hrun ht (a / 2) (by linarith), eventually_ge_atTop K]
        with k hk hkK
      have hxX := run_mem hH1 hrun k t ht.le
      have h1 := hk _ hxX
      have hb := hK k hkK (x (k + 1) t)
      have hb' := hK (k + 1) (by omega) (x (k + 1) t)
      have htop := ne_top_of_le_ne_top (V_ne_top' hH1 ht.le hxX)
        (approx_le_V hH1 hrun k t (x (k + 1) t))
      have := EReal.toReal_le_toReal h1 hb' (EReal.add_lt_top htop (EReal.coe_ne_top _)).ne
      rw [EReal.toReal_add htop hb (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe] at this
      linarith
  have e : (fun k => (M.V t (x (k + 1) t)).toReal - (M.approx θ β x k t (x (k + 1) t)).toReal) =
      (fun k => ((M.V t (x (k + 1) t)).toReal -
        (M.approx θ β x (k + 1) t (x (k + 1) t)).toReal) +
        ((M.approx θ β x (k + 1) t (x (k + 1) t)).toReal -
          (M.approx θ β x k t (x (k + 1) t)).toReal)) := by
    funext k; ring
  rw [e]
  have := h2.add hinc
  rwa [add_zero] at this

lemma gap_all (hH1 : M.H1) (hrun : M.IsRun x u θ β) :
    ∀ n s, s + n = M.T → Tendsto (fun k => (M.V s (x (k + 1) s)).toReal -
      (M.approx θ β x k s (x (k + 1) s)).toReal) atTop (𝓝 0) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    simp only [add_zero] at hs
    subst hs
    refine tendsto_const_nhds.congr (fun k => ?_)
    rw [approx_ge M θ β x k le_rfl, sub_self]
  | succ n ih =>
    intro s hs
    exact gap_step hH1 hrun (by omega) (ih (s + 1) (by omega))

theorem main (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ t < M.T,
      Tendsto (fun k => M.W t (x k t) (u k t) - M.V t (x k t)) atTop (𝓝 0) ∧
        Tendsto (fun k => M.V t (x k t) - M.approx θ β x k t (x k t)) atTop (𝓝 0) := by
  intro t ht
  obtain ⟨h1, h2, hfin⟩ := step hH1 hrun ht (gap_all hH1 hrun (M.T - (t + 1)) (t + 1) (by omega))
  have hVfin : ∀ k, M.V t (x (k + 1) t) ≠ ⊤ ∧ M.V t (x (k + 1) t) ≠ ⊥ := fun k =>
    ⟨V_ne_top' hH1 ht.le (run_mem hH1 hrun k t ht.le), V_ne_bot hH1 hrun ht.le _⟩
  constructor
  · refine (tendsto_add_atTop_iff_nat 1).1 ?_
    have h := EReal.tendsto_coe.2 h1
    rw [EReal.coe_zero] at h
    refine h.congr' ?_
    filter_upwards [hfin] with k hk
    rw [EReal.coe_sub, EReal.coe_toReal hk.1 hk.2.1, EReal.coe_toReal (hVfin k).1 (hVfin k).2]
  · refine (tendsto_add_atTop_iff_nat 1).1 ?_
    have h := EReal.tendsto_coe.2 h2
    rw [EReal.coe_zero] at h
    refine h.congr' ?_
    filter_upwards [hfin] with k hk
    rw [EReal.coe_sub, EReal.coe_toReal hk.2.2.2 hk.2.2.1,
      EReal.coe_toReal (hVfin k).1 (hVfin k).2]

end RunLemmas2

end SDDPAux

open ConvexSDDP.Det Filter Topology in
theorem solution {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ t < M.T,
      Tendsto (fun k => M.W t (x k t) (u k t) - M.V t (x k t)) atTop (𝓝 0) ∧
        Tendsto (fun k => M.V t (x k t) - M.approx θ β x k t (x k t)) atTop (𝓝 0) := by
  exact SDDPAux.main M hH1 x u θ β hrun
