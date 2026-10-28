-- Prove2me | solution 1 for DualityStability.StrongDuality.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T12:44:31.374997+00:00
-- url     : https://prove2.me/submissions/4a93e68c-7c7b-452e-a43d-89daf5a75845

import Mathlib
import Definitions.Def_DualityStability_StrongDuality_Program

set_option autoImplicit false

namespace DS3

open DualityStability.StrongDuality Filter Topology
open scoped Pointwise

/-- Convexity of the strict epigraph. -/
def SEConv {X : Type*} [AddCommGroup X] [Module ℝ X] (h : X → EReal) : Prop :=
  Convex ℝ {q : X × ℝ | h q.1 < (q.2 : EReal)}

section Generic

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

lemma ereal_mul_cancel' (ε c r0 : ℝ) (he : 0 < ε) :
    ((ε⁻¹ : ℝ) : EReal) * ((((r0 : ℝ) + ε * c : ℝ) : EReal) - (r0 : EReal)) = (c : EReal) := by
  rw [← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  field_simp
  ring

lemma le_scaled {h : X → EReal} (hc : SEConv h) {r : ℝ} (h0 : h 0 = r) (z : X) {ρ t : ℝ}
    (hρ : 0 < ρ) (hz : h (ρ • z) < ((r + ρ * t : ℝ) : EReal)) {ε : ℝ} (he : 0 < ε)
    (heρ : ε < ρ) : h (ε • z) ≤ ((r + ε * t : ℝ) : EReal) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc'
  induction c using EReal.rec with
  | bot => exact absurd hc' (not_lt_bot)
  | top => exact le_top
  | coe c =>
    have hc'' : r + ε * t < c := by exact_mod_cast hc'
    obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = ε / ρ := ⟨_, rfl⟩
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 - b := ⟨_, rfl⟩
    have hb : 0 < b := by rw [hb_def]; exact div_pos he hρ
    have ha : 0 < a := by
      have : ε / ρ < 1 := (div_lt_one hρ).2 heρ
      rw [ha_def, hb_def]; linarith
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (c - r - ε * t) / a := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; exact div_pos (by linarith) ha
    have m1 : ((0 : X), r + δ) ∈ {q : X × ℝ | h q.1 < (q.2 : EReal)} := by
      show h 0 < ((r + δ : ℝ) : EReal)
      rw [h0]; exact_mod_cast (by linarith : r < r + δ)
    have m2 : (ρ • z, r + ρ * t) ∈ {q : X × ℝ | h q.1 < (q.2 : EReal)} := hz
    have hab : a + b = 1 := by rw [ha_def]; ring
    have hm := hc m1 m2 ha.le hb.le hab
    have h1 : a * δ = c - r - ε * t := by rw [hδ]; field_simp
    have h2 : b * ρ = ε := by rw [hb_def]; field_simp
    have heq : a • ((0 : X), r + δ) + b • (ρ • z, r + ρ * t) = (ε • z, c) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, zero_add, smul_smul, h2]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination h1 + t * h2 + r * hab
    rw [heq] at hm
    exact hm.le

lemma rd_le {h : X → EReal} (hc : SEConv h) {r : ℝ} (h0 : h 0 = r) (z : X) {ρ t : ℝ}
    (hρ : 0 < ρ) (hz : h (ρ • z) < ((r + ρ * t : ℝ) : EReal)) :
    rightDerivative h r z ≤ t := by
  unfold rightDerivative
  have ev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ((ε⁻¹ : ℝ) : EReal) * (h (ε • z) - r) ≤ (t : EReal) := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with ε hε
    have k := le_scaled hc h0 z hρ hz hε.1 hε.2
    calc ((ε⁻¹ : ℝ) : EReal) * (h (ε • z) - r)
        ≤ ((ε⁻¹ : ℝ) : EReal) * (((r + ε * t : ℝ) : EReal) - r) := by
          apply mul_le_mul_of_nonneg_left (EReal.sub_le_sub k le_rfl)
          exact_mod_cast (inv_pos.2 hε.1).le
      _ = t := ereal_mul_cancel' ε t r hε.1
  calc liminf (fun ε : ℝ => ((ε⁻¹ : ℝ) : EReal) * (h (ε • z) - r)) (𝓝[>] 0)
      ≤ liminf (fun _ : ℝ => (t : EReal)) (𝓝[>] 0) := liminf_le_liminf ev
    _ = t := liminf_const _

lemma le_rd {h : X → EReal} {r : ℝ} (l : X →L[ℝ] ℝ)
    (hl : ∀ w, (((r + l w : ℝ)) : EReal) ≤ h w) (z : X) :
    ((l z : ℝ) : EReal) ≤ rightDerivative h r z := by
  unfold rightDerivative
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  calc ((l z : ℝ) : EReal) = ((ε⁻¹ : ℝ) : EReal) * (((r + ε * l z : ℝ) : EReal) - r) :=
        (ereal_mul_cancel' ε (l z) r hε).symm
    _ ≤ ((ε⁻¹ : ℝ) : EReal) * (h (ε • z) - r) := by
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast (inv_pos.2 hε).le)
        apply EReal.sub_le_sub _ le_rfl
        have := hl (ε • z)
        simpa [map_smul, smul_eq_mul] using this

end Generic

section Stab

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]

set_option maxHeartbeats 1000000 in
lemma stable_sub {h : X → EReal} (hc : SEConv h) {r : ℝ} (h0 : h 0 = r)
    (hs : ¬ UnstablySet h) : ∃ l : X →L[ℝ] ℝ, ∀ z, ((r + l z : ℝ) : EReal) ≤ h z := by
  unfold UnstablySet at hs
  push_neg at hs
  obtain ⟨U, hU, M, hM⟩ := hs r h0
  obtain ⟨V, ⟨hV0, hVo, hVc⟩, hVU⟩ := (LocallyConvexSpace.convex_open_basis_zero ℝ X).mem_iff.1 hU
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |M| + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; positivity
  have hMK : -K < -M := by rw [hKdef]; have := le_abs_self M; linarith
  let Q : Set (X × ℝ) := {p | ∃ ρ : ℝ, 0 < ρ ∧ p.1 ∈ ρ • V ∧ p.2 < -(ρ * K)}
  let S : Set (X × ℝ) := {p | h p.1 < ((r + p.2 : ℝ) : EReal)}
  have hQo : IsOpen Q := by
    have : Q = ⋃ ρ ∈ Set.Ioi (0:ℝ), (ρ • V) ×ˢ Set.Iio (-(ρ * K)) := by
      ext p
      simp only [Q, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_Iio, Set.mem_Ioi,
        exists_prop]
    rw [this]
    exact isOpen_biUnion fun ρ hρ => (hVo.smul₀ (ne_of_gt hρ)).prod isOpen_Iio
  have hQc : Convex ℝ Q := by
    intro p hp q hq a b ha hb hab
    obtain ⟨ρ1, hρ1, ⟨v1, hv1, hv1e⟩, hs1⟩ := hp
    obtain ⟨ρ2, hρ2, ⟨v2, hv2, hv2e⟩, hs2⟩ := hq
    have hmin := lt_min hρ1 hρ2
    have hR : 0 < a * ρ1 + b * ρ2 := by
      nlinarith [mul_le_mul_of_nonneg_left (min_le_left ρ1 ρ2) ha,
        mul_le_mul_of_nonneg_left (min_le_right ρ1 ρ2) hb]
    refine ⟨a * ρ1 + b * ρ2, hR, ?_, ?_⟩
    · refine ⟨(a * ρ1 / (a * ρ1 + b * ρ2)) • v1 + (b * ρ2 / (a * ρ1 + b * ρ2)) • v2,
        hVc hv1 hv2 (by positivity) (by positivity) (by field_simp), ?_⟩
      simp only [Prod.fst_add, Prod.smul_fst, ← hv1e, ← hv2e, smul_add, smul_smul]
      congr 1 <;> congr 1 <;> field_simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rcases ha.eq_or_lt with ha0 | ha0
      · subst ha0
        have hb1 : b = 1 := by linarith
        subst hb1
        simp only [zero_mul, one_mul, zero_add]
        exact hs2
      · have e1 := mul_lt_mul_of_pos_left hs1 ha0
        have e2 := mul_le_mul_of_nonneg_left hs2.le hb
        nlinarith
  have hSc : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    have hm := hc (x := (p.1, r + p.2)) hp (y := (q.1, r + q.2)) hq ha hb hab
    have e : a • (p.1, r + p.2) + b • (q.1, r + q.2)
        = ((a • p + b • q).1, r + (a • p + b • q).2) := by
      ext
      · simp
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination r * hab
    rw [e] at hm
    exact hm
  have hdisj : Disjoint Q S := by
    rw [Set.disjoint_left]
    rintro p ⟨ρ, hρ, ⟨v, hv, hve⟩, hp2⟩ hpS
    have hpS' : h (ρ • v) < ((r + ρ * (p.2 / ρ) : ℝ) : EReal) := by
      have hve' : ρ • v = p.1 := hve
      rw [hve', mul_div_cancel₀ _ hρ.ne']; exact hpS
    have h1 := rd_le hc h0 v hρ hpS'
    have h2 := hM v (hVU hv)
    have h3 : p.2 / ρ < -M := by
      have : p.2 / ρ < -K := by
        rw [div_lt_iff₀ hρ]; linarith
      linarith
    have h4 : ((-M : ℝ) : EReal) ≤ ((p.2 / ρ : ℝ) : EReal) := h2.trans h1
    have h5 : -M ≤ p.2 / ρ := by exact_mod_cast h4
    linarith
  obtain ⟨φ, u, hφQ, hφS⟩ := geometric_hahn_banach_open hQc hQo hSc hdisj
  have hS0 : ∀ s : ℝ, 0 < s → ((0:X), s) ∈ S := by
    intro s hs
    show h 0 < ((r + s : ℝ) : EReal)
    rw [h0]; exact_mod_cast (by linarith : r < r + s)
  have hQ0 : ∀ ρ : ℝ, 0 < ρ → ((0:X), -(2 * ρ * K)) ∈ Q := fun ρ hρ =>
    ⟨ρ, hρ, ⟨0, hV0, smul_zero ρ⟩, by show -(2 * ρ * K) < -(ρ * K); nlinarith⟩
  have φ0s : ∀ s : ℝ, φ ((0:X), s) = s * φ ((0:X), 1) := by
    intro s
    have : ((0:X), s) = s • ((0:X), (1:ℝ)) := by ext <;> simp
    rw [this, map_smul, smul_eq_mul]
  have hu1 : ∀ s : ℝ, 0 < s → u ≤ s * φ ((0:X), 1) := fun s hs => (φ0s s) ▸ hφS _ (hS0 s hs)
  have hu2 : ∀ ρ : ℝ, 0 < ρ → -(2 * ρ * K) * φ ((0:X), 1) < u := fun ρ hρ => by
    rw [← φ0s]; exact hφQ _ (hQ0 ρ hρ)
  have hα : 0 < φ ((0:X), 1) := by
    by_contra hneg
    push_neg at hneg
    have a1 := hu1 1 one_pos
    have a2 := hu2 1 one_pos
    nlinarith
  have hu0 : 0 ≤ u := by
    by_contra hneg
    push_neg at hneg
    have hρ : 0 < -u / (4 * K * φ ((0:X), 1)) := div_pos (neg_pos.2 hneg) (by positivity)
    have a2 := hu2 _ hρ
    have e : -(2 * (-u / (4 * K * φ ((0:X), 1))) * K) * φ ((0:X), 1) = u / 2 := by
      field_simp; ring
    rw [e] at a2
    linarith
  let l : X →L[ℝ] ℝ := (-(φ ((0:X), 1))⁻¹) • (φ.comp (ContinuousLinearMap.inl ℝ X ℝ))
  refine ⟨l, fun z => ?_⟩
  have hl : l z = -((φ ((0:X), 1))⁻¹ * φ (z, 0)) := by
    simp [l]
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hzS : (z, s - r) ∈ S := by
    show h z < ((r + (s - r) : ℝ) : EReal)
    simpa using hs1
  have a3 := hφS _ hzS
  have e : φ (z, s - r) = φ (z, 0) + (s - r) * φ ((0:X), 1) := by
    rw [← φ0s, ← map_add]; congr 1; ext <;> simp
  have hs2' : s < r + l z := by exact_mod_cast hs2
  rw [hl] at hs2'
  have k1 : (s - r) * φ ((0:X), 1) < -((φ ((0:X), 1))⁻¹ * φ (z, 0)) * φ ((0:X), 1) :=
    mul_lt_mul_of_pos_right (by linarith) hα
  have k2 : -((φ ((0:X), 1))⁻¹ * φ (z, 0)) * φ ((0:X), 1) = -φ (z, 0) := by
    field_simp
  linarith

lemma sub_stable {h : X → EReal} {r : ℝ} (h0 : h 0 = r) (l : X →L[ℝ] ℝ)
    (hl : ∀ w, ((r + l w : ℝ) : EReal) ≤ h w) : StablySet h := by
  refine ⟨by rw [h0]; exact EReal.coe_lt_top r, ?_⟩
  rintro ⟨r', h0', hU⟩
  have hr : r' = r := by rw [h0] at h0'; exact_mod_cast h0'.symm
  subst hr
  have hUn : (l ⁻¹' Set.Ioo (-1) 1) ∈ 𝓝 (0:X) :=
    l.continuous.continuousAt.preimage_mem_nhds (by simpa using Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))
  obtain ⟨z, hz, hlt⟩ := hU _ hUn 1
  have k := le_rd l hl z
  have k2 : ((l z : ℝ) : EReal) < ((-1 : ℝ) : EReal) := k.trans_lt hlt
  have k3 : l z < -1 := by exact_mod_cast k2
  exact absurd hz.1 (by simp only [not_lt]; linarith)

end Stab

section Aux

lemma aux_weak (G Fs a b : EReal) (c d : ℝ) (ha : a ≠ ⊥) (hb : b ≠ ⊤)
    (hG : G ≤ ((c - d : ℝ) : EReal) - b) (hF : (c : EReal) - a ≤ Fs) :
    G - Fs + d ≤ a - b := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top => rw [EReal.top_sub hb]; exact le_top
  | coe a =>
    induction b using EReal.rec with
    | bot => rw [EReal.coe_sub_bot]; exact le_top
    | top => exact absurd rfl hb
    | coe b =>
      have e : (((c - d : ℝ) : EReal) - (b : EReal)) - ((c : EReal) - (a : EReal)) + (d : EReal)
          = ((a - b : ℝ) : EReal) := by norm_cast; ring
      calc G - Fs + d ≤ (((c - d : ℝ) : EReal) - (b : EReal)) - ((c : EReal) - (a : EReal)) + d :=
            add_le_add (EReal.sub_le_sub hG hF) le_rfl
        _ = ((a - b : ℝ) : EReal) := e
        _ = (a : EReal) - (b : EReal) := by norm_cast

lemma aux_dsub (a b : EReal) (r c e : ℝ) (ha : a ≠ ⊥) (hb : b ≠ ⊤)
    (h : ((r + (c - e) : ℝ) : EReal) ≤ a - b) : (c : EReal) - a ≤ ((e : EReal) - b) - r := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top => simp
  | coe a =>
    induction b using EReal.rec with
    | bot => simp
    | top => exact absurd rfl hb
    | coe b =>
      have h' : r + (c - e) ≤ a - b := by exact_mod_cast h
      have : c - a ≤ e - b - r := by linarith
      exact_mod_cast this

lemma aux_split (a b : EReal) (ha : a ≠ ⊥) (hb : b ≠ ⊤) (s : ℝ) (h : a - b < s) :
    ∃ α β : ℝ, a = α ∧ -b = β ∧ α + β < s := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top => rw [EReal.top_sub hb] at h; exact absurd h (not_lt.2 le_top)
  | coe a =>
    induction b using EReal.rec with
    | bot => rw [EReal.coe_sub_bot] at h; exact absurd h (not_lt.2 le_top)
    | top => exact absurd rfl hb
    | coe b =>
      refine ⟨a, -b, rfl, by simp, ?_⟩
      have : a - b < s := by exact_mod_cast h
      linarith

lemma aux_sub_ne_top (G Fs : EReal) (hG : G ≠ ⊤) (hF : Fs ≠ ⊥) : G - Fs ≠ ⊤ := by
  induction G using EReal.rec with
  | bot => simp
  | top => exact absurd rfl hG
  | coe g =>
    induction Fs using EReal.rec with
    | bot => exact absurd rfl hF
    | top => simp
    | coe f => exact_mod_cast EReal.coe_ne_top (g - f)

end Aux

section FM

variable {X X' : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [TopologicalSpace X'] [AddCommGroup X'] [Module ℝ X']
  [IsTopologicalAddGroup X'] [ContinuousSMul ℝ X'] [LocallyConvexSpace ℝ X'] [T2Space X']

/-- Convex conjugate with respect to a pairing. -/
noncomputable def conj (π : TopPairing X X') (k : X → EReal) (x' : X') : EReal :=
  ⨆ w, ((π.pair w x' : ℝ) : EReal) - k w

lemma phi_split (φ : StrongDual ℝ (X × ℝ)) (w : X) (s : ℝ) :
    φ (w, s) = φ (w, 0) + s * φ ((0 : X), 1) := by
  have : (w, s) = (w, (0:ℝ)) + s • ((0:X), (1:ℝ)) := by ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, smul_eq_mul]

lemma fm_sep (k : X → EReal) (hconv : EpiConvex k) (hlsc : LowerSemicontinuous k) (x : X) (t : ℝ)
    (ht : (t : EReal) < k x) :
    ∃ (φ : StrongDual ℝ (X × ℝ)) (u : ℝ), φ (x, t) < u ∧ ∀ w (s : ℝ), k w ≤ s → u < φ (w, s) := by
  have hcl : IsClosed {q : X × ℝ | k q.1 ≤ (q.2 : EReal)} :=
    hlsc.isClosed_epigraph.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  obtain ⟨φ, u, h1, h2⟩ := geometric_hahn_banach_point_closed (x := (x, t)) hconv hcl
    (by simp only [Set.mem_setOf_eq, not_le]; exact ht)
  exact ⟨φ, u, h1, fun w s hs => h2 (w, s) hs⟩

lemma fm_nonneg (k : X → EReal) (φ : StrongDual ℝ (X × ℝ)) (u : ℝ)
    (hsep : ∀ w (s : ℝ), k w ≤ s → u < φ (w, s)) (x0 : X) (v : ℝ) (hv : k x0 = v) :
    0 ≤ φ ((0:X), 1) := by
  by_contra hneg
  push_neg at hneg
  have hs : 0 ≤ (|φ (x0, v)| + |u| + 1) / (-φ ((0:X), 1)) :=
    div_nonneg (by positivity) (by linarith)
  have h1 := hsep x0 (v + (|φ (x0, v)| + |u| + 1) / (-φ ((0:X), 1)))
    (by rw [hv]; exact_mod_cast (by linarith : v ≤ v + (|φ (x0, v)| + |u| + 1) / (-φ ((0:X), 1))))
  rw [phi_split] at h1
  have h2 := phi_split φ x0 v
  have e : (v + (|φ (x0, v)| + |u| + 1) / (-φ ((0:X), 1))) * φ ((0:X), 1)
      = v * φ ((0:X), 1) - (|φ (x0, v)| + |u| + 1) := by
    have hne : φ ((0:X), 1) ≠ 0 := hneg.ne
    rw [add_mul, div_neg, neg_mul, div_mul_cancel₀ _ hne]; ring
  rw [e] at h1
  have := le_abs_self (φ (x0, v))
  have := neg_abs_le u
  linarith

lemma fm_pos (π : TopPairing X X') (k : X → EReal) (hnb : ∀ x, k x ≠ ⊥)
    (φ : StrongDual ℝ (X × ℝ)) (u : ℝ)
    (hsep : ∀ w (s : ℝ), k w ≤ s → u < φ (w, s)) (ha : 0 < φ ((0:X), 1)) :
    ∃ y : X', conj π k y ≤ ((-u / φ ((0:X), 1) : ℝ) : EReal) ∧
      ∀ w, π.pair w y = -((φ ((0:X), 1))⁻¹ * φ (w, 0)) := by
  let l : X →L[ℝ] ℝ := (-(φ ((0:X), 1))⁻¹) • (φ.comp (ContinuousLinearMap.inl ℝ X ℝ))
  obtain ⟨y, hy, -⟩ := π.represents_left l
  have hl : ∀ w, l w = -((φ ((0:X), 1))⁻¹ * φ (w, 0)) := fun w => by simp [l]
  have hpair : ∀ w, π.pair w y = -((φ ((0:X), 1))⁻¹ * φ (w, 0)) := fun w => by
    rw [← hy w, hl w]
  refine ⟨y, iSup_le fun w => ?_, hpair⟩
  induction hkw : k w using EReal.rec with
  | bot => exact absurd hkw (hnb w)
  | top => simp
  | coe v =>
    have h1 := hsep w v (le_of_eq hkw)
    rw [phi_split] at h1
    rw [hpair w]
    have key : -((φ ((0:X), 1))⁻¹ * φ (w, 0)) - v ≤ -u / φ ((0:X), 1) := by
      rw [← sub_nonneg]
      have e : -u / φ ((0:X), 1) - (-((φ ((0:X), 1))⁻¹ * φ (w, 0)) - v)
          = (φ (w, 0) + v * φ ((0:X), 1) - u) / φ ((0:X), 1) := by
        field_simp; ring
      rw [e]
      exact div_nonneg (by linarith) ha.le
    exact_mod_cast key

set_option maxHeartbeats 1000000 in
theorem fm (π : TopPairing X X') (k : X → EReal) (hconv : EpiConvex k)
    (hlsc : LowerSemicontinuous k) (hnb : ∀ x, k x ≠ ⊥) (hfin : ∃ x, k x ≠ ⊤)
    (x : X) (t : ℝ) (ht : (t : EReal) < k x) :
    ∃ y : X', (t : EReal) < ((π.pair x y : ℝ) : EReal) - conj π k y := by
  obtain ⟨φ, u, h1, h2⟩ := fm_sep k hconv hlsc x t ht
  obtain ⟨x0, hx0⟩ := hfin
  obtain ⟨v, hv⟩ : ∃ v : ℝ, k x0 = v := by
    induction hk : k x0 using EReal.rec with
    | bot => exact absurd hk (hnb x0)
    | top => exact absurd hk hx0
    | coe v => exact ⟨v, rfl⟩
  have ha := fm_nonneg k φ u h2 x0 v hv
  rcases ha.eq_or_lt with ha0 | ha0
  · obtain ⟨φ0, u0, h01, h02⟩ := fm_sep k hconv hlsc x0 (v - 1)
      (by rw [hv]; exact_mod_cast (by linarith : v - 1 < v))
    have ha0' := fm_nonneg k φ0 u0 h02 x0 v hv
    have hpos0 : 0 < φ0 ((0:X), 1) := by
      rcases ha0'.eq_or_lt with h | h
      · exfalso
        have e1 := h02 x0 v (le_of_eq hv)
        rw [phi_split, ← h, mul_zero, add_zero] at e1 h01
        linarith
      · exact h
    obtain ⟨y0, hc0, -⟩ := fm_pos π k hnb φ0 u0 h02 hpos0
    obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = -u0 / φ0 ((0:X), 1) := ⟨_, rfl⟩
    rw [← hc0def] at hc0
    let l1 : X →L[ℝ] ℝ := -(φ.comp (ContinuousLinearMap.inl ℝ X ℝ))
    obtain ⟨y1, hy1, -⟩ := π.represents_left l1
    have hy1' : ∀ w, π.pair w y1 = -φ (w, 0) := fun w => by rw [← hy1 w]; simp [l1]
    have hlx : φ (x, 0) < u := by
      have := h1; rwa [phi_split, ← ha0, mul_zero, add_zero] at this
    have hlw : ∀ w (s : ℝ), k w ≤ s → u < φ (w, 0) := fun w s hs => by
      have := h2 w s hs; rwa [phi_split, ← ha0, mul_zero, add_zero] at this
    obtain ⟨lam, hlam⟩ : ∃ lam : ℝ,
        lam = (|t| + |π.pair x y0 - c0| + 1) / (u - φ (x, 0)) := ⟨_, rfl⟩
    have hD : 0 < u - φ (x, 0) := by linarith
    have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
    have hlamD : lam * (u - φ (x, 0)) = |t| + |π.pair x y0 - c0| + 1 := by
      rw [hlam]; field_simp
    refine ⟨y0 + lam • y1, ?_⟩
    have hconj : conj π k (y0 + lam • y1) ≤ ((c0 - lam * u : ℝ) : EReal) := iSup_le fun w => by
      induction hkw : k w using EReal.rec with
      | bot => exact absurd hkw (hnb w)
      | top => simp
      | coe v' =>
        have e1 : ((π.pair w y0 : ℝ) : EReal) - k w ≤ conj π k y0 :=
          le_iSup (fun w => ((π.pair w y0 : ℝ) : EReal) - k w) w
        rw [hkw] at e1
        have e1' : π.pair w y0 - v' ≤ c0 := by exact_mod_cast e1.trans hc0
        have e2 := hlw w v' (le_of_eq hkw)
        have e3 := mul_le_mul_of_nonneg_left e2.le hlam0
        have hp : π.pair w (y0 + lam • y1) = π.pair w y0 + lam * (-φ (w, 0)) := by
          rw [map_add, map_smul, smul_eq_mul, hy1']
        rw [hp]
        have : π.pair w y0 + lam * (-φ (w, 0)) - v' ≤ c0 - lam * u := by nlinarith
        exact_mod_cast this
    have hp : π.pair x (y0 + lam • y1) = π.pair x y0 + lam * (-φ (x, 0)) := by
      rw [map_add, map_smul, smul_eq_mul, hy1']
    calc (t : EReal) < ((π.pair x (y0 + lam • y1) - (c0 - lam * u) : ℝ) : EReal) := by
          rw [hp]
          have := le_abs_self t
          have := neg_abs_le (π.pair x y0 - c0)
          have : t < π.pair x y0 + lam * -φ (x, 0) - (c0 - lam * u) := by nlinarith
          exact_mod_cast this
      _ ≤ ((π.pair x (y0 + lam • y1) : ℝ) : EReal) - conj π k (y0 + lam • y1) := by
          rw [EReal.coe_sub]; exact EReal.sub_le_sub le_rfl hconj
  · obtain ⟨y, hc, hpair⟩ := fm_pos π k hnb φ u h2 ha0
    refine ⟨y, ?_⟩
    have h1' := h1
    rw [phi_split] at h1'
    calc (t : EReal) < ((π.pair x y - (-u / φ ((0:X), 1)) : ℝ) : EReal) := by
          rw [hpair x]
          have key : 0 < -((φ ((0:X), 1))⁻¹ * φ (x, 0)) - (-u / φ ((0:X), 1)) - t := by
            have e : -((φ ((0:X), 1))⁻¹ * φ (x, 0)) - (-u / φ ((0:X), 1)) - t
                = (u - (φ (x, 0) + t * φ ((0:X), 1))) / φ ((0:X), 1) := by
              field_simp; ring
            rw [e]; exact div_pos (by linarith) ha0
          exact_mod_cast (by linarith : t < -((φ ((0:X), 1))⁻¹ * φ (x, 0)) - (-u / φ ((0:X), 1)))
      _ ≤ ((π.pair x y : ℝ) : EReal) - conj π k y := by
          rw [EReal.coe_sub]; exact EReal.sub_le_sub le_rfl hc

end FM

section Prog

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

variable (p : Program E E' F F')

lemma weak (z : F) (x : E) (y' : F') :
    p.dualAt y' + (p.fPair.pair z y' : EReal) ≤ p.primalAt z x := by
  have hf : ((p.ePair.pair x (p.Astar y') : ℝ) : EReal) - p.f x ≤ p.fstar (p.Astar y') :=
    le_iSup (fun x => ((p.ePair.pair x (p.Astar y') : ℝ) : EReal) - p.f x) x
  have hg : p.gstar y' ≤ ((p.fPair.pair (p.A x - z) y' : ℝ) : EReal) - p.g (p.A x - z) :=
    iInf_le (fun y => ((p.fPair.pair y y' : ℝ) : EReal) - p.g y) (p.A x - z)
  have hpair : p.fPair.pair (p.A x - z) y' = p.ePair.pair x (p.Astar y') - p.fPair.pair z y' := by
    rw [map_sub, LinearMap.sub_apply, p.adjoint]
  rw [hpair] at hg
  exact aux_weak _ _ _ _ _ _ (p.f_no_neg_inf x) (p.g_no_pos_inf _) hg hf

lemma dual_le_h0 (y' : F') : p.dualAt y' ≤ p.h 0 := by
  refine le_iInf fun x => ?_
  have := weak p 0 x y'
  simpa using this

lemma sub_of_dual (y' : F') (r : ℝ) (hd : p.dualAt y' = r) :
    ∀ z, ((r + p.fPair.pair z y' : ℝ) : EReal) ≤ p.h z := by
  intro z
  refine le_iInf fun x => ?_
  have := weak p z x y'
  rw [hd] at this
  exact_mod_cast this

lemma fstar_ne_bot (x' : E') : p.fstar x' ≠ ⊥ := by
  obtain ⟨x0, hx0⟩ := p.f_some_finite
  have hle : ((p.ePair.pair x0 x' : ℝ) : EReal) - p.f x0 ≤ p.fstar x' :=
    le_iSup (fun x => ((p.ePair.pair x x' : ℝ) : EReal) - p.f x) x0
  intro hb
  rw [hb, le_bot_iff] at hle
  have h1 := p.f_no_neg_inf x0
  induction hfx : p.f x0 using EReal.rec with
  | bot => exact h1 hfx
  | top => exact hx0 hfx
  | coe v =>
    rw [hfx] at hle
    exact EReal.coe_ne_bot _ (by exact_mod_cast hle)

lemma gstar_ne_top (y' : F') : p.gstar y' ≠ ⊤ := by
  obtain ⟨y0, hy0⟩ := p.g_some_finite
  have hle : p.gstar y' ≤ ((p.fPair.pair y0 y' : ℝ) : EReal) - p.g y0 :=
    iInf_le (fun y => ((p.fPair.pair y y' : ℝ) : EReal) - p.g y) y0
  intro ht
  rw [ht, top_le_iff] at hle
  have h1 := p.g_no_pos_inf y0
  induction hgy : p.g y0 using EReal.rec with
  | bot => exact hy0 hgy
  | top => exact h1 hgy
  | coe v =>
    rw [hgy] at hle
    exact EReal.coe_ne_top _ (by exact_mod_cast hle)

lemma dual_ne_top (y' : F') : p.dualAt y' ≠ ⊤ :=
  aux_sub_ne_top _ _ (gstar_ne_top p y') (fstar_ne_bot p _)

lemma dual_of_sub (y' : F') (r : ℝ) (hsub : ∀ z, ((r + p.fPair.pair z y' : ℝ) : EReal) ≤ p.h z) :
    (r : EReal) ≤ p.dualAt y' := by
  have key : ∀ x w, ((p.ePair.pair x (p.Astar y') : ℝ) : EReal) - p.f x
      ≤ (((p.fPair.pair w y' : ℝ) : EReal) - p.g w) - r := by
    intro x w
    have h1 := hsub (p.A x - w)
    have h2 : p.h (p.A x - w) ≤ p.primalAt (p.A x - w) x := iInf_le _ x
    have h3 : p.primalAt (p.A x - w) x = p.f x - p.g w := by
      simp [Program.primalAt]
    rw [h3] at h2
    have hpair : p.fPair.pair (p.A x - w) y'
        = p.ePair.pair x (p.Astar y') - p.fPair.pair w y' := by
      rw [map_sub, LinearMap.sub_apply, p.adjoint]
    rw [hpair] at h1
    exact aux_dsub _ _ _ _ _ (p.f_no_neg_inf x) (p.g_no_pos_inf w) (h1.trans h2)
  have hFs : p.fstar (p.Astar y') + r ≤ p.gstar y' := by
    refine le_iInf fun w => ?_
    rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot r)) (Or.inl (EReal.coe_ne_top r))]
    exact iSup_le fun x => key x w
  unfold Program.dualAt
  rw [EReal.le_sub_iff_add_le (Or.inl (fstar_ne_bot p _)) (Or.inr (gstar_ne_top p y')), add_comm]
  exact hFs

set_option maxHeartbeats 1000000 in
lemma h_conv : SEConv p.h := by
  intro q1 hq1 q2 hq2 t s ht hs hts
  simp only [Set.mem_setOf_eq] at hq1 hq2 ⊢
  obtain ⟨x1, hx1⟩ := iInf_lt_iff.1 hq1
  obtain ⟨x2, hx2⟩ := iInf_lt_iff.1 hq2
  obtain ⟨α1, β1, hα1, hβ1, hs1⟩ := aux_split _ _ (p.f_no_neg_inf x1) (p.g_no_pos_inf _) _ hx1
  obtain ⟨α2, β2, hα2, hβ2, hs2⟩ := aux_split _ _ (p.f_no_neg_inf x2) (p.g_no_pos_inf _) _ hx2
  have hf := p.f_convex (x := (x1, α1)) (by show p.f x1 ≤ _; rw [hα1])
    (y := (x2, α2)) (by show p.f x2 ≤ _; rw [hα2]) ht hs hts
  have hg := p.g_concave (x := (p.A x1 - q1.1, β1)) (by show -p.g _ ≤ _; rw [hβ1])
    (y := (p.A x2 - q2.1, β2)) (by show -p.g _ ≤ _; rw [hβ2]) ht hs hts
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at hf hg
  have hlin : t • (p.A x1 - q1.1) + s • (p.A x2 - q2.1)
      = p.A (t • x1 + s • x2) - (t • q1 + s • q2).1 := by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, smul_sub]
    abel
  rw [hlin] at hg
  have hlt : t * α1 + s * α2 + (t * β1 + s * β2) < (t • q1 + s • q2).2 := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rcases ht.eq_or_lt with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      linarith
    · nlinarith [mul_le_mul_of_nonneg_left hs2.le hs]
  calc p.h (t • q1 + s • q2).1 ≤ p.primalAt (t • q1 + s • q2).1 (t • x1 + s • x2) := iInf_le _ _
    _ = p.f (t • x1 + s • x2) + -p.g (p.A (t • x1 + s • x2) - (t • q1 + s • q2).1) := rfl
    _ ≤ ((t * α1 + s * α2 : ℝ) : EReal) + ((t * β1 + s * β2 : ℝ) : EReal) := add_le_add hf hg
    _ < (((t • q1 + s • q2).2 : ℝ) : EReal) := by exact_mod_cast hlt

set_option maxHeartbeats 1000000 in
theorem part1 : StablySet p.h ↔ IsGreatest (Set.range p.dualAt) (p.h 0) := by
  have hub : ∀ y', p.dualAt y' ≤ p.h 0 := dual_le_h0 p
  have hcases : p.h 0 = ⊥ ∨ p.h 0 = ⊤ ∨ ∃ r : ℝ, p.h 0 = r := by
    induction p.h 0 using EReal.rec <;> simp
  rcases hcases with hbot | htop | ⟨r, hr⟩
  · constructor
    · intro _
      rw [hbot]
      refine ⟨⟨0, le_bot_iff.1 (hbot ▸ hub 0)⟩, ?_⟩
      rintro _ ⟨y', rfl⟩
      exact hbot ▸ hub y'
    · intro _
      refine ⟨by rw [hbot]; exact bot_lt_top, ?_⟩
      rintro ⟨r, hr, -⟩
      rw [hbot] at hr
      exact EReal.bot_ne_coe r hr
  · constructor
    · rintro ⟨hlt, -⟩
      rw [htop] at hlt
      exact absurd hlt (lt_irrefl _)
    · rintro ⟨⟨y', hy'⟩, -⟩
      rw [htop] at hy'
      exact (dual_ne_top p y' hy').elim
  · constructor
    · intro hs
      obtain ⟨l, hl⟩ := stable_sub (h_conv p) hr hs.2
      obtain ⟨y', hy', -⟩ := p.fPair.represents_left l
      have hsub : ∀ z, ((r + p.fPair.pair z y' : ℝ) : EReal) ≤ p.h z := fun z => by
        rw [← hy' z]; exact hl z
      have h1 := dual_of_sub p y' r hsub
      have h2 : p.dualAt y' = p.h 0 := le_antisymm (hub y') (hr ▸ h1)
      refine ⟨⟨y', h2⟩, ?_⟩
      rintro _ ⟨y'', rfl⟩
      exact hub y''
    · rintro ⟨⟨y', hy'⟩, -⟩
      rw [hr] at hy'
      have hsub := sub_of_dual p y' r hy'
      let l : F →L[ℝ] ℝ := ⟨p.fPair.pair.flip y', p.fPair.continuous_left y'⟩
      exact sub_stable hr l (fun z => hsub z)

lemma aux_btwn (a b : EReal) (ha : a ≠ ⊥) (hb : b ≠ ⊥) (c : ℝ) (h : (c : EReal) < a + b) :
    ∃ α β : ℝ, (α : EReal) < a ∧ (β : EReal) < b ∧ c < α + β := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top =>
    induction b using EReal.rec with
    | bot => exact absurd rfl hb
    | top => exact ⟨c + 1, 0, EReal.coe_lt_top _, EReal.coe_lt_top _, by linarith⟩
    | coe b => exact ⟨c - b + 2, b - 1, EReal.coe_lt_top _,
        by exact_mod_cast (by linarith : b - 1 < b), by linarith⟩
  | coe a =>
    induction b using EReal.rec with
    | bot => exact absurd rfl hb
    | top => exact ⟨a - 1, c - a + 2, by exact_mod_cast (by linarith : a - 1 < a),
        EReal.coe_lt_top _, by linarith⟩
    | coe b =>
      have h' : c < a + b := by exact_mod_cast h
      refine ⟨a - (a + b - c) / 3, b - (a + b - c) / 3, ?_, ?_, by linarith⟩
      · exact_mod_cast (by linarith : a - (a + b - c) / 3 < a)
      · exact_mod_cast (by linarith : b - (a + b - c) / 3 < b)

lemma fstar_comb (x1' x2' : E') (β1 β2 : ℝ) (h1 : p.fstar x1' ≤ β1) (h2 : p.fstar x2' ≤ β2)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    p.fstar (t • x1' + s • x2') ≤ ((t * β1 + s * β2 : ℝ) : EReal) := by
  refine iSup_le fun x => ?_
  have e1 : ((p.ePair.pair x x1' : ℝ) : EReal) - p.f x ≤ p.fstar x1' :=
    le_iSup (fun x => ((p.ePair.pair x x1' : ℝ) : EReal) - p.f x) x
  have e2 : ((p.ePair.pair x x2' : ℝ) : EReal) - p.f x ≤ p.fstar x2' :=
    le_iSup (fun x => ((p.ePair.pair x x2' : ℝ) : EReal) - p.f x) x
  have e1' := e1.trans h1
  have e2' := e2.trans h2
  have hnb := p.f_no_neg_inf x
  induction hfx : p.f x using EReal.rec with
  | bot => exact absurd hfx hnb
  | top => simp
  | coe φ =>
    rw [hfx] at e1' e2'
    have k1 : p.ePair.pair x x1' - φ ≤ β1 := by exact_mod_cast e1'
    have k2 : p.ePair.pair x x2' - φ ≤ β2 := by exact_mod_cast e2'
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have : t * p.ePair.pair x x1' + s * p.ePair.pair x x2' - φ ≤ t * β1 + s * β2 := by
      calc t * p.ePair.pair x x1' + s * p.ePair.pair x x2' - φ
          = t * (p.ePair.pair x x1' - φ) + s * (p.ePair.pair x x2' - φ) := by
            linear_combination φ * hts
        _ ≤ t * β1 + s * β2 :=
            add_le_add (mul_le_mul_of_nonneg_left k1 ht) (mul_le_mul_of_nonneg_left k2 hs)
    exact_mod_cast this

lemma gstar_comb (y1 y2 : F') (α1 α2 : ℝ) (h1 : ((-α1 : ℝ) : EReal) ≤ p.gstar y1)
    (h2 : ((-α2 : ℝ) : EReal) ≤ p.gstar y2)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    ((-(t * α1 + s * α2) : ℝ) : EReal) ≤ p.gstar (t • y1 + s • y2) := by
  refine le_iInf fun y => ?_
  have e1 : p.gstar y1 ≤ ((p.fPair.pair y y1 : ℝ) : EReal) - p.g y :=
    iInf_le (fun y => ((p.fPair.pair y y1 : ℝ) : EReal) - p.g y) y
  have e2 : p.gstar y2 ≤ ((p.fPair.pair y y2 : ℝ) : EReal) - p.g y :=
    iInf_le (fun y => ((p.fPair.pair y y2 : ℝ) : EReal) - p.g y) y
  have e1' := h1.trans e1
  have e2' := h2.trans e2
  have hnt := p.g_no_pos_inf y
  induction hgy : p.g y using EReal.rec with
  | bot => rw [EReal.coe_sub_bot]; exact le_top
  | top => exact absurd hgy hnt
  | coe γ =>
    rw [hgy] at e1' e2'
    have k1 : -α1 ≤ p.fPair.pair y y1 - γ := by exact_mod_cast e1'
    have k2 : -α2 ≤ p.fPair.pair y y2 - γ := by exact_mod_cast e2'
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have : -(t * α1 + s * α2) ≤ t * p.fPair.pair y y1 + s * p.fPair.pair y y2 - γ := by
      calc -(t * α1 + s * α2) = t * (-α1) + s * (-α2) := by ring
        _ ≤ t * (p.fPair.pair y y1 - γ) + s * (p.fPair.pair y y2 - γ) :=
            add_le_add (mul_le_mul_of_nonneg_left k1 ht) (mul_le_mul_of_nonneg_left k2 hs)
        _ = t * p.fPair.pair y y1 + s * p.fPair.pair y y2 - γ := by
            linear_combination (-γ) * hts
    exact_mod_cast this

set_option maxHeartbeats 1000000 in
lemma dualH_conv : SEConv p.dualH := by
  intro q1 hq1 q2 hq2 t s ht hs hts
  simp only [Set.mem_setOf_eq] at hq1 hq2 ⊢
  obtain ⟨y1, hy1⟩ := iInf_lt_iff.1 hq1
  obtain ⟨y2, hy2⟩ := iInf_lt_iff.1 hq2
  have nb : ∀ y', -p.gstar y' ≠ ⊥ := fun y' => by
    rw [Ne, EReal.neg_eq_bot_iff]; exact gstar_ne_top p y'
  have nt : ∀ x', -p.fstar x' ≠ ⊤ := fun x' => by
    rw [Ne, EReal.neg_eq_top_iff]; exact fstar_ne_bot p x'
  obtain ⟨α1, β1, hα1, hβ1, hs1⟩ := aux_split _ _ (nb y1) (nt _) _ hy1
  obtain ⟨α2, β2, hα2, hβ2, hs2⟩ := aux_split _ _ (nb y2) (nt _) _ hy2
  rw [neg_neg] at hβ1 hβ2
  have hg1 : ((-α1 : ℝ) : EReal) ≤ p.gstar y1 := by
    rw [EReal.coe_neg, ← hα1, neg_neg]
  have hg2 : ((-α2 : ℝ) : EReal) ≤ p.gstar y2 := by
    rw [EReal.coe_neg, ← hα2, neg_neg]
  have hg := gstar_comb p y1 y2 α1 α2 hg1 hg2 t s ht hs hts
  have hf := fstar_comb p _ _ β1 β2 hβ1.le hβ2.le t s ht hs hts
  have hlin : t • (p.Astar y1 - q1.1) + s • (p.Astar y2 - q2.1)
      = p.Astar (t • y1 + s • y2) - (t • q1 + s • q2).1 := by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, smul_sub]
    abel
  rw [hlin] at hf
  have hg' : -p.gstar (t • y1 + s • y2) ≤ ((t * α1 + s * α2 : ℝ) : EReal) := by
    rw [EReal.neg_le, ← EReal.coe_neg]; exact hg
  have hlt : t * α1 + s * α2 + (t * β1 + s * β2) < (t • q1 + s • q2).2 := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rcases ht.eq_or_lt with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      linarith
    · nlinarith [mul_le_mul_of_nonneg_left hs2.le hs]
  calc p.dualH (t • q1 + s • q2).1
      ≤ -p.gstar (t • y1 + s • y2) - -p.fstar (p.Astar (t • y1 + s • y2) - (t • q1 + s • q2).1) :=
        iInf_le (fun y' => -p.gstar y' - -p.fstar (p.Astar y' - (t • q1 + s • q2).1)) _
    _ = -p.gstar (t • y1 + s • y2) + p.fstar (p.Astar (t • y1 + s • y2) - (t • q1 + s • q2).1) := by
        rw [sub_eq_add_neg, neg_neg]
    _ ≤ ((t * α1 + s * α2 : ℝ) : EReal) + ((t * β1 + s * β2 : ℝ) : EReal) := add_le_add hg' hf
    _ < (((t • q1 + s • q2).2 : ℝ) : EReal) := by exact_mod_cast hlt

lemma dualH0 : p.dualH 0 = -p.dualValue := by
  have term : ∀ y', -p.gstar y' - -p.fstar (p.Astar y' - 0) = -p.dualAt y' := by
    intro y'
    rw [sub_zero]
    unfold Program.dualAt
    rw [EReal.neg_sub (Or.inr (fstar_ne_bot p _)) (Or.inl (gstar_ne_top p y')), sub_eq_add_neg,
      neg_neg]
  have hH : p.dualH 0 = ⨅ y', -p.dualAt y' := by
    unfold Program.dualH
    exact iInf_congr term
  rw [hH]
  unfold Program.dualValue
  apply le_antisymm
  · rw [EReal.le_neg]
    exact iSup_le fun y => by rw [EReal.le_neg]; exact iInf_le (fun y' => -p.dualAt y') y
  · exact le_iInf fun y => EReal.neg_le_neg_iff.2 (le_iSup p.dualAt y)

lemma primal_ne_bot (x : E) : p.primalAt 0 x ≠ ⊥ := by
  unfold Program.primalAt
  rw [sub_eq_add_neg, Ne, ← Ne, EReal.add_ne_bot_iff]
  exact ⟨p.f_no_neg_inf x, by rw [Ne, EReal.neg_eq_bot_iff]; exact p.g_no_pos_inf _⟩

lemma weak2 (x : E) : p.dualValue ≤ p.primalAt 0 x :=
  iSup_le fun y' => by have := weak p 0 x y'; simpa using this

set_option maxHeartbeats 1000000 in
lemma attained_of_sub (r : ℝ) (xt : E)
    (hsub : ∀ z', ((r + p.ePair.pair xt z' : ℝ) : EReal) ≤ p.dualH z') :
    p.primalAt 0 (-xt) ≤ ((-r : ℝ) : EReal) := by
  by_contra hlt
  push_neg at hlt
  have hP : p.primalAt 0 (-xt) = p.f (-xt) + -p.g (p.A (-xt) - 0) := by
    unfold Program.primalAt; rw [sub_eq_add_neg]
  rw [hP] at hlt
  obtain ⟨α, β, hα, hβ, hαβ⟩ := aux_btwn _ _ (p.f_no_neg_inf _)
    (by rw [Ne, EReal.neg_eq_bot_iff]; exact p.g_no_pos_inf _) _ hlt
  obtain ⟨x', hx'⟩ := fm p.ePair p.f p.f_convex p.f_lsc p.f_no_neg_inf p.f_some_finite _ α hα
  obtain ⟨y0, hy0⟩ := fm p.fPair (fun y => -p.g y) p.g_concave p.g_usc
    (fun y => by rw [Ne, EReal.neg_eq_bot_iff]; exact p.g_no_pos_inf y)
    (by obtain ⟨y, hy⟩ := p.g_some_finite; exact ⟨y, by rw [Ne, EReal.neg_eq_top_iff]; exact hy⟩)
    _ β hβ
  have hfs : conj p.ePair p.f x' = p.fstar x' := rfl
  rw [hfs] at hx'
  -- fstar x' is real
  obtain ⟨F1, hF1⟩ : ∃ F1 : ℝ, p.fstar x' = F1 := by
    have h1 := fstar_ne_bot p x'
    induction hk : p.fstar x' using EReal.rec with
    | bot => exact absurd hk h1
    | top => rw [hk] at hx'; simp at hx'
    | coe v => exact ⟨v, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, conj p.fPair (fun y => -p.g y) y0 = C := by
    induction hk : conj p.fPair (fun y => -p.g y) y0 using EReal.rec with
    | bot =>
      exfalso
      obtain ⟨y, hy⟩ := p.g_some_finite
      have e : ((p.fPair.pair y y0 : ℝ) : EReal) - (fun y => -p.g y) y
          ≤ conj p.fPair (fun y => -p.g y) y0 :=
        le_iSup (fun w => ((p.fPair.pair w y0 : ℝ) : EReal) - (fun y => -p.g y) w) y
      rw [hk] at e
      have hnt := p.g_no_pos_inf y
      induction hgy : p.g y using EReal.rec with
      | bot => exact hy hgy
      | top => exact hnt hgy
      | coe γ =>
        simp only [hgy] at e
        have : ((p.fPair.pair y y0 + γ : ℝ) : EReal) ≤ ⊥ := by
          rw [EReal.coe_add]; rwa [sub_eq_add_neg, neg_neg] at e
        exact absurd (le_bot_iff.1 this) (EReal.coe_ne_bot _)
    | top => rw [hk] at hy0; simp at hy0
    | coe v => exact ⟨v, rfl⟩
  rw [hF1] at hx'
  rw [hC] at hy0
  have hx'' : α < p.ePair.pair (-xt) x' - F1 := by exact_mod_cast hx'
  have hy0'' : β < p.fPair.pair (p.A (-xt) - 0) y0 - C := by exact_mod_cast hy0
  -- -gstar (-y0) ≤ C
  have hgs : ((-C : ℝ) : EReal) ≤ p.gstar (-y0) := by
    refine le_iInf fun y => ?_
    have e : ((p.fPair.pair y y0 : ℝ) : EReal) - (fun y => -p.g y) y
        ≤ conj p.fPair (fun y => -p.g y) y0 :=
      le_iSup (fun w => ((p.fPair.pair w y0 : ℝ) : EReal) - (fun y => -p.g y) w) y
    rw [hC] at e
    have hnt := p.g_no_pos_inf y
    induction hgy : p.g y using EReal.rec with
    | bot => simp
    | top => exact absurd hgy hnt
    | coe γ =>
      simp only [hgy] at e
      have e' : p.fPair.pair y y0 + γ ≤ C := by
        have : ((p.fPair.pair y y0 + γ : ℝ) : EReal) ≤ C := by
          rw [EReal.coe_add]; rw [sub_eq_add_neg, neg_neg] at e; exact e
        exact_mod_cast this
      rw [map_neg]
      have : -C ≤ -p.fPair.pair y y0 - γ := by linarith
      exact_mod_cast this
  have hz := hsub (p.Astar (-y0) - x')
  have hd : p.dualH (p.Astar (-y0) - x') ≤ -p.gstar (-y0) - -p.fstar (p.Astar (-y0) - (p.Astar (-y0) - x')) :=
    iInf_le (fun y' => -p.gstar y' - -p.fstar (p.Astar y' - (p.Astar (-y0) - x'))) (-y0)
  have heq : -p.gstar (-y0) - -p.fstar (p.Astar (-y0) - (p.Astar (-y0) - x'))
      = -p.gstar (-y0) + (F1 : EReal) := by
    rw [sub_sub_cancel, hF1, sub_eq_add_neg, neg_neg]
  rw [heq] at hd
  have hg' : -p.gstar (-y0) ≤ (C : EReal) := by
    rw [EReal.neg_le]; rw [EReal.coe_neg] at hgs; exact hgs
  have hfin : ((r + p.ePair.pair xt (p.Astar (-y0) - x') : ℝ) : EReal) ≤ ((C + F1 : ℝ) : EReal) := by
    rw [EReal.coe_add C F1]
    exact hz.trans (hd.trans (add_le_add hg' le_rfl))
  have hfin' : r + p.ePair.pair xt (p.Astar (-y0) - x') ≤ C + F1 := by exact_mod_cast hfin
  have hadj : p.fPair.pair (p.A (-xt) - 0) y0 = -p.ePair.pair xt (p.Astar y0) := by
    rw [sub_zero, p.adjoint, map_neg, LinearMap.neg_apply]
  rw [hadj] at hy0''
  have hp1 : p.ePair.pair xt (p.Astar (-y0) - x') = -p.ePair.pair xt (p.Astar y0) - p.ePair.pair xt x' := by
    rw [map_sub, map_neg, map_neg]
  have hp2 : p.ePair.pair (-xt) x' = -p.ePair.pair xt x' := by
    rw [map_neg, LinearMap.neg_apply]
  rw [hp1] at hfin'
  rw [hp2] at hx''
  linarith

set_option maxHeartbeats 1000000 in
lemma sub_of_attained (x : E) (V : ℝ) (hx : p.primalAt 0 x = V) :
    ∀ z', ((-V + p.ePair.pair (-x) z' : ℝ) : EReal) ≤ p.dualH z' := by
  intro z'
  obtain ⟨φ, γ, hφ, hγ, hV⟩ : ∃ φ γ : ℝ, p.f x = φ ∧ p.g (p.A x - 0) = γ ∧ φ - γ = V := by
    have h1 := p.f_no_neg_inf x
    have h2 := p.g_no_pos_inf (p.A x - 0)
    unfold Program.primalAt at hx
    induction hf : p.f x using EReal.rec with
    | bot => exact absurd hf h1
    | top =>
      rw [hf, EReal.top_sub h2] at hx; exact absurd hx (EReal.coe_ne_top V).symm
    | coe φ =>
      induction hg : p.g (p.A x - 0) using EReal.rec with
      | bot => rw [hf, hg, EReal.coe_sub_bot] at hx; exact absurd hx (EReal.coe_ne_top V).symm
      | top => exact absurd hg h2
      | coe γ =>
        rw [hf, hg] at hx
        exact ⟨φ, γ, rfl, rfl, by exact_mod_cast hx⟩
  refine le_iInf fun y' => ?_
  have hF : ((p.ePair.pair x (p.Astar y' - z') : ℝ) : EReal) - p.f x ≤ p.fstar (p.Astar y' - z') :=
    le_iSup (fun w => ((p.ePair.pair w (p.Astar y' - z') : ℝ) : EReal) - p.f w) x
  have hG : p.gstar y' ≤ ((p.fPair.pair (p.A x - 0) y' : ℝ) : EReal) - p.g (p.A x - 0) :=
    iInf_le (fun y => ((p.fPair.pair y y' : ℝ) : EReal) - p.g y) (p.A x - 0)
  rw [hφ] at hF
  rw [hγ] at hG
  have hG' : ((-(p.fPair.pair (p.A x - 0) y' - γ) : ℝ) : EReal) ≤ -p.gstar y' := by
    rw [EReal.coe_neg, EReal.neg_le_neg_iff, EReal.coe_sub]; exact hG
  rw [sub_eq_add_neg, neg_neg]
  calc ((-V + p.ePair.pair (-x) z' : ℝ) : EReal)
      = ((-(p.fPair.pair (p.A x - 0) y' - γ) : ℝ) : EReal)
        + ((p.ePair.pair x (p.Astar y' - z') - φ : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        rw [sub_zero, p.adjoint, map_sub, map_neg, LinearMap.neg_apply]
        linarith
    _ ≤ -p.gstar y' + p.fstar (p.Astar y' - z') := by
        refine add_le_add hG' ?_
        rw [EReal.coe_sub]; exact hF

set_option maxHeartbeats 1000000 in
theorem part2 : IsLeast (Set.range (p.primalAt 0)) p.dualValue ↔ StablySet p.dualH := by
  have hlb := weak2 p
  have hH0 := dualH0 p
  have hcases : p.dualValue = ⊥ ∨ p.dualValue = ⊤ ∨ ∃ V : ℝ, p.dualValue = V := by
    induction p.dualValue using EReal.rec <;> simp
  rcases hcases with hbot | htop | ⟨V, hV⟩
  · constructor
    · rintro ⟨⟨x, hx⟩, -⟩
      rw [hbot] at hx
      exact absurd hx (primal_ne_bot p x)
    · rintro ⟨hlt, -⟩
      rw [hH0, hbot] at hlt
      simp at hlt
  · constructor
    · intro _
      refine ⟨by rw [hH0, htop]; simp, ?_⟩
      rintro ⟨r, hr, -⟩
      rw [hH0, htop] at hr
      simp at hr
    · intro _
      rw [htop]
      refine ⟨⟨0, top_le_iff.1 (htop ▸ hlb 0)⟩, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact htop ▸ hlb x
  · have h0 : p.dualH 0 = ((-V : ℝ) : EReal) := by rw [hH0, hV, EReal.coe_neg]
    constructor
    · rintro ⟨⟨x, hx⟩, -⟩
      rw [hV] at hx
      have hsub := sub_of_attained p x V hx
      let l : E' →L[ℝ] ℝ := ⟨p.ePair.pair (-x), p.ePair.continuous_right (-x)⟩
      exact sub_stable h0 l (fun z => hsub z)
    · intro hs
      obtain ⟨l, hl⟩ := stable_sub (dualH_conv p) h0 hs.2
      obtain ⟨xt, hxt, -⟩ := p.ePair.represents_right l
      have hsub : ∀ z', ((-V + p.ePair.pair xt z' : ℝ) : EReal) ≤ p.dualH z' := fun z' => by
        rw [← hxt z']; exact hl z'
      have h1 := attained_of_sub p (-V) xt hsub
      rw [neg_neg] at h1
      have h2 : p.primalAt 0 (-xt) = p.dualValue := le_antisymm (hV ▸ h1) (hlb _)
      refine ⟨⟨-xt, h2⟩, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hlb x

theorem main : (StablySet p.h ↔ IsGreatest (Set.range p.dualAt) (p.h 0)) ∧
    (IsLeast (Set.range (p.primalAt 0)) p.dualValue ↔ StablySet p.dualH) :=
  ⟨part1 p, part2 p⟩

end Prog

end DS3

open DualityStability.StrongDuality in
theorem solution {E E' F F' : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
    [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']
    (p : Program E E' F F') :
    (StablySet p.h ↔ IsGreatest (Set.range p.dualAt) (p.h 0)) ∧
    (IsLeast (Set.range (p.primalAt 0)) p.dualValue ↔ StablySet p.dualH) := by
  exact DS3.main p
