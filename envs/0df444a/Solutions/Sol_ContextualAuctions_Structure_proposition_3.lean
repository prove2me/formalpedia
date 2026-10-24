-- Prove2me | solution 1 for ContextualAuctions.Structure.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T08:41:42.190009+00:00
-- url     : https://prove2.me/submissions/0878fcc8-b918-485f-abd8-d9ec5cf72bc5

import Mathlib
import Definitions.Def_ContextualAuctions_Structure_Setting
import Definitions.Def_ContextualAuctions_Structure_Structural

open MeasureTheory Set ContextualAuctions.Structure Pointwise

namespace CAProp3Aux

/-! ### Pure real analysis on a convex function `Q` -/

/-- Change of variables `t ↦ (1+t)/c - 1` transports a unique minimizer. -/
lemma conv_um (Q f : ℝ → ℝ) (c K T μ : ℝ) (hc : 0 < c)
    (hf : ∀ t, f t = c * Q ((1 + t) / c - 1) + K)
    (h : IsUniqueMinOn f (Icc 0 T) μ) :
    IsUniqueMinOn Q (Icc (1 / c - 1) ((1 + T) / c - 1)) ((1 + μ) / c - 1) := by
  obtain ⟨hmem, hmin, huniq⟩ := h
  have back : ∀ τ, (1 + (c * (1 + τ) - 1)) / c - 1 = τ := by
    intro τ; field_simp; ring
  have memJ : ∀ t ∈ Icc (0:ℝ) T, (1 + t) / c - 1 ∈ Icc (1 / c - 1) ((1 + T) / c - 1) := by
    intro t ht
    constructor
    · have : 1 / c ≤ (1 + t) / c := div_le_div_of_nonneg_right (by linarith [ht.1]) hc.le
      linarith
    · have : (1 + t) / c ≤ (1 + T) / c := div_le_div_of_nonneg_right (by linarith [ht.2]) hc.le
      linarith
  have memI : ∀ τ ∈ Icc (1 / c - 1) ((1 + T) / c - 1), c * (1 + τ) - 1 ∈ Icc (0:ℝ) T := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hτ
    have e1 : 1 / c ≤ 1 + τ := by linarith
    have e2 : 1 + τ ≤ (1 + T) / c := by linarith
    rw [div_le_iff₀ hc] at e1
    rw [le_div_iff₀ hc] at e2
    constructor <;> nlinarith
  refine ⟨memJ μ hmem, ?_, ?_⟩
  · intro τ hτ
    have := hmin (memI τ hτ)
    simp only [Set.mem_setOf_eq, hf, back] at this
    have h2 := (mul_le_mul_iff_of_pos_left hc).1 (by linarith : c * Q ((1 + μ) / c - 1) ≤ c * Q τ)
    exact h2
  · intro τ hτ hτmin
    have key : c * (1 + τ) - 1 = μ := by
      apply huniq _ (memI τ hτ)
      intro t ht
      have := hτmin (memJ t ht)
      simp only [Set.mem_setOf_eq] at this ⊢
      rw [hf, hf, back]
      nlinarith
    rw [← key]; field_simp; ring

/-- An interior unique minimizer on a window is a global minimizer on `(-1, ∞)`. -/
lemma interior_global (Q : ℝ → ℝ) (hQ : ConvexOn ℝ (Ioi (-1)) Q) (l h τ : ℝ)
    (hl : -1 ≤ l) (hτ : τ ∈ Ioo l h) (hmin : IsMinOn Q (Icc l h) τ) :
    IsMinOn Q (Ioi (-1)) τ := by
  have hτ1 : τ ∈ Ioi (-1 : ℝ) := by simp only [mem_Ioi]; linarith [hτ.1]
  apply IsMinOn.of_isLocalMinOn_of_convexOn hτ1 _ hQ
  have hn : Ioo l h ∈ nhds τ := Ioo_mem_nhds hτ.1 hτ.2
  have : ∀ᶠ y in nhds τ, Q τ ≤ Q y := by
    filter_upwards [hn] with y hy
    exact hmin ⟨hy.1.le, hy.2.le⟩
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds this

/-- Lemma B: an interior unique minimizer coincides with any other point of no larger value. -/
lemma interior_unique (Q : ℝ → ℝ) (hQ : ConvexOn ℝ (Ioi (-1)) Q) (l h τ₁ τ₂ : ℝ)
    (hl : -1 ≤ l) (hτ : τ₁ ∈ Ioo l h) (hum : IsUniqueMinOn Q (Icc l h) τ₁)
    (hτ₂ : -1 < τ₂) (hle : Q τ₂ ≤ Q τ₁) : τ₁ = τ₂ := by
  obtain ⟨-, hmin, huniq⟩ := hum
  have hL : (({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q τ₁}) : Set ℝ).OrdConnected :=
    convex_iff_ordConnected.1 (hQ.convex_le _)
  have h1 : τ₁ ∈ ({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q τ₁}) :=
    ⟨by simp only [mem_Ioi]; linarith [hτ.1], le_rfl⟩
  have h2 : τ₂ ∈ ({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q τ₁}) := ⟨hτ₂, hle⟩
  by_contra hne
  have finish : ∀ z, z ∈ ({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q τ₁}) → z ∈ Icc l h → z ≠ τ₁ → False := by
    intro z hz hzJ hzne
    apply hzne
    apply huniq z hzJ
    intro x hx
    exact le_trans hz.2 (hmin hx)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · set z := min τ₂ ((τ₁ + h) / 2)
    have hz1 : τ₁ < z := lt_min hlt (by linarith [hτ.2])
    have hz2 : z ≤ τ₂ := min_le_left _ _
    have hz3 : z ≤ (τ₁ + h) / 2 := min_le_right _ _
    exact finish z (hL.out h1 h2 ⟨hz1.le, hz2⟩) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ hz1.ne'
  · set z := max τ₂ ((τ₁ + l) / 2)
    have hz1 : z < τ₁ := max_lt hgt (by linarith [hτ.1])
    have hz2 : τ₂ ≤ z := le_max_left _ _
    have hz3 : (τ₁ + l) / 2 ≤ z := le_max_right _ _
    exact finish z (hL.out h2 h1 ⟨hz2, hz1.le⟩) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ hz1.ne

/-- Lemma C: the left endpoint of a window, when it is the unique minimizer there, lies to the
right of every global minimizer. -/
lemma unpaced_ge (Q : ℝ → ℝ) (hQ : ConvexOn ℝ (Ioi (-1)) Q) (l h ρ : ℝ)
    (hl : -1 < l) (hlh : l < h) (hum : IsUniqueMinOn Q (Icc l h) l)
    (hρ : -1 < ρ) (hρmin : IsMinOn Q (Ioi (-1)) ρ) : ρ ≤ l := by
  obtain ⟨-, hmin, huniq⟩ := hum
  by_contra hcon
  push Not at hcon
  have hL : (({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q l}) : Set ℝ).OrdConnected :=
    convex_iff_ordConnected.1 (hQ.convex_le _)
  have h1 : l ∈ ({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q l}) := ⟨hl, le_rfl⟩
  have h2 : ρ ∈ ({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q l}) := ⟨hρ, hρmin (show l ∈ Ioi (-1 : ℝ) from hl)⟩
  set z := min ρ h
  have hz1 : l < z := lt_min hcon hlh
  have hz2 : z ≤ ρ := min_le_left _ _
  have hz3 : z ≤ h := min_le_right _ _
  have hz : z ∈ ({x ∈ Ioi (-1 : ℝ) | Q x ≤ Q l}) := hL.out h1 h2 ⟨hz1.le, hz2⟩
  have : z = l := huniq z ⟨hz1.le, hz3⟩ (fun x hx => le_trans hz.2 (hmin hx))
  linarith


/-! ### The dual function `q^µ` -/

open Classical in
/-- The objective of the inner supremum of `q^µ` for a given bid function. -/
noncomputable def Gb (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (b : (Fin M.d → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, (if wins M (beta M mu) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M

/-- The set whose supremum appears in `q^µ`. -/
def Sset (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) : Set ℝ :=
  {v | ∃ b, Admissible M (beta M mu) b ∧ v = Gb M mu θ b t}

lemma q_eq (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) :
    qDual M mu θ t = sSup (Sset M mu θ t) + t * θ.2 := rfl

lemma adm_zero (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) :
    Admissible M (beta M mu) (fun _ => 0) := by
  refine ⟨measurable_const, fun _ => le_rfl, ?_⟩
  simp

lemma Sset_nonempty (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) :
    (Sset M mu θ t).Nonempty := ⟨_, _, adm_zero M mu, rfl⟩

lemma Gb_affine (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M mu) b) (x y a c : ℝ) (hac : a + c = 1) :
    Gb M mu θ b (a * x + c * y) = a * Gb M mu θ b x + c * Gb M mu θ b y := by
  classical
  set X : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) → ℝ :=
    fun ω => if wins M (beta M mu) b ω then val θ ω.1 else 0 with hXdef
  set Y : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) → ℝ :=
    fun ω => if wins M (beta M mu) b ω then b ω.1 else 0 with hYdef
  have hY : Integrable Y (P M) := hb.2.2
  have key : ∀ t, (fun ω => if wins M (beta M mu) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0)
      = fun ω => X ω - (1 + t) * Y ω := by
    intro t; funext ω; simp only [hXdef, hYdef]; split_ifs <;> ring
  by_cases hX : Integrable X (P M)
  · have hG : ∀ t, Gb M mu θ b t = (∫ ω, X ω ∂P M) - (1 + t) * ∫ ω, Y ω ∂P M := by
      intro t; unfold Gb; rw [key t, integral_sub hX (hY.const_mul _), integral_const_mul]
    rw [hG, hG, hG]
    have : c = 1 - a := by linarith
    subst this; ring
  · have hG : ∀ t, Gb M mu θ b t = 0 := by
      intro t; unfold Gb; rw [key t]; apply integral_undef
      intro h; apply hX
      have h2 := h.add (hY.const_mul (1 + t))
      have e : ((fun a => X a - (1 + t) * Y a) + fun x => (1 + t) * Y x) = X := by
        funext ω; simp
      rwa [e] at h2
    simp [hG]

lemma ae_mem_A (M : Model) (hM : M.Standing) : ∀ᵐ ω ∂(P M), ω.1 ∈ M.A := by
  haveI := hM.probF; haveI := hM.probG
  have h2 : IsFiniteMeasure (Measure.pi fun _ : Fin (M.n - 1) => M.G) := inferInstance
  haveI : SFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) :=
    @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ h2)
  rw [ae_iff]
  have : {ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) | ¬ ω.1 ∈ M.A}
      = M.Aᶜ ×ˢ Set.univ := by ext ω; simp
  rw [this]; unfold P; rw [Measure.prod_prod, hM.F_A, zero_mul]

lemma P_prob (M : Model) (hM : M.Standing) : IsProbabilityMeasure (P M) := by
  haveI := hM.probF; haveI := hM.probG
  unfold P; infer_instance

lemma Gb_le (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M mu) b) (C t : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ α ∈ M.A, val θ α ≤ C) (ht : -1 ≤ t) : Gb M mu θ b t ≤ C := by
  classical
  have := P_prob M hM
  unfold Gb
  by_cases hi : Integrable (fun ω => if wins M (beta M mu) b ω then val θ ω.1 - (1 + t) * b ω.1
      else 0) (P M)
  · calc _ ≤ ∫ _, C ∂(P M) := integral_mono_ae hi (integrable_const C) ?_
      _ = C := by simp
    filter_upwards [ae_mem_A M hM] with ω hω
    split_ifs
    · have h1 := hb.2.1 ω.1; have h2 := hC _ hω; nlinarith
    · exact hC0
  · rw [integral_undef hi]; exact hC0

lemma Gb_zero_nonneg (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ)
    (θ : (Fin M.d → ℝ) × ℝ) (hθ : ∀ α ∈ M.A, 0 ≤ val θ α) (t : ℝ) :
    0 ≤ Gb M mu θ (fun _ => 0) t := by
  unfold Gb
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_A M hM] with ω hω
  split_ifs
  · simpa using hθ _ hω
  · exact le_rfl

lemma Sset_bdd (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (C t : ℝ) (hC0 : 0 ≤ C) (hC : ∀ α ∈ M.A, val θ α ≤ C) (ht : -1 ≤ t) :
    ∀ v ∈ Sset M mu θ t, v ≤ C := by
  rintro v ⟨b, hb, rfl⟩
  exact Gb_le M hM mu θ b hb C t hC0 hC ht

lemma q_convex (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ α ∈ M.A, val θ α ≤ C) :
    ConvexOn ℝ (Ioi (-1)) (qDual M mu θ) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a c ha hc hac
  simp only [smul_eq_mul]
  simp only [mem_Ioi] at hx hy
  have hbx : BddAbove (Sset M mu θ x) := ⟨C, Sset_bdd M hM mu θ C x hC0 hC hx.le⟩
  have hby : BddAbove (Sset M mu θ y) := ⟨C, Sset_bdd M hM mu θ C y hC0 hC hy.le⟩
  have h1 : sSup (Sset M mu θ (a * x + c * y)) ≤
      a * sSup (Sset M mu θ x) + c * sSup (Sset M mu θ y) := by
    apply csSup_le (Sset_nonempty M mu θ _)
    rintro v ⟨b, hb, rfl⟩
    rw [Gb_affine M mu θ b hb x y a c hac]
    have e1 := le_csSup hbx ⟨b, hb, rfl⟩
    have e2 := le_csSup hby ⟨b, hb, rfl⟩
    have := mul_le_mul_of_nonneg_left e1 ha
    have := mul_le_mul_of_nonneg_left e2 hc
    linarith
  rw [q_eq, q_eq, q_eq]
  nlinarith

lemma val_smul {d : ℕ} (c : ℝ) (w : Fin d → ℝ) (B : ℝ) (α : Fin d → ℝ) :
    val (c • w, B) α = c * val (w, B) α := by
  simp [val, Finset.mul_sum, mul_assoc]

lemma q_scale (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (w : Fin M.d → ℝ) (B c t : ℝ)
    (hc : 0 < c) :
    qDual M mu (c • w, B) t = c * qDual M mu (w, B) ((1 + t) / c - 1) + (c - 1) * B := by
  have hG : ∀ b, Gb M mu (c • w, B) b t = c * Gb M mu (w, B) b ((1 + t) / c - 1) := by
    intro b
    unfold Gb
    rw [← integral_const_mul]
    congr 1; funext ω
    split_ifs
    · rw [val_smul]; field_simp; ring
    · simp
  have hS : Sset M mu (c • w, B) t = c • Sset M mu (w, B) ((1 + t) / c - 1) := by
    ext v
    simp only [Sset, Set.mem_smul_set, mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨_, ⟨b, hb, rfl⟩, (hG b).symm⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩; exact ⟨b, hb, (hG b).symm⟩
  rw [q_eq, q_eq, hS, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]
  simp only
  field_simp
  ring


/-! ### `ω`, the type space and the support -/

lemma val_pos (M : Model) (hM : M.Standing) (θ : (Fin M.d → ℝ) × ℝ) (hθ : θ ∈ Theta M)
    (α : Fin M.d → ℝ) (hα : α ∈ M.A) : 0 < val θ α := by
  have hne : (Finset.univ : Finset (Fin M.d)).Nonempty :=
    ⟨⟨0, by have := hM.two_le_d; omega⟩, Finset.mem_univ _⟩
  unfold val
  exact Finset.sum_pos (fun i _ => mul_pos (hθ.1 i).1 (hM.A_pos hα i)) hne

lemma omega_bdd (M : Model) (hM : M.Standing) :
    BddAbove {v | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val θ α} := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hM.A_bounded
  refine ⟨M.d * (M.U * R), ?_⟩
  rintro v ⟨θ, hθ, α, hα, rfl⟩
  unfold val
  calc ∑ i, θ.1 i * α i ≤ ∑ _i : Fin M.d, M.U * R := by
        apply Finset.sum_le_sum; intro i _
        have h1 := (hθ.1 i); have h2 := hM.A_pos hα i
        have h3 : α i ≤ R := le_trans (le_trans (le_abs_self _)
          (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm α i)) (hR α hα)
        nlinarith [h1.1, h1.2]
    _ = M.d * (M.U * R) := by simp

lemma val_le_omega (M : Model) (hM : M.Standing) (θ : (Fin M.d → ℝ) × ℝ) (hθ : θ ∈ Theta M)
    (α : Fin M.d → ℝ) (hα : α ∈ M.A) : val θ α ≤ omega M :=
  le_csSup (omega_bdd M hM) ⟨θ, hθ, α, hα, rfl⟩

lemma omega_pos (M : Model) (hM : M.Standing) (θ : (Fin M.d → ℝ) × ℝ) (hθ : θ ∈ Theta M) :
    0 < omega M := by
  obtain ⟨α0, hα0⟩ := hM.A_nonempty
  exact lt_of_lt_of_le (val_pos M hM θ hθ α0 hα0) (val_le_omega M hM θ hθ α0 hα0)

/-- The best response never sits at the upper end `ω / B_min` of the dual interval. -/
lemma mu_lt (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (h6 : SixStanding M mu)
    (θ : (Fin M.d → ℝ) × ℝ) (hθ : θ ∈ supp M) : mu θ < omega M / M.Bmin := by
  have hΘ := h6.supp_subset hθ
  obtain ⟨hmem, hmin, -⟩ := h6.unique_best_response θ hθ
  have hωpos := omega_pos M hM θ hΘ
  have hBmin := hM.Bmin_pos
  have hT : 0 ≤ omega M / M.Bmin := by positivity
  have hC : ∀ α ∈ M.A, val θ α ≤ omega M := fun α hα => val_le_omega M hM θ hΘ α hα
  have hq0 : qDual M mu θ 0 ≤ omega M := by
    rw [q_eq, zero_mul, add_zero]
    exact csSup_le (Sset_nonempty M mu θ 0) (Sset_bdd M hM mu θ _ 0 hωpos.le hC (by norm_num))
  have hqT : omega M / M.Bmin * θ.2 ≤ qDual M mu θ (omega M / M.Bmin) := by
    rw [q_eq]
    have hb : BddAbove (Sset M mu θ (omega M / M.Bmin)) :=
      ⟨_, Sset_bdd M hM mu θ _ _ hωpos.le hC (by linarith)⟩
    have e1 := le_csSup hb ⟨_, adm_zero M mu, rfl⟩
    have e2 := Gb_zero_nonneg M hM mu θ (fun α hα => (val_pos M hM θ hΘ α hα).le)
      (omega M / M.Bmin)
    linarith
  have hTB : omega M < omega M / M.Bmin * θ.2 := by
    have hB := hΘ.2.1
    rw [div_mul_eq_mul_div, lt_div_iff₀ hBmin]; nlinarith
  rcases lt_or_eq_of_le hmem.2 with h | h
  · exact h
  · exfalso
    have := hmin (show (0:ℝ) ∈ Icc 0 (omega M / M.Bmin) from ⟨le_rfl, hT⟩)
    simp only [Set.mem_setOf_eq] at this
    rw [h] at this; linarith

lemma wnorm_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) : wnorm (c • v) = |c| * wnorm v := by
  unfold wnorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end CAProp3Aux

open CAProp3Aux

theorem solution (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ)
    (h6 : SixStanding M mu) (what : Fin M.d → ℝ) (hunit : wnorm what = 1)
    (hpos : ∀ i, 0 < what i) (B : ℝ) (hB : 0 < B)
    (hray : ∃ w, (w, B) ∈ supp M ∧ (wnorm w)⁻¹ • w = what) :
    (∀ w₁ w₂ : Fin M.d → ℝ, (w₁, B) ∈ supp M → (w₂, B) ∈ supp M →
        (wnorm w₁)⁻¹ • w₁ = what → (wnorm w₂)⁻¹ • w₂ = what →
        0 < mu (w₁, B) → 0 < mu (w₂, B) →
        (1 + mu (w₁, B))⁻¹ • w₁ = (1 + mu (w₂, B))⁻¹ • w₂) ∧
    ((∃ w, (w, B) ∈ supp M ∧ (wnorm w)⁻¹ • w = what ∧ mu (w, B) = 0) →
      ∃ w₀ : Fin M.d → ℝ,
        ((w₀, B) ∈ supp M ∧ (wnorm w₀)⁻¹ • w₀ = what ∧ mu (w₀, B) = 0) ∧
        (∀ w, (w, B) ∈ supp M → (wnorm w)⁻¹ • w = what → mu (w, B) = 0 →
          wnorm w ≤ wnorm w₀) ∧
        ∀ w, (w, B) ∈ supp M → (wnorm w)⁻¹ • w = what → 0 < mu (w, B) →
          (1 + mu (w, B))⁻¹ • w = w₀) := by
  obtain ⟨ws, hws, hwsdir⟩ := hray
  have dir : ∀ w : Fin M.d → ℝ, (wnorm w)⁻¹ • w = what → 0 < wnorm w ∧ w = wnorm w • what := by
    intro w hw
    have hne : wnorm w ≠ 0 := by
      intro h0; rw [h0, inv_zero, zero_smul] at hw
      rw [← hw] at hunit; simp [wnorm] at hunit
    have hnn : 0 ≤ wnorm w := Real.sqrt_nonneg _
    refine ⟨lt_of_le_of_ne hnn (Ne.symm hne), ?_⟩
    rw [← hw, smul_smul, mul_inv_cancel₀ hne, one_smul]
  obtain ⟨hs0, -⟩ := dir ws hwsdir
  obtain ⟨s0, hs0def⟩ : ∃ s, wnorm ws = s := ⟨_, rfl⟩
  rw [hs0def] at hs0 hwsdir
  have alongE : ∀ w, (wnorm w)⁻¹ • w = what → ∃ c : ℝ, 0 < c ∧ w = c • ws := by
    intro w hw
    obtain ⟨hwpos, hweq⟩ := dir w hw
    refine ⟨wnorm w / s0, div_pos hwpos hs0, ?_⟩
    calc w = wnorm w • what := hweq
      _ = wnorm w • (s0⁻¹ • ws) := by rw [hwsdir]
      _ = (wnorm w / s0) • ws := by rw [smul_smul, div_eq_mul_inv]
  have wnc : ∀ c : ℝ, 0 < c → wnorm (c • ws) = c * s0 := by
    intro c hc; rw [wnorm_smul, abs_of_pos hc, hs0def]
  have dirc : ∀ c : ℝ, 0 < c → (wnorm (c • ws))⁻¹ • (c • ws) = what := by
    intro c hc
    rw [wnc c hc, smul_smul, ← hwsdir]
    congr 1
    field_simp
  set T := omega M / M.Bmin with hTdef
  have hΘs := h6.supp_subset hws
  have hω := omega_pos M hM _ hΘs
  have hTpos : 0 < T := div_pos hω hM.Bmin_pos
  set Q := qDual M mu (ws, B) with hQdef
  have hQ : ConvexOn ℝ (Ioi (-1)) Q :=
    q_convex M hM mu (ws, B) (omega M) hω.le (fun α hα => val_le_omega M hM _ hΘs α hα)
  have um : ∀ c : ℝ, 0 < c → (c • ws, B) ∈ supp M →
      IsUniqueMinOn Q (Icc (1 / c - 1) ((1 + T) / c - 1)) ((1 + mu (c • ws, B)) / c - 1) := by
    intro c hc hmem
    exact conv_um Q (qDual M mu (c • ws, B)) c ((c - 1) * B) T _ hc
      (fun t => q_scale M mu ws B c t hc) (h6.unique_best_response _ hmem)
  have hl : ∀ c : ℝ, 0 < c → -1 < 1 / c - 1 := by
    intro c hc; have : 0 < 1 / c := by positivity
    linarith
  have hlh : ∀ c : ℝ, 0 < c → 1 / c - 1 < (1 + T) / c - 1 := by
    intro c hc
    have : 1 / c < (1 + T) / c := div_lt_div_of_pos_right (by linarith) hc
    linarith
  have inter : ∀ c : ℝ, 0 < c → (c • ws, B) ∈ supp M → 0 < mu (c • ws, B) →
      (1 + mu (c • ws, B)) / c - 1 ∈ Ioo (1 / c - 1) ((1 + T) / c - 1) := by
    intro c hc hmem hp
    have hlt := mu_lt M hM mu h6 _ hmem
    constructor
    · have : 1 / c < (1 + mu (c • ws, B)) / c := div_lt_div_of_pos_right (by linarith) hc
      linarith
    · have : (1 + mu (c • ws, B)) / c < (1 + T) / c := div_lt_div_of_pos_right (by linarith) hc
      linarith
  have glob : ∀ c : ℝ, 0 < c → (c • ws, B) ∈ supp M → 0 < mu (c • ws, B) →
      IsMinOn Q (Ioi (-1)) ((1 + mu (c • ws, B)) / c - 1) := by
    intro c hc hmem hp
    exact interior_global Q hQ _ _ _ (hl c hc).le (inter c hc hmem hp) (um c hc hmem).2.1
  have pvec : ∀ c : ℝ, 0 < c → (c • ws, B) ∈ supp M →
      (1 + mu (c • ws, B))⁻¹ • (c • ws) = (1 + ((1 + mu (c • ws, B)) / c - 1))⁻¹ • ws := by
    intro c hc hmem
    have hm := (h6.range _ (h6.supp_subset hmem)).1
    rw [smul_smul]
    congr 1
    rw [show (1:ℝ) + ((1 + mu (c • ws, B)) / c - 1) = (1 + mu (c • ws, B)) / c by ring, inv_div,
      div_eq_mul_inv, mul_comm]
  have tau_eq : ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → (c₁ • ws, B) ∈ supp M → (c₂ • ws, B) ∈ supp M →
      0 < mu (c₁ • ws, B) → 0 < mu (c₂ • ws, B) →
      (1 + mu (c₁ • ws, B)) / c₁ - 1 = (1 + mu (c₂ • ws, B)) / c₂ - 1 := by
    intro c₁ c₂ hc₁ hc₂ hm₁ hm₂ hp₁ hp₂
    have i₂ := inter c₂ hc₂ hm₂ hp₂
    have g₂ := glob c₂ hc₂ hm₂ hp₂
    have i₁ := inter c₁ hc₁ hm₁ hp₁
    exact interior_unique Q hQ _ _ _ _ (hl c₁ hc₁).le i₁ (um c₁ hc₁ hm₁)
      (by linarith [i₂.1, hl c₂ hc₂])
      (g₂ (show _ ∈ Ioi (-1 : ℝ) by simp only [mem_Ioi]; linarith [i₁.1, hl c₁ hc₁]))
  refine ⟨?_, ?_⟩
  · intro w₁ w₂ h₁ h₂ d₁ d₂ p₁ p₂
    obtain ⟨c₁, hc₁, rfl⟩ := alongE w₁ d₁
    obtain ⟨c₂, hc₂, rfl⟩ := alongE w₂ d₂
    rw [pvec c₁ hc₁ h₁, pvec c₂ hc₂ h₂, tau_eq c₁ c₂ hc₁ hc₂ h₁ h₂ p₁ p₂]
  · rintro ⟨wu, hu, du, mu0⟩
    obtain ⟨cu, hcu, rfl⟩ := alongE wu du
    by_cases hp : ∃ c : ℝ, 0 < c ∧ (c • ws, B) ∈ supp M ∧ 0 < mu (c • ws, B)
    · obtain ⟨cp, hcp, hpm, hpp⟩ := hp
      set ρ := (1 + mu (cp • ws, B)) / cp - 1 with hρdef
      have hρg : IsMinOn Q (Ioi (-1)) ρ := glob cp hcp hpm hpp
      have hρi := inter cp hcp hpm hpp
      have hρ1 : -1 < ρ := by linarith [hρi.1, hl cp hcp]
      have unp : ∀ c : ℝ, 0 < c → (c • ws, B) ∈ supp M → mu (c • ws, B) = 0 → ρ ≤ 1 / c - 1 := by
        intro c hc hm h0
        have := um c hc hm
        rw [h0, add_zero] at this
        exact unpaced_ge Q hQ _ _ ρ (hl c hc) (hlh c hc) this hρ1 hρg
      have h1ρ : 0 < 1 + ρ := by linarith
      set c0 := 1 / (1 + ρ) with hc0def
      have hc0 : 0 < c0 := by positivity
      have hcu_le : cu ≤ c0 := by
        have := unp cu hcu hu mu0
        rw [hc0def, le_div_iff₀ h1ρ]
        have h' : 1 + ρ ≤ 1 / cu := by linarith
        rw [le_div_iff₀ hcu] at h'
        linarith
      have hcp_gt : c0 < cp := by
        have h' : 1 / cp < 1 + ρ := by linarith [hρi.1]
        rw [div_lt_iff₀ hcp] at h'
        rw [hc0def, div_lt_iff₀ h1ρ]
        linarith
      have hmem0 : (c0 • ws, B) ∈ supp M := by
        have hd : 0 < cp - cu := by linarith
        have hconv := h6.supp_convex hu hpm (a := (cp - c0) / (cp - cu)) (b := (c0 - cu) / (cp - cu))
          (div_nonneg (by linarith) hd.le) (div_nonneg (by linarith) hd.le)
          (by field_simp; ring)
        convert hconv using 1
        ext i
        · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          field_simp
          ring
      have hmu0 : mu (c0 • ws, B) = 0 := by
        have hum := um c0 hc0 hmem0
        have e1 : 1 / c0 = 1 + ρ := by rw [hc0def]; field_simp
        have hρJ : ρ ∈ Icc (1 / c0 - 1) ((1 + T) / c0 - 1) := by
          constructor
          · rw [e1]; linarith
          · rw [div_eq_mul_one_div, e1]; nlinarith
        have := hum.2.2 ρ hρJ (fun x hx => hρg (show x ∈ Ioi (-1 : ℝ) by
          simp only [mem_Ioi]; linarith [hx.1, hl c0 hc0]))
        rw [div_eq_mul_one_div, e1] at this
        have hm := (h6.range _ (h6.supp_subset hmem0)).1
        nlinarith
      refine ⟨c0 • ws, ⟨hmem0, dirc c0 hc0, hmu0⟩, ?_, ?_⟩
      · intro w hw dw m0
        obtain ⟨c, hc, rfl⟩ := alongE w dw
        rw [wnc c hc, wnc c0 hc0]
        have := unp c hc hw m0
        have hcc : c ≤ c0 := by
          rw [hc0def, le_div_iff₀ h1ρ]
          have h' : 1 + ρ ≤ 1 / c := by linarith
          rw [le_div_iff₀ hc] at h'
          linarith
        exact mul_le_mul_of_nonneg_right hcc hs0.le
      · intro w hw dw pw
        obtain ⟨c, hc, rfl⟩ := alongE w dw
        rw [pvec c hc hw, tau_eq c cp hc hcp hw hpm pw hpp, ← hρdef, hc0def, one_div]
    · push Not at hp
      set Cset : Set ℝ := {c : ℝ | (c • ws, B) ∈ supp M} with hCdef
      have i0 : Fin M.d := ⟨0, by have := hM.two_le_d; omega⟩
      have hws0 : 0 < ws i0 := (hΘs.1 i0).1
      have hclosed : IsClosed Cset :=
        h6.supp_compact.isClosed.preimage
          ((continuous_id.smul continuous_const).prodMk continuous_const)
      have hpos' : ∀ c ∈ Cset, 0 < c := by
        intro c hc
        have := ((h6.supp_subset hc).1 i0).1
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact pos_of_mul_pos_left this hws0.le
      have hbdd : BddAbove Cset := by
        refine ⟨M.U / ws i0, fun c hc => ?_⟩
        have := ((h6.supp_subset hc).1 i0).2
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [le_div_iff₀ hws0]; linarith
      have h1C : (1 : ℝ) ∈ Cset := by simp only [hCdef, mem_setOf_eq, one_smul]; exact hws
      have hne : Cset.Nonempty := ⟨1, h1C⟩
      have hcm : sSup Cset ∈ Cset := hclosed.csSup_mem hne hbdd
      have hcmpos := hpos' _ hcm
      refine ⟨sSup Cset • ws, ⟨hcm, dirc _ hcmpos, ?_⟩, ?_, ?_⟩
      · exact le_antisymm (hp _ hcmpos hcm) (h6.range _ (h6.supp_subset hcm)).1
      · intro w hw dw _
        obtain ⟨c, hc, rfl⟩ := alongE w dw
        rw [wnc c hc, wnc _ hcmpos]
        exact mul_le_mul_of_nonneg_right (le_csSup hbdd hw) hs0.le
      · intro w hw dw pw
        obtain ⟨c, hc, rfl⟩ := alongE w dw
        exact absurd (hp c hc hw) (not_le.2 pw)
