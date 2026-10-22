-- Prove2me | solution 1 for CustomHedge.Exist.ec_27_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:02:16.668621+00:00
-- url     : https://prove2.me/submissions/04b47b41-a1cd-487b-bb8b-e7bfd46d5082

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model


open MeasureTheory ProbabilityTheory

namespace CHAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma int_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg

/-- expansion of `∫ (f + t h)^2`. -/
lemma expand {f h : Ω → ℝ} (hf : MemLp f 2 P) (hh : MemLp h 2 P) (t : ℝ) :
    ∫ ω, (f ω + t * h ω) ^ 2 ∂P =
      ∫ ω, f ω ^ 2 ∂P + 2 * t * ∫ ω, f ω * h ω ∂P + t ^ 2 * ∫ ω, h ω ^ 2 ∂P := by
  have e : (fun ω => (f ω + t * h ω) ^ 2) =
      fun ω => (f ω ^ 2 + (2 * t) * (f ω * h ω)) + t ^ 2 * h ω ^ 2 := by
    funext ω; ring
  rw [e, integral_add, integral_add, integral_const_mul, integral_const_mul]
  · exact hf.integrable_sq
  · exact (int_mul hf hh).const_mul _
  · exact hf.integrable_sq.add ((int_mul hf hh).const_mul _)
  · exact hh.integrable_sq.const_mul _

lemma cs {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, f ω * g ω ∂P) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂P) * ∫ ω, g ω ^ 2 ∂P := by
  set A := ∫ ω, f ω ^ 2 ∂P
  set B := ∫ ω, g ω ^ 2 ∂P
  set C := ∫ ω, f ω * g ω ∂P
  have key : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
    intro t
    rw [← expand hf hg t]
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun ω => sq_nonneg _)
  have hA : 0 ≤ A := integral_nonneg (fun ω => sq_nonneg _)
  rcases hB.lt_or_eq with hB | hB
  · have := key (-C / B)
    have e : A + 2 * (-C / B) * C + (-C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp; ring
    rw [e] at this
    have : C ^ 2 / B ≤ A := by linarith
    rw [div_le_iff₀ hB] at this
    linarith
  · rw [← hB]
    by_contra hC
    have hC' : C ≠ 0 := by
      intro h; apply hC; rw [h]; simp
    have := key (-(A + 1) / (2 * C))
    rw [← hB] at this
    have e : A + 2 * (-(A + 1) / (2 * C)) * C + (-(A + 1) / (2 * C)) ^ 2 * 0 = -1 := by
      field_simp; ring
    rw [e] at this
    linarith

lemma ae_zero_of_sq {f : Ω → ℝ} (hf : MemLp f 2 P) (h : ∫ ω, f ω ^ 2 ∂P = 0) :
    f =ᵐ[P] 0 := by
  have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω)) hf.integrable_sq).1 h
  filter_upwards [this] with ω hω
  simpa using hω

lemma sq_congr {f g : Ω → ℝ} (h : f =ᵐ[P] g) : ∫ ω, f ω ^ 2 ∂P = ∫ ω, g ω ^ 2 ∂P := by
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

variable {m : MeasurableSpace Ω}

/-- tower: `∫ f g = ∫ E[f|m] g` for `g` `m`-measurable. -/
lemma tower (hm : m ≤ mΩ) {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (hgm : StronglyMeasurable[m] g) :
    ∫ ω, f ω * g ω ∂P = ∫ ω, (P[f|m]) ω * g ω ∂P := by
  have h1 : P[f * g|m] =ᵐ[P] P[f|m] * g :=
    condExp_mul_of_stronglyMeasurable_right hgm (int_mul hf hg) (hf.integrable one_le_two)
  have h2 := integral_condExp hm (μ := P) (f := f * g)
  calc ∫ ω, f ω * g ω ∂P = ∫ ω, (f * g) ω ∂P := rfl
    _ = ∫ ω, (P[f * g|m]) ω ∂P := h2.symm
    _ = ∫ ω, (P[f|m] * g) ω ∂P := integral_congr_ae h1
    _ = _ := rfl

lemma memLp_condExp {f : Ω → ℝ} (hf : MemLp f 2 P) : MemLp (P[f|m]) 2 P :=
  hf.condExp one_le_two

lemma sq_condExp_eq (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, (P[f|m]) ω ^ 2 ∂P = ∫ ω, f ω * (P[f|m]) ω ∂P := by
  rw [tower hm hf (memLp_condExp hf) stronglyMeasurable_condExp]
  congr 1; funext ω; ring

lemma sq_condExp_le (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, (P[f|m]) ω ^ 2 ∂P ≤ ∫ ω, f ω ^ 2 ∂P := by
  have h := cs hf (memLp_condExp (m := m) hf)
  rw [← sq_condExp_eq hm hf] at h
  have h0 : 0 ≤ ∫ ω, (P[f|m]) ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  have h1 : 0 ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  nlinarith


open CustomHedge.Exist

lemma var_eq {m : MeasurableSpace Ω} {φ : Ω → ℝ} (h : InCentered P m φ) :
    variance φ P = ∫ ω, φ ω ^ 2 ∂P := by
  rw [variance_eq_integral h.1.2.1.aemeasurable, h.2]
  simp

lemma pearson_eq {m₁ m₂ : MeasurableSpace Ω} {φ ψ : Ω → ℝ} (hφ : InCentered P m₁ φ)
    (hψ : InCentered P m₂ ψ) :
    pearsonCorr P φ ψ = (∫ ω, φ ω * ψ ω ∂P) /
      Real.sqrt ((∫ ω, φ ω ^ 2 ∂P) * ∫ ω, ψ ω ^ 2 ∂P) := by
  unfold pearsonCorr
  rw [var_eq hφ, var_eq hψ, hφ.2, hψ.2]
  simp

lemma bdd (m₁ m₂ : MeasurableSpace Ω) :
    BddAbove {r : ℝ | ∃ φ ψ : Ω → ℝ, InCentered P m₁ φ ∧ InCentered P m₂ ψ ∧
      0 < variance φ P ∧ 0 < variance ψ P ∧ r = pearsonCorr P φ ψ} := by
  refine ⟨1, ?_⟩
  rintro r ⟨φ, ψ, hφ, hψ, hvφ, hvψ, rfl⟩
  rw [pearson_eq hφ hψ]
  rw [var_eq hφ] at hvφ
  rw [var_eq hψ] at hvψ
  have hpos : 0 < Real.sqrt ((∫ ω, φ ω ^ 2 ∂P) * ∫ ω, ψ ω ^ 2 ∂P) :=
    Real.sqrt_pos.2 (mul_pos hvφ hvψ)
  rw [div_le_one hpos]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (cs hφ.1.2 hψ.1.2))

lemma inner_le {m₁ m₂ : MeasurableSpace Ω} {φ ψ : Ω → ℝ} (hφ : InCentered P m₁ φ)
    (hψ : InCentered P m₂ ψ) :
    ∫ ω, φ ω * ψ ω ∂P ≤ maximalCorrelation P m₁ m₂ * Real.sqrt (∫ ω, φ ω ^ 2 ∂P) *
      Real.sqrt (∫ ω, ψ ω ^ 2 ∂P) := by
  have hA : 0 ≤ ∫ ω, φ ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  have hB : 0 ≤ ∫ ω, ψ ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
  rcases hA.lt_or_eq with hA | hA
  · rcases hB.lt_or_eq with hB | hB
    · have hmem : pearsonCorr P φ ψ ∈ {r : ℝ | ∃ φ ψ : Ω → ℝ, InCentered P m₁ φ ∧
          InCentered P m₂ ψ ∧ 0 < variance φ P ∧ 0 < variance ψ P ∧
          r = pearsonCorr P φ ψ} :=
        ⟨φ, ψ, hφ, hψ, by rw [var_eq hφ]; exact hA, by rw [var_eq hψ]; exact hB, rfl⟩
      have hle := le_csSup (bdd (P := P) m₁ m₂) hmem
      have hpos : 0 < Real.sqrt ((∫ ω, φ ω ^ 2 ∂P) * ∫ ω, ψ ω ^ 2 ∂P) :=
        Real.sqrt_pos.2 (mul_pos hA hB)
      rw [pearson_eq hφ hψ, div_le_iff₀ hpos, Real.sqrt_mul hA.le] at hle
      unfold maximalCorrelation
      linarith
    · have h0 := ae_zero_of_sq hψ.1.2 hB.symm
      have : ∫ ω, φ ω * ψ ω ∂P = 0 := by
        rw [integral_congr_ae (g := fun _ => (0:ℝ))]
        · simp
        · filter_upwards [h0] with ω hω; simp [hω]
      rw [this, ← hB]; simp
  · have h0 := ae_zero_of_sq hφ.1.2 hA.symm
    have : ∫ ω, φ ω * ψ ω ∂P = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      · filter_upwards [h0] with ω hω; simp [hω]
    rw [this, ← hA]; simp

lemma centered_condExp {m₁ m₂ : MeasurableSpace Ω} (hm₂ : m₂ ≤ mΩ) {φ : Ω → ℝ}
    (hφ : InCentered P m₁ φ) : InCentered P m₂ (P[φ|m₂]) :=
  ⟨⟨stronglyMeasurable_condExp, memLp_condExp hφ.1.2⟩, by rw [integral_condExp hm₂]; exact hφ.2⟩

lemma ec28 {m₁ m₂ : MeasurableSpace Ω} (hm₂ : m₂ ≤ mΩ) {φ : Ω → ℝ}
    (hφ : InCentered P m₁ φ) :
    ∫ ω, (P[φ|m₂]) ω ^ 2 ∂P ≤ (max (maximalCorrelation P m₁ m₂) 0) ^ 2 * ∫ ω, φ ω ^ 2 ∂P := by
  set r := maximalCorrelation P m₁ m₂
  have hψ := centered_condExp hm₂ hφ
  have h := inner_le hφ hψ
  rw [← sq_condExp_eq hm₂ hφ.1.2] at h
  set B := ∫ ω, (P[φ|m₂]) ω ^ 2 ∂P
  set A := ∫ ω, φ ω ^ 2 ∂P
  have hA : 0 ≤ A := integral_nonneg (fun ω => sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun ω => sq_nonneg _)
  rcases hB.lt_or_eq with hB | hB
  · have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
    have e : B = Real.sqrt B ^ 2 := (Real.sq_sqrt hB.le).symm
    have h1 : Real.sqrt B ≤ r * Real.sqrt A := by
      have : Real.sqrt B * Real.sqrt B ≤ (r * Real.sqrt A) * Real.sqrt B := by
        nlinarith
      exact le_of_mul_le_mul_right this hsB
    have h2 : Real.sqrt B ≤ max r 0 * Real.sqrt A :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
    have h3 : Real.sqrt B ^ 2 ≤ (max r 0 * Real.sqrt A) ^ 2 :=
      pow_le_pow_left₀ hsB.le h2 2
    rw [mul_pow, Real.sq_sqrt hA] at h3
    linarith
  · rw [← hB]; positivity

lemma condExp_zero_of_orth {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P)
    (hf0 : ∫ ω, f ω ∂P = 0) (h : ∀ φ, InCentered P m φ → ∫ ω, f ω * φ ω ∂P = 0) :
    P[f|m] =ᵐ[P] 0 := by
  have hc : InCentered P m (P[f|m]) :=
    ⟨⟨stronglyMeasurable_condExp, memLp_condExp hf⟩, by rw [integral_condExp hm]; exact hf0⟩
  have h1 := h _ hc
  rw [← sq_condExp_eq hm hf] at h1
  exact ae_zero_of_sq (memLp_condExp hf) h1

lemma orth_of_condExp_zero {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P)
    (h : P[f|m] =ᵐ[P] 0) : ∀ φ, InCentered P m φ → ∫ ω, f ω * φ ω ∂P = 0 := by
  intro φ hφ
  rw [tower hm hf hφ.1.2 hφ.1.1, integral_congr_ae (g := fun _ => (0:ℝ))]
  · simp
  · filter_upwards [h] with ω hω; simp [hω]

lemma quad_zero {B C : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * C + t ^ 2 * B) : C = 0 := by
  set s := |B| + 1 with hs
  have hs0 : 0 < s := by positivity
  have h1 := h (-C / s)
  have e : 2 * (-C / s) * C + (-C / s) ^ 2 * B = C ^ 2 * (B - 2 * s) / s ^ 2 := by
    field_simp; ring
  rw [e, le_div_iff₀ (by positivity), zero_mul] at h1
  have hB : B - 2 * s ≤ -1 := by
    rw [hs]; have := le_abs_self B; have := abs_nonneg B; linarith
  have : C ^ 2 ≤ 0 := by nlinarith [sq_nonneg C]
  nlinarith [sq_nonneg C]

end CHAux


open MeasureTheory ProbabilityTheory CustomHedge.Exist

namespace CHAux

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

section
variable (M : Market Ω EX EY EI)

noncomputable def K0 : Ω → ℝ := fun ω => M.K ω - ∫ ω', M.K ω' ∂M.P
noncomputable def J (W : Ω → ℝ) : ℝ := ∫ ω, (K0 M ω + W ω) ^ 2 ∂M.P
noncomputable def cen (H : Ω → ℝ) : Ω → ℝ := fun ω => H ω - ∫ ω', H ω' ∂M.P

end

variable {M : Market Ω EX EY EI} (hS : M.Standing)
include hS

lemma hFX : M.FX ≤ ‹MeasurableSpace Ω› := hS.2.1.comap_le
lemma hFI : M.FI ≤ ‹MeasurableSpace Ω› := hS.2.2.2.1.comap_le
lemma memPos : MemLp M.pos 2 M.P := hS.2.2.2.2.2.1
lemma memD : MemLp M.D 2 M.P := hS.2.2.2.2.2.2.2.2.2.1
lemma intD : ∫ ω, M.D ω ∂M.P = 1 := hS.2.2.2.2.2.2.2.2.1
lemma apos : 0 < M.a := hS.2.2.2.2.2.2.2.2.2.2.2

lemma memK : MemLp M.K 2 M.P := (memPos hS).add ((memD hS).const_mul _)

omit hS in
lemma memLp_const' [IsProbabilityMeasure M.P] (c : ℝ) : MemLp (fun _ : Ω => c) 2 M.P :=
  memLp_const c

lemma memK0 [IsProbabilityMeasure M.P] : MemLp (K0 M) 2 M.P :=
  (memK hS).sub (memLp_const _)

lemma intK0 [IsProbabilityMeasure M.P] : ∫ ω, K0 M ω ∂M.P = 0 := by
  unfold K0
  rw [integral_sub ((memK hS).integrable one_le_two) (integrable_const _)]
  simp

omit hS in
lemma cen_memLp [IsProbabilityMeasure M.P] {H : Ω → ℝ} (hH : MemLp H 2 M.P) :
    MemLp (cen M H) 2 M.P := hH.sub (memLp_const _)

omit hS in
lemma cen_int [IsProbabilityMeasure M.P] {H : Ω → ℝ} (hH : MemLp H 2 M.P) :
    ∫ ω, cen M H ω ∂M.P = 0 := by
  unfold cen
  rw [integral_sub (hH.integrable one_le_two) (integrable_const _)]
  simp

omit hS in
lemma cen_centeredX [IsProbabilityMeasure M.P] {H : Ω → ℝ}
    (hH : InClaims M.P M.FX H) : InCentered M.P M.FX (cen M H) :=
  ⟨⟨hH.1.sub stronglyMeasurable_const, cen_memLp hH.2⟩, cen_int hH.2⟩

omit hS in
lemma cen_centeredI [IsProbabilityMeasure M.P] {H : Ω → ℝ}
    (hH : InClaims M.P M.FI H) : InCentered M.P M.FI (cen M H) :=
  ⟨⟨hH.1.sub stronglyMeasurable_const, cen_memLp hH.2⟩, cen_int hH.2⟩


section
variable (M) in
noncomputable def C0 : ℝ :=
  M.rho * ∫ ω, M.pos ω ∂M.P
    + M.rho * ∫ ω, (M.pos ω - ∫ ω', M.pos ω' ∂M.P) * (M.D ω - 1) ∂M.P
    + M.rho * (M.rho / M.a) / 2 * ∫ ω, (M.D ω - 1) ^ 2 ∂M.P
end

lemma cen_D [IsProbabilityMeasure M.P] {H : Ω → ℝ} (hH : MemLp H 2 M.P) (hQ : M.EQ H = 0) :
    ∫ ω, cen M H ω * (M.D ω - 1) ∂M.P = -∫ ω, H ω ∂M.P := by
  unfold Market.EQ at hQ
  unfold cen
  set EH := ∫ ω, H ω ∂M.P
  have e : (fun ω => (H ω - EH) * (M.D ω - 1)) =
      fun ω => ((H ω * M.D ω - H ω) - EH * M.D ω) + EH := by funext ω; ring
  have i1 : Integrable (fun ω => H ω * M.D ω) M.P := int_mul hH (memD hS)
  have i2 : Integrable H M.P := hH.integrable one_le_two
  have i3 : Integrable (fun ω => EH * M.D ω) M.P := ((memD hS).integrable one_le_two).const_mul _
  rw [e, integral_add, integral_sub, integral_sub, integral_const_mul, hQ, intD hS]
  · simp; rfl
  all_goals (first | exact i1 | exact i2 | exact i3 | exact (i1.sub i2) | exact (i1.sub i2).sub i3 | exact integrable_const _)

lemma U_eq [IsProbabilityMeasure M.P] {H G : Ω → ℝ} (hF : M.Feasible H G) :
    M.U (M.pos + H + G) = C0 M - M.a / 2 * J M (cen M H + cen M G) := by
  obtain ⟨hH, hG, hQH, hQG⟩ := hF
  have hH2 := hH.2
  have hG2 := hG.2
  have hp := memPos hS
  have hD := memD hS
  obtain ⟨k, hk⟩ : ∃ k, k = M.rho / M.a := ⟨_, rfl⟩
  have hak : M.a * k = M.rho := by rw [hk]; field_simp [(apos hS).ne']
  unfold C0
  rw [← hk]
  set Ep := ∫ ω, M.pos ω ∂M.P
  set EH := ∫ ω, H ω ∂M.P
  set EG := ∫ ω, G ω ∂M.P
  have hEZ : ∫ ω, (M.pos + H + G) ω ∂M.P = Ep + EH + EG := by
    simp only [Pi.add_apply]
    rw [integral_add, integral_add]
    all_goals (first | exact hp.integrable one_le_two | exact hH2.integrable one_le_two | exact hG2.integrable one_le_two | exact (hp.integrable one_le_two).add (hH2.integrable one_le_two))
  have hZ : MemLp (M.pos + H + G) 2 M.P := (hp.add hH2).add hG2
  have hVar : variance (M.pos + H + G) M.P =
      ∫ ω, (M.pos ω + H ω + G ω - (Ep + EH + EG)) ^ 2 ∂M.P := by
    rw [variance_eq_integral hZ.1.aemeasurable, hEZ]
    simp only [Pi.add_apply]
  have hEK : ∫ ω, M.K ω ∂M.P = Ep + k := by
    unfold Market.K
    rw [integral_add (hp.integrable one_le_two) ((hD.integrable one_le_two).const_mul _),
      integral_const_mul, intD hS, mul_one, hk]
  -- the pieces
  set Zc : Ω → ℝ := fun ω => M.pos ω + H ω + G ω - (Ep + EH + EG)
  set p0 : Ω → ℝ := fun ω => M.pos ω - Ep
  set d : Ω → ℝ := fun ω => M.D ω - 1
  have mZc : MemLp Zc 2 M.P := hZ.sub (memLp_const _)
  have mp0 : MemLp p0 2 M.P := hp.sub (memLp_const _)
  have md : MemLp d 2 M.P := hD.sub (memLp_const _)
  have mcH : MemLp (cen M H) 2 M.P := cen_memLp hH2
  have mcG : MemLp (cen M G) 2 M.P := cen_memLp hG2
  have e : (fun ω => (K0 M ω + (cen M H + cen M G) ω) ^ 2) =
      fun ω => Zc ω ^ 2 + (2 * k) * (p0 ω * d ω) + (2 * k) * (cen M H ω * d ω)
        + (2 * k) * (cen M G ω * d ω) + k ^ 2 * d ω ^ 2 := by
    funext ω
    simp only [K0, cen, Pi.add_apply, Zc, p0, d]
    rw [hEK]
    simp only [Market.K]
    rw [← hk]
    ring
  have i1 := mZc.integrable_sq
  have i2 := (int_mul mp0 md).const_mul (2 * k)
  have i3 := (int_mul mcH md).const_mul (2 * k)
  have i4 := (int_mul mcG md).const_mul (2 * k)
  have i5 := md.integrable_sq.const_mul (k ^ 2)
  have hJ : J M (cen M H + cen M G) = ∫ ω, Zc ω ^ 2 ∂M.P
      + (2 * k) * ∫ ω, p0 ω * d ω ∂M.P + (2 * k) * (-EH) + (2 * k) * (-EG)
      + k ^ 2 * ∫ ω, d ω ^ 2 ∂M.P := by
    unfold J
    rw [e, integral_add, integral_add, integral_add, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, cen_D hS hH2 hQH,
      cen_D hS hG2 hQG]
    all_goals (first | exact i1 | exact i2 | exact i3 | exact i4 | exact i5 | exact i1.add i2 | exact (i1.add i2).add i3 | exact ((i1.add i2).add i3).add i4)
  have hU : M.U (M.pos + H + G) = M.rho * (Ep + EH + EG) - M.a / 2 * ∫ ω, Zc ω ^ 2 ∂M.P := by
    unfold Market.U
    rw [hEZ, hVar]
  rw [hU, hJ]
  linear_combination ((∫ ω, p0 ω * d ω ∂M.P - EH - EG) + k / 2 * ∫ ω, d ω ^ 2 ∂M.P) * hak

lemma liftX [IsProbabilityMeasure M.P] {H₀ : Ω → ℝ} (h : InCentered M.P M.FX H₀) :
    InClaims M.P M.FX (fun ω => H₀ ω - M.EQ H₀) ∧ M.EQ (fun ω => H₀ ω - M.EQ H₀) = 0 ∧
      cen M (fun ω => H₀ ω - M.EQ H₀) = H₀ := by
  refine ⟨⟨h.1.1.sub stronglyMeasurable_const, h.1.2.sub (memLp_const _)⟩, ?_, ?_⟩
  · unfold Market.EQ
    have e : (fun ω => (H₀ ω - ∫ ω', H₀ ω' * M.D ω' ∂M.P) * M.D ω) =
        fun ω => H₀ ω * M.D ω - (∫ ω', H₀ ω' * M.D ω' ∂M.P) * M.D ω := by funext ω; ring
    rw [e, integral_sub (int_mul h.1.2 (memD hS)) (((memD hS).integrable one_le_two).const_mul _),
      integral_const_mul, intD hS]
    ring
  · funext ω
    unfold cen
    rw [integral_sub (h.1.2.integrable one_le_two) (integrable_const _), h.2]
    simp

lemma liftI [IsProbabilityMeasure M.P] {H₀ : Ω → ℝ} (h : InCentered M.P M.FI H₀) :
    InClaims M.P M.FI (fun ω => H₀ ω - M.EQ H₀) ∧ M.EQ (fun ω => H₀ ω - M.EQ H₀) = 0 ∧
      cen M (fun ω => H₀ ω - M.EQ H₀) = H₀ := by
  refine ⟨⟨h.1.1.sub stronglyMeasurable_const, h.1.2.sub (memLp_const _)⟩, ?_, ?_⟩
  · unfold Market.EQ
    have e : (fun ω => (H₀ ω - ∫ ω', H₀ ω' * M.D ω' ∂M.P) * M.D ω) =
        fun ω => H₀ ω * M.D ω - (∫ ω', H₀ ω' * M.D ω' ∂M.P) * M.D ω := by funext ω; ring
    rw [e, integral_sub (int_mul h.1.2 (memD hS)) (((memD hS).integrable one_le_two).const_mul _),
      integral_const_mul, intD hS]
    ring
  · funext ω
    unfold cen
    rw [integral_sub (h.1.2.integrable one_le_two) (integrable_const _), h.2]
    simp

section
variable (M) in
/-- minimality of `W` for `J` over `ℍ_X + ℍ_I`. -/
def IsMin (W : Ω → ℝ) : Prop :=
  ∀ H₀ G₀, InCentered M.P M.FX H₀ → InCentered M.P M.FI G₀ → J M W ≤ J M (H₀ + G₀)
end

lemma opt_min [IsProbabilityMeasure M.P] {H G : Ω → ℝ} (hO : M.IsOptimal H G) :
    IsMin M (cen M H + cen M G) := by
  intro H₀ G₀ hX hI
  obtain ⟨a1, a2, a3⟩ := liftX hS hX
  obtain ⟨b1, b2, b3⟩ := liftI hS hI
  have hF' : M.Feasible (fun ω => H₀ ω - M.EQ H₀) (fun ω => G₀ ω - M.EQ G₀) := ⟨a1, b1, a2, b2⟩
  have h := hO.2 _ _ hF'
  rw [U_eq hS hF', U_eq hS hO.1, a3, b3] at h
  have := apos hS
  nlinarith

lemma min_opt [IsProbabilityMeasure M.P] {H G : Ω → ℝ} (hF : M.Feasible H G)
    (hm : IsMin M (cen M H + cen M G)) : M.IsOptimal H G := by
  refine ⟨hF, fun H' G' hF' => ?_⟩
  rw [U_eq hS hF', U_eq hS hF]
  have := hm _ _ (cen_centeredX hF'.1) (cen_centeredI hF'.2.1)
  have := apos hS
  nlinarith

lemma J_expand [IsProbabilityMeasure M.P] {W h : Ω → ℝ} (hW : MemLp W 2 M.P)
    (hh : MemLp h 2 M.P) (t : ℝ) :
    J M (fun ω => W ω + t * h ω) = J M W + 2 * t * ∫ ω, (K0 M ω + W ω) * h ω ∂M.P
      + t ^ 2 * ∫ ω, h ω ^ 2 ∂M.P := by
  unfold J
  have e : (fun ω => (K0 M ω + (W ω + t * h ω)) ^ 2) =
      fun ω => ((K0 M ω + W ω) + t * h ω) ^ 2 := by funext ω; ring
  rw [e]
  exact expand ((memK0 hS).add hW) hh t

lemma min_orthX [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) (hm : IsMin M (H₀ + G₀)) :
    ∀ φ, InCentered M.P M.FX φ → ∫ ω, (K0 M ω + (H₀ + G₀) ω) * φ ω ∂M.P = 0 := by
  intro φ hφ
  apply quad_zero (B := ∫ ω, φ ω ^ 2 ∂M.P)
  intro t
  have hc : InCentered M.P M.FX (fun ω => H₀ ω + t * φ ω) := by
    refine ⟨⟨hX.1.1.add (stronglyMeasurable_const.mul hφ.1.1), hX.1.2.add (hφ.1.2.const_mul t)⟩, ?_⟩
    rw [integral_add (hX.1.2.integrable one_le_two) ((hφ.1.2.integrable one_le_two).const_mul t),
      integral_const_mul, hX.2, hφ.2]
    simp
  have h := hm _ _ hc hI
  have e : ((fun ω => H₀ ω + t * φ ω) + G₀) = fun ω => (H₀ + G₀) ω + t * φ ω := by
    funext ω; simp only [Pi.add_apply]; ring
  rw [e, J_expand hS (hX.1.2.add hI.1.2) hφ.1.2] at h
  linarith

lemma min_orthI [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) (hm : IsMin M (H₀ + G₀)) :
    ∀ φ, InCentered M.P M.FI φ → ∫ ω, (K0 M ω + (H₀ + G₀) ω) * φ ω ∂M.P = 0 := by
  intro φ hφ
  apply quad_zero (B := ∫ ω, φ ω ^ 2 ∂M.P)
  intro t
  have hc : InCentered M.P M.FI (fun ω => G₀ ω + t * φ ω) := by
    refine ⟨⟨hI.1.1.add (stronglyMeasurable_const.mul hφ.1.1), hI.1.2.add (hφ.1.2.const_mul t)⟩, ?_⟩
    rw [integral_add (hI.1.2.integrable one_le_two) ((hφ.1.2.integrable one_le_two).const_mul t),
      integral_const_mul, hI.2, hφ.2]
    simp
  have h := hm _ _ hX hc
  have e : (H₀ + fun ω => G₀ ω + t * φ ω) = fun ω => (H₀ + G₀) ω + t * φ ω := by
    funext ω; simp only [Pi.add_apply]; ring
  rw [e, J_expand hS (hX.1.2.add hI.1.2) hφ.1.2] at h
  linarith

/-- if `K0 + W` is orthogonal to `ℍ_X` and `ℍ_I`, then `J W' = J W + ‖W' - W‖²`. -/
lemma J_orth [IsProbabilityMeasure M.P] {H₀ G₀ H₁ G₁ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) (hX1 : InCentered M.P M.FX H₁) (hI1 : InCentered M.P M.FI G₁)
    (oX : ∀ φ, InCentered M.P M.FX φ → ∫ ω, (K0 M ω + (H₀ + G₀) ω) * φ ω ∂M.P = 0)
    (oI : ∀ φ, InCentered M.P M.FI φ → ∫ ω, (K0 M ω + (H₀ + G₀) ω) * φ ω ∂M.P = 0) :
    J M (H₁ + G₁) = J M (H₀ + G₀) + ∫ ω, ((H₁ + G₁) ω - (H₀ + G₀) ω) ^ 2 ∂M.P := by
  have mW := hX.1.2.add hI.1.2
  have mW1 := hX1.1.2.add hI1.1.2
  have e : (H₁ + G₁) = fun ω => (H₀ + G₀) ω + 1 * ((H₁ + G₁) ω - (H₀ + G₀) ω) := by
    funext ω; ring
  have dX : InCentered M.P M.FX (fun ω => H₁ ω - H₀ ω) := by
    refine ⟨⟨hX1.1.1.sub hX.1.1, hX1.1.2.sub hX.1.2⟩, ?_⟩
    rw [integral_sub (hX1.1.2.integrable one_le_two) (hX.1.2.integrable one_le_two), hX1.2, hX.2]
    simp
  have dI : InCentered M.P M.FI (fun ω => G₁ ω - G₀ ω) := by
    refine ⟨⟨hI1.1.1.sub hI.1.1, hI1.1.2.sub hI.1.2⟩, ?_⟩
    rw [integral_sub (hI1.1.2.integrable one_le_two) (hI.1.2.integrable one_le_two), hI1.2, hI.2]
    simp
  have hzero : ∫ ω, (K0 M ω + (H₀ + G₀) ω) * ((H₁ + G₁) ω - (H₀ + G₀) ω) ∂M.P = 0 := by
    have e2 : (fun ω => (K0 M ω + (H₀ + G₀) ω) * ((H₁ + G₁) ω - (H₀ + G₀) ω)) =
        fun ω => (K0 M ω + (H₀ + G₀) ω) * (H₁ ω - H₀ ω) +
          (K0 M ω + (H₀ + G₀) ω) * (G₁ ω - G₀ ω) := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [e2, integral_add, oX _ dX, oI _ dI]
    · simp
    · exact int_mul ((memK0 hS).add mW) dX.1.2
    · exact int_mul ((memK0 hS).add mW) dI.1.2
  conv_lhs => rw [e]
  rw [J_expand hS (h := fun ω => (H₁ + G₁) ω - (H₀ + G₀) ω) mW (by exact mW1.sub mW), hzero]
  simp

end CHAux


open MeasureTheory ProbabilityTheory CustomHedge.Exist

namespace CHAux

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

variable {M : Market Ω EX EY EI} (hS : M.Standing)
include hS

/-- `Π^X_0 = -E[K₀|𝓕_X] + E[E[K₀|𝓕_I]|𝓕_X]` a.s. -/
lemma Pi0X_ae [IsProbabilityMeasure M.P] :
    M.Pi0X =ᵐ[M.P] -M.P[K0 M|M.FX] + M.P[M.P[K0 M|M.FI]|M.FX] := by
  set c := ∫ ω', M.K ω' ∂M.P
  have eK : M.K = K0 M + fun _ => c := by funext ω; simp [K0, c]
  have iK0 : Integrable (K0 M) M.P := (memK0 hS).integrable one_le_two
  have h1 : M.P[M.K|M.FI] =ᵐ[M.P] M.P[K0 M|M.FI] + fun _ => c := by
    rw [eK]
    have := condExp_add (m := M.FI) iK0 (integrable_const c)
    rwa [condExp_const (hFI hS)] at this
  have h2 : M.K - M.P[M.K|M.FI] =ᵐ[M.P] K0 M - M.P[K0 M|M.FI] := by
    filter_upwards [h1] with ω hω
    simp only [Pi.sub_apply, hω, Pi.add_apply]
    rw [eK]; simp only [Pi.add_apply]; ring
  have h3 := condExp_congr_ae (m := M.FX) h2
  have h4 := condExp_sub (m := M.FX) iK0 (integrable_condExp (m := M.FI) (f := K0 M)) (μ := M.P)
  unfold Market.Pi0X
  filter_upwards [h3, h4] with ω h3 h4
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at h3 h4 ⊢
  rw [h3, h4]; ring

/-- First-order system ⇒ fixed-point equation (7). -/
lemma foc_fixed [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) (fX : M.P[K0 M + (H₀ + G₀)|M.FX] =ᵐ[M.P] 0)
    (fI : M.P[K0 M + (H₀ + G₀)|M.FI] =ᵐ[M.P] 0) : H₀ =ᵐ[M.P] M.Pi0X + M.T H₀ := by
  have iK0 : Integrable (K0 M) M.P := (memK0 hS).integrable one_le_two
  have iH : Integrable H₀ M.P := hX.1.2.integrable one_le_two
  have iG : Integrable G₀ M.P := hI.1.2.integrable one_le_two
  have a1 := condExp_add (m := M.FX) iK0 (iH.add iG)
  have a2 := condExp_add (m := M.FX) iH iG
  have a3 : M.P[H₀|M.FX] = H₀ := condExp_of_stronglyMeasurable (hFX hS) hX.1.1 iH
  have b1 := condExp_add (m := M.FI) iK0 (iH.add iG)
  have b2 := condExp_add (m := M.FI) iH iG
  have b3 : M.P[G₀|M.FI] = G₀ := condExp_of_stronglyMeasurable (hFI hS) hI.1.1 iG
  have e1 : M.P[H₀|M.FI] =ᵐ[M.P] -M.P[K0 M|M.FI] - G₀ := by
    filter_upwards [fI, b1, b2] with ω h0 h1 h2
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply, Pi.sub_apply] at h0 h1 h2 ⊢
    rw [b3] at h2
    linarith
  have c1 := condExp_congr_ae (m := M.FX) e1
  have c2 := condExp_sub (m := M.FX) (integrable_condExp (m := M.FI) (f := K0 M)).neg iG
    (μ := M.P)
  have c3 := condExp_neg (m := M.FX) (μ := M.P) (M.P[K0 M|M.FI])
  have d := Pi0X_ae hS
  unfold Market.T
  filter_upwards [fX, a1, a2, c1, c2, c3, d] with ω h0 h1 h2 h3 h4 h5 h6
  simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply, Pi.sub_apply] at h0 h1 h2 h3 h4 h5 h6 ⊢
  rw [a3] at h2
  rw [h6, h3, h4, h5]
  linarith

/-- fixed point ⇒ first-order system for `G₀ = -E[K₀|𝓕_I] - E[H₀|𝓕_I]`. -/
lemma fixed_foc [IsProbabilityMeasure M.P] {H₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hfix : H₀ =ᵐ[M.P] M.Pi0X + M.T H₀) :
    InCentered M.P M.FI (-M.P[K0 M|M.FI] - M.P[H₀|M.FI]) ∧
    M.P[K0 M + (H₀ + (-M.P[K0 M|M.FI] - M.P[H₀|M.FI]))|M.FX] =ᵐ[M.P] 0 ∧
    M.P[K0 M + (H₀ + (-M.P[K0 M|M.FI] - M.P[H₀|M.FI]))|M.FI] =ᵐ[M.P] 0 := by
  set G₀ := -M.P[K0 M|M.FI] - M.P[H₀|M.FI] with hG₀
  have iK0 : Integrable (K0 M) M.P := (memK0 hS).integrable one_le_two
  have iH : Integrable H₀ M.P := hX.1.2.integrable one_le_two
  have hI : InCentered M.P M.FI G₀ := by
    refine ⟨⟨stronglyMeasurable_condExp.neg.sub stronglyMeasurable_condExp,
      ((memLp_condExp (memK0 hS)).neg).sub (memLp_condExp hX.1.2)⟩, ?_⟩
    show ∫ ω, (-M.P[K0 M|M.FI] ω - M.P[H₀|M.FI] ω) ∂M.P = 0
    rw [integral_sub, integral_neg,
      integral_condExp (hFI hS), integral_condExp (hFI hS), intK0 hS, hX.2]
    · simp
    · exact integrable_condExp.neg
    · exact integrable_condExp
  have iG : Integrable G₀ M.P := hI.1.2.integrable one_le_two
  refine ⟨hI, ?_, ?_⟩
  · have a1 := condExp_add (m := M.FX) iK0 (iH.add iG)
    have a2 := condExp_add (m := M.FX) iH iG
    have a3 : M.P[H₀|M.FX] = H₀ := condExp_of_stronglyMeasurable (hFX hS) hX.1.1 iH
    have c2 := condExp_sub (m := M.FX) (integrable_condExp (m := M.FI) (f := K0 M)).neg
      (integrable_condExp (m := M.FI) (f := H₀)) (μ := M.P)
    have c3 := condExp_neg (m := M.FX) (μ := M.P) (M.P[K0 M|M.FI])
    have d := Pi0X_ae hS
    filter_upwards [a1, a2, c2, c3, d, hfix] with ω h1 h2 h4 h5 h6 h7
    rw [hG₀] at h1 h2
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply, Pi.sub_apply, Market.T] at h1 h2 h4 h5 h6 h7 ⊢
    rw [a3] at h2
    rw [h1, h2, h4, h5]
    rw [h6] at h7
    linarith
  · have b1 := condExp_add (m := M.FI) iK0 (iH.add iG)
    have b2 := condExp_add (m := M.FI) iH iG
    have b3 : M.P[G₀|M.FI] = G₀ := condExp_of_stronglyMeasurable (hFI hS) hI.1.1 iG
    filter_upwards [b1, b2] with ω h1 h2
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2, b3, hG₀]
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring

lemma memW [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) : MemLp (K0 M + (H₀ + G₀)) 2 M.P :=
  (memK0 hS).add (hX.1.2.add hI.1.2)

lemma intW [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) : ∫ ω, (K0 M + (H₀ + G₀)) ω ∂M.P = 0 := by
  simp only [Pi.add_apply]
  rw [integral_add, integral_add, intK0 hS, hX.2, hI.2]
  · simp
  · exact hX.1.2.integrable one_le_two
  · exact hI.1.2.integrable one_le_two
  · exact (memK0 hS).integrable one_le_two
  · exact (hX.1.2.add hI.1.2).integrable one_le_two

lemma min_foc [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) (hm : IsMin M (H₀ + G₀)) :
    M.P[K0 M + (H₀ + G₀)|M.FX] =ᵐ[M.P] 0 ∧ M.P[K0 M + (H₀ + G₀)|M.FI] =ᵐ[M.P] 0 :=
  ⟨condExp_zero_of_orth (hFX hS) (memW hS hX hI) (intW hS hX hI)
      (fun φ hφ => min_orthX hS hX hI hm φ hφ),
    condExp_zero_of_orth (hFI hS) (memW hS hX hI) (intW hS hX hI)
      (fun φ hφ => min_orthI hS hX hI hm φ hφ)⟩

lemma part3 [IsProbabilityMeasure M.P] {H G : Ω → ℝ} (hO : M.IsOptimal H G) :
    cen M H =ᵐ[M.P] M.Pi0X + M.T (cen M H) := by
  have hX := cen_centeredX hO.1.1
  have hI := cen_centeredI hO.1.2.1
  obtain ⟨f1, f2⟩ := min_foc hS hX hI (opt_min hS hO)
  exact foc_fixed hS hX hI f1 f2

lemma exists_opt [IsProbabilityMeasure M.P] {H₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hfix : H₀ =ᵐ[M.P] M.Pi0X + M.T H₀) : ∃ H G, M.IsOptimal H G := by
  obtain ⟨hI, f1, f2⟩ := fixed_foc hS hX hfix
  set G₀ := -M.P[K0 M|M.FI] - M.P[H₀|M.FI]
  have oX := orth_of_condExp_zero (hFX hS) (memW hS hX hI) f1
  have oI := orth_of_condExp_zero (hFI hS) (memW hS hX hI) f2
  obtain ⟨a1, a2, a3⟩ := liftX hS hX
  obtain ⟨b1, b2, b3⟩ := liftI hS hI
  refine ⟨_, _, min_opt hS ⟨a1, b1, a2, b2⟩ ?_⟩
  rw [a3, b3]
  intro H₁ G₁ hX1 hI1
  rw [J_orth hS hX hI hX1 hI1 (fun φ hφ => oX φ hφ) (fun φ hφ => oI φ hφ)]
  have : 0 ≤ ∫ ω, ((H₁ + G₁) ω - (H₀ + G₀) ω) ^ 2 ∂M.P := integral_nonneg (fun ω => sq_nonneg _)
  linarith

omit hS in
lemma ae_eq_of_cen [IsProbabilityMeasure M.P] (hS : M.Standing) {H₁ H₂ : Ω → ℝ}
    (h1 : MemLp H₁ 2 M.P) (h2 : MemLp H₂ 2 M.P)
    (q1 : M.EQ H₁ = 0) (q2 : M.EQ H₂ = 0) (hc : cen M H₁ =ᵐ[M.P] cen M H₂) :
    H₁ =ᵐ[M.P] H₂ := by
  set c := ∫ ω, H₁ ω ∂M.P - ∫ ω, H₂ ω ∂M.P
  have hd : (fun ω => H₁ ω - H₂ ω) =ᵐ[M.P] fun _ => c := by
    filter_upwards [hc] with ω hω
    simp only [cen] at hω
    simp only [c]; linarith
  have hc0 : c = 0 := by
    unfold Market.EQ at q1 q2
    have e1 : ∫ ω, (H₁ ω - H₂ ω) * M.D ω ∂M.P = 0 := by
      have e : (fun ω => (H₁ ω - H₂ ω) * M.D ω) = fun ω => H₁ ω * M.D ω - H₂ ω * M.D ω := by
        funext ω; ring
      rw [e, integral_sub (int_mul h1 (memD hS)) (int_mul h2 (memD hS)), q1, q2]
      simp
    have e2 : ∫ ω, (H₁ ω - H₂ ω) * M.D ω ∂M.P = ∫ ω, c * M.D ω ∂M.P := by
      apply integral_congr_ae
      filter_upwards [hd] with ω hω
      rw [hω]
    rw [e2, integral_const_mul, intD hS, mul_one] at e1
    exact e1
  filter_upwards [hd] with ω hω
  rw [hc0] at hω
  linarith

lemma unique [IsProbabilityMeasure M.P] (hr : M.maxCorr < 1) {H₁ G₁ H₂ G₂ : Ω → ℝ}
    (hO1 : M.IsOptimal H₁ G₁) (hO2 : M.IsOptimal H₂ G₂) :
    H₁ =ᵐ[M.P] H₂ ∧ G₁ =ᵐ[M.P] G₂ := by
  have hX1 := cen_centeredX hO1.1.1
  have hI1 := cen_centeredI hO1.1.2.1
  have hX2 := cen_centeredX hO2.1.1
  have hI2 := cen_centeredI hO2.1.2.1
  have m1 := opt_min hS hO1
  have m2 := opt_min hS hO2
  have hJ := J_orth hS hX1 hI1 hX2 hI2 (fun φ hφ => min_orthX hS hX1 hI1 m1 φ hφ)
    (fun φ hφ => min_orthI hS hX1 hI1 m1 φ hφ)
  have l1 := m1 _ _ hX2 hI2
  have l2 := m2 _ _ hX1 hI1
  have hN : ∫ ω, ((cen M H₂ + cen M G₂) ω - (cen M H₁ + cen M G₁) ω) ^ 2 ∂M.P = 0 := by
    have : 0 ≤ ∫ ω, ((cen M H₂ + cen M G₂) ω - (cen M H₁ + cen M G₁) ω) ^ 2 ∂M.P :=
      integral_nonneg (fun ω => sq_nonneg _)
    linarith
  have hW := ae_zero_of_sq (f := fun ω => (cen M H₂ + cen M G₂) ω - (cen M H₁ + cen M G₁) ω)
    (by exact (hX2.1.2.add hI2.1.2).sub (hX1.1.2.add hI1.1.2)) hN
  -- Z := cen H₁ - cen H₂ ∈ ℍ_X, Z' := cen G₂ - cen G₁ ∈ ℍ_I, Z = Z' a.s.
  set Z := fun ω => cen M H₁ ω - cen M H₂ ω
  set Z' := fun ω => cen M G₂ ω - cen M G₁ ω
  have hZ : InCentered M.P M.FX Z := by
    refine ⟨⟨hX1.1.1.sub hX2.1.1, hX1.1.2.sub hX2.1.2⟩, ?_⟩
    rw [integral_sub (hX1.1.2.integrable one_le_two) (hX2.1.2.integrable one_le_two), hX1.2, hX2.2]
    simp
  have hZ' : InCentered M.P M.FI Z' := by
    refine ⟨⟨hI2.1.1.sub hI1.1.1, hI2.1.2.sub hI1.1.2⟩, ?_⟩
    rw [integral_sub (hI2.1.2.integrable one_le_two) (hI1.1.2.integrable one_le_two), hI2.2, hI1.2]
    simp
  have hZZ : Z =ᵐ[M.P] Z' := by
    filter_upwards [hW] with ω hω
    simp only [Pi.add_apply, Pi.zero_apply] at hω
    simp only [Z, Z']; linarith
  have hc : M.P[Z|M.FI] =ᵐ[M.P] Z' := by
    rw [← condExp_of_stronglyMeasurable (hFI hS) hZ'.1.1 (hZ'.1.2.integrable one_le_two)]
    exact condExp_congr_ae hZZ
  have h28 := ec28 (hFI hS) hZ
  rw [sq_congr hc, sq_congr hZZ] at h28
  have hr0 : max M.maxCorr 0 < 1 := max_lt hr one_pos
  have hr1 : 0 ≤ max M.maxCorr 0 := le_max_right _ _
  have hsq : (max M.maxCorr 0) ^ 2 < 1 := by nlinarith
  have hN0 : 0 ≤ ∫ ω, Z' ω ^ 2 ∂M.P := integral_nonneg (fun ω => sq_nonneg _)
  have hN' : ∫ ω, Z' ω ^ 2 ∂M.P = 0 := by
    unfold Market.maxCorr at hsq
    nlinarith
  have hZ'0 := ae_zero_of_sq hZ'.1.2 hN'
  refine ⟨ae_eq_of_cen hS hO1.1.1.2 hO2.1.1.2 hO1.1.2.2.1 hO2.1.2.2.1 ?_,
    ae_eq_of_cen hS hO1.1.2.1.2 hO2.1.2.1.2 hO1.1.2.2.2 hO2.1.2.2.2 ?_⟩
  · filter_upwards [hZZ, hZ'0] with ω h1 h2
    simp only [Z, Z', Pi.zero_apply] at h1 h2
    linarith
  · filter_upwards [hZ'0] with ω h2
    simp only [Z', Pi.zero_apply] at h2
    linarith

end CHAux


open MeasureTheory ProbabilityTheory CustomHedge.Exist

namespace CHAux

section generic
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma norm_sq_Lp (w : Lp ℝ 2 P) : ‖w‖ ^ 2 = ∫ ω, w ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  congr 1; funext ω
  simp [sq]

lemma norm_sq_toLp {h : Ω → ℝ} (hh : MemLp h 2 P) : ‖hh.toLp h‖ ^ 2 = ∫ ω, h ω ^ 2 ∂P := by
  rw [norm_sq_Lp]
  exact sq_congr (MemLp.coeFn_toLp hh)

lemma centering_le {c : Ω → ℝ} (hc : MemLp c 2 P) :
    ∫ ω, (c ω - ∫ ω', c ω' ∂P) ^ 2 ∂P ≤ ∫ ω, c ω ^ 2 ∂P := by
  have h := expand hc (memLp_const (∫ ω', c ω' ∂P)) (-1)
  have e : (fun ω => (c ω + -1 * (∫ ω', c ω' ∂P)) ^ 2) = fun ω => (c ω - ∫ ω', c ω' ∂P) ^ 2 := by
    funext ω; ring
  rw [e] at h
  rw [h, integral_mul_const]
  simp
  nlinarith [sq_nonneg (∫ ω', c ω' ∂P)]

end generic

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

variable {M : Market Ω EX EY EI} (hS : M.Standing)
include hS

lemma memPi0X [IsProbabilityMeasure M.P] : MemLp M.Pi0X 2 M.P := by
  unfold Market.Pi0X
  exact (memLp_condExp ((memK hS).sub (memLp_condExp (memK hS)))).neg

omit hS in
lemma memT [IsProbabilityMeasure M.P] {u : Ω → ℝ} (hu : MemLp u 2 M.P) : MemLp (M.T u) 2 M.P :=
  memLp_condExp (memLp_condExp hu)

lemma intPi0X [IsProbabilityMeasure M.P] : ∫ ω, M.Pi0X ω ∂M.P = 0 := by
  unfold Market.Pi0X
  simp only [Pi.neg_apply]
  rw [integral_neg, integral_condExp (hFX hS)]
  simp only [Pi.sub_apply]
  rw [integral_sub ((memK hS).integrable one_le_two) integrable_condExp, integral_condExp (hFI hS)]
  simp

lemma intT [IsProbabilityMeasure M.P] (u : Ω → ℝ) : ∫ ω, M.T u ω ∂M.P = ∫ ω, u ω ∂M.P := by
  unfold Market.T
  rw [integral_condExp (hFX hS), integral_condExp (hFI hS)]

section
variable (M) in
noncomputable def gmap (z : Lp ℝ 2 M.P) : Ω → ℝ :=
  M.Pi0X + M.T (fun ω => M.P[⇑z|M.FX] ω - ∫ ω', z ω' ∂M.P)
end

lemma memg [IsProbabilityMeasure M.P] (z : Lp ℝ 2 M.P) : MemLp (gmap M z) 2 M.P :=
  (memPi0X hS).add (memT ((memLp_condExp (Lp.memLp z)).sub (memLp_const _)))

omit hS in
/-- `T` is linear a.e. -/
lemma T_sub [IsProbabilityMeasure M.P] {u v : Ω → ℝ} (hu : Integrable u M.P)
    (hv : Integrable v M.P) : M.T u - M.T v =ᵐ[M.P] M.T (u - v) := by
  unfold Market.T
  have h1 := condExp_sub (m := M.FX) (integrable_condExp (m := M.FI) (f := u))
    (integrable_condExp (m := M.FI) (f := v)) (μ := M.P)
  have h2 := condExp_congr_ae (m := M.FX) (condExp_sub (m := M.FI) hu hv (μ := M.P))
  exact h1.symm.trans h2.symm

lemma g_diff [IsProbabilityMeasure M.P] (z₁ z₂ : Lp ℝ 2 M.P) :
    gmap M z₁ - gmap M z₂ =ᵐ[M.P]
      M.T (fun ω => M.P[⇑(z₁ - z₂)|M.FX] ω - ∫ ω', (z₁ - z₂) ω' ∂M.P) := by
  have i1 := Lp.memLp z₁
  have i2 := Lp.memLp z₂
  have hu1 : Integrable (fun ω => M.P[⇑z₁|M.FX] ω - ∫ ω', z₁ ω' ∂M.P) M.P :=
    integrable_condExp.sub (integrable_const _)
  have hu2 : Integrable (fun ω => M.P[⇑z₂|M.FX] ω - ∫ ω', z₂ ω' ∂M.P) M.P :=
    integrable_condExp.sub (integrable_const _)
  have e0 : gmap M z₁ - gmap M z₂ = M.T (fun ω => M.P[⇑z₁|M.FX] ω - ∫ ω', z₁ ω' ∂M.P)
      - M.T (fun ω => M.P[⇑z₂|M.FX] ω - ∫ ω', z₂ ω' ∂M.P) := by
    funext ω; simp only [gmap, Pi.sub_apply, Pi.add_apply]; ring
  rw [e0]
  refine (T_sub hu1 hu2).trans ?_
  unfold Market.T
  apply condExp_congr_ae
  apply condExp_congr_ae
  have hc := condExp_sub (m := M.FX) (i1.integrable one_le_two) (i2.integrable one_le_two)
    (μ := M.P)
  have hc2 := condExp_congr_ae (m := M.FX) (Lp.coeFn_sub z₁ z₂) (μ := M.P)
  have hint : ∫ ω', (z₁ - z₂) ω' ∂M.P = ∫ ω', z₁ ω' ∂M.P - ∫ ω', z₂ ω' ∂M.P := by
    rw [integral_congr_ae (Lp.coeFn_sub z₁ z₂)]
    exact integral_sub (i1.integrable one_le_two) (i2.integrable one_le_two)
  filter_upwards [hc, hc2] with ω h1 h2
  simp only [Pi.sub_apply] at h1 h2 ⊢
  rw [h2, h1, hint]
  ring

lemma g_lip [IsProbabilityMeasure M.P] (z₁ z₂ : Lp ℝ 2 M.P) :
    dist ((memg hS z₁).toLp (gmap M z₁)) ((memg hS z₂).toLp (gmap M z₂)) ≤
      max M.maxCorr 0 * dist z₁ z₂ := by
  set w := z₁ - z₂
  set φ : Ω → ℝ := fun ω => M.P[⇑w|M.FX] ω - ∫ ω', w ω' ∂M.P
  have hφ : InCentered M.P M.FX φ := by
    refine ⟨⟨stronglyMeasurable_condExp.sub stronglyMeasurable_const,
      (memLp_condExp (Lp.memLp w)).sub (memLp_const _)⟩, ?_⟩
    rw [integral_sub integrable_condExp (integrable_const _), integral_condExp (hFX hS)]
    simp
  have hsq : dist ((memg hS z₁).toLp (gmap M z₁)) ((memg hS z₂).toLp (gmap M z₂)) ^ 2 ≤
      (max M.maxCorr 0) ^ 2 * dist z₁ z₂ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, norm_sq_toLp, sq_congr (g_diff hS z₁ z₂)]
    have a1 := sq_condExp_le (hFX hS) (memLp_condExp (m := M.FI) hφ.1.2)
    have a2 := ec28 (hFI hS) hφ
    have a3 := centering_le (memLp_condExp (m := M.FX) (Lp.memLp w))
    rw [integral_condExp (hFX hS)] at a3
    have a4 := sq_condExp_le (m := M.FX) (hFX hS) (Lp.memLp w)
    rw [← norm_sq_Lp] at a4
    unfold Market.T
    unfold Market.maxCorr
    have hr : 0 ≤ (max (maximalCorrelation M.P M.FX M.FI) 0) ^ 2 := sq_nonneg _
    calc _ ≤ _ := a1
      _ ≤ _ := a2
      _ ≤ _ := mul_le_mul_of_nonneg_left (a3.trans a4) hr
  have hr : 0 ≤ max M.maxCorr 0 := le_max_right _ _
  rw [← mul_pow] at hsq
  exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg hr dist_nonneg) two_ne_zero).1 hsq

lemma exists_fixed [IsProbabilityMeasure M.P] (hr : M.maxCorr < 1) :
    ∃ H₀, InCentered M.P M.FX H₀ ∧ H₀ =ᵐ[M.P] M.Pi0X + M.T H₀ := by
  set K : NNReal := ⟨max M.maxCorr 0, le_max_right _ _⟩
  set F : Lp ℝ 2 M.P → Lp ℝ 2 M.P := fun z => (memg hS z).toLp (gmap M z)
  have hK : K < 1 := by
    show (max M.maxCorr 0) < 1
    exact max_lt hr one_pos
  have hc : ContractingWith K F :=
    ⟨hK, LipschitzWith.of_dist_le_mul fun z₁ z₂ => g_lip hS z₁ z₂⟩
  set z := ContractingWith.fixedPoint F hc
  have hz : F z = z := ContractingWith.fixedPoint_isFixedPt hc
  set H₀ := gmap M z
  have hzH : (⇑z : Ω → ℝ) =ᵐ[M.P] H₀ := by
    have := MemLp.coeFn_toLp (memg hS z)
    rw [show (memg hS z).toLp (gmap M z) = F z from rfl, hz] at this
    exact this
  have mH : MemLp H₀ 2 M.P := memg hS z
  have smH : StronglyMeasurable[M.FX] H₀ := by
    show StronglyMeasurable[M.FX] (M.Pi0X + M.T _)
    unfold Market.Pi0X Market.T
    exact stronglyMeasurable_condExp.neg.add stronglyMeasurable_condExp
  have iH : Integrable H₀ M.P := mH.integrable one_le_two
  have hcz : M.P[⇑z|M.FX] =ᵐ[M.P] H₀ := by
    rw [← condExp_of_stronglyMeasurable (hFX hS) smH iH]
    exact condExp_congr_ae hzH
  have hint : ∫ ω, z ω ∂M.P = ∫ ω, H₀ ω ∂M.P := integral_congr_ae hzH
  set c := ∫ ω, H₀ ω ∂M.P
  have hu : (fun ω => M.P[⇑z|M.FX] ω - ∫ ω', z ω' ∂M.P) =ᵐ[M.P] H₀ - fun _ => c := by
    filter_upwards [hcz] with ω h
    simp only [Pi.sub_apply, h, hint]
  have hT1 : M.T (fun ω => M.P[⇑z|M.FX] ω - ∫ ω', z ω' ∂M.P) =ᵐ[M.P] M.T (H₀ - fun _ => c) := by
    unfold Market.T
    exact condExp_congr_ae (condExp_congr_ae hu)
  have hT2 : M.T H₀ - M.T (fun _ => c) =ᵐ[M.P] M.T (H₀ - fun _ => c) :=
    T_sub iH (integrable_const c)
  have hTc : M.T (fun _ => c) = fun _ => c := by
    unfold Market.T
    rw [condExp_const (hFI hS), condExp_const (hFX hS)]
  rw [hTc] at hT2
  -- (*) H₀ = Π + T H₀ - c a.e.
  have hstar : H₀ =ᵐ[M.P] fun ω => M.Pi0X ω + M.T H₀ ω - c := by
    filter_upwards [hT1, hT2] with ω h1 h2
    simp only [Pi.sub_apply] at h2
    show M.Pi0X ω + M.T _ ω = _
    rw [h1, ← h2]
    ring
  have hc0 : c = 0 := by
    have := integral_congr_ae hstar
    rw [integral_sub, integral_add, intPi0X hS, intT hS] at this
    · simp at this; linarith
    · exact (memPi0X hS).integrable one_le_two
    · exact (memT mH).integrable one_le_two
    · exact ((memPi0X hS).add (memT mH)).integrable one_le_two
    · exact integrable_const c
  refine ⟨H₀, ⟨⟨smH, mH⟩, hc0⟩, ?_⟩
  filter_upwards [hstar] with ω h
  rw [h, hc0]
  simp

end CHAux


open MeasureTheory ProbabilityTheory CustomHedge.Exist

namespace CHAux

section generic
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma maxCorr_nonneg (m₁ m₂ : MeasurableSpace Ω) : 0 ≤ maximalCorrelation P m₁ m₂ := by
  unfold maximalCorrelation
  set S := {r : ℝ | ∃ φ ψ : Ω → ℝ, InCentered P m₁ φ ∧ InCentered P m₂ ψ ∧
    0 < variance φ P ∧ 0 < variance ψ P ∧ r = pearsonCorr P φ ψ}
  rcases S.eq_empty_or_nonempty with h | ⟨r, φ, ψ, hφ, hψ, hvφ, hvψ, rfl⟩
  · rw [h, Real.sSup_empty]
  · have hψ' : InCentered P m₂ (-ψ) := by
      refine ⟨⟨hψ.1.1.neg, hψ.1.2.neg⟩, ?_⟩
      simp only [Pi.neg_apply]
      rw [integral_neg, hψ.2, neg_zero]
    have hv' : variance (-ψ) P = variance ψ P := by
      rw [var_eq hψ', var_eq hψ]; simp
    have hmem1 : pearsonCorr P φ ψ ∈ S := ⟨φ, ψ, hφ, hψ, hvφ, hvψ, rfl⟩
    have hmem2 : pearsonCorr P φ (-ψ) ∈ S := ⟨φ, -ψ, hφ, hψ', hvφ, by rw [hv']; exact hvψ, rfl⟩
    have he : pearsonCorr P φ (-ψ) = -pearsonCorr P φ ψ := by
      rw [pearson_eq hφ hψ', pearson_eq hφ hψ]
      simp only [Pi.neg_apply, mul_neg, neg_sq]
      rw [integral_neg, neg_div]
    have h1 := le_csSup (bdd (P := P) m₁ m₂) hmem1
    have h2 := le_csSup (bdd (P := P) m₁ m₂) hmem2
    rw [he] at h2
    linarith

end generic

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

variable {M : Market Ω EX EY EI} (hS : M.Standing)
include hS

lemma ms_inner_le_maxCorr (φ ψ : Ω → ℝ)
    (hφ : InCentered M.P M.FX φ) (hψ : InCentered M.P M.FI ψ) :
    ∫ ω, condExp M.FI M.P φ ω * ψ ω ∂M.P ≤ M.maxCorr * l2norm M.P φ * l2norm M.P ψ := by
  haveI : IsProbabilityMeasure M.P := hS.1
  rw [← tower (hFI hS) hφ.1.2 hψ.1.2 hψ.1.1]
  exact inner_le hφ hψ

lemma ms_ec_28 (φ : Ω → ℝ) (hφ : InCentered M.P M.FX φ) :
    l2norm M.P (condExp M.FI M.P φ) ≤ M.maxCorr * l2norm M.P φ := by
  haveI : IsProbabilityMeasure M.P := hS.1
  have h := ec28 (hFI hS) hφ
  have h0 := maxCorr_nonneg (P := M.P) M.FX M.FI
  rw [max_eq_left h0] at h
  unfold l2norm Market.maxCorr
  rw [← Real.sqrt_sq h0, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

lemma ms_T_norm_le (φ : Ω → ℝ) (hφ : InCentered M.P M.FX φ) :
    l2norm M.P (M.T φ) ≤ M.maxCorr * l2norm M.P φ := by
  haveI : IsProbabilityMeasure M.P := hS.1
  refine le_trans ?_ (ms_ec_28 hS φ hφ)
  unfold l2norm Market.T
  exact Real.sqrt_le_sqrt (sq_condExp_le (hFX hS) (memLp_condExp hφ.1.2))

lemma ms_T_maps_centered :
    (∀ Z : Ω → ℝ, Integrable Z M.P → ∫ ω, M.T Z ω ∂M.P = ∫ ω, Z ω ∂M.P) ∧
      (∀ Z : Ω → ℝ, InCentered M.P M.FX Z → InCentered M.P M.FX (M.T Z)) ∧
      InCentered M.P M.FX M.Pi0X := by
  haveI : IsProbabilityMeasure M.P := hS.1
  refine ⟨fun Z _ => intT hS Z, fun Z hZ => ?_, ?_⟩
  · refine ⟨⟨stronglyMeasurable_condExp, memT hZ.1.2⟩, ?_⟩
    rw [intT hS, hZ.2]
  · refine ⟨⟨?_, memPi0X hS⟩, intPi0X hS⟩
    unfold Market.Pi0X
    exact stronglyMeasurable_condExp.neg

/-- `E[K₀|M.FX] = E[π - Eπ|M.FX] - E[(ϱ/a)(1-D)|M.FX]` a.s. -/
lemma condExp_K0X [IsProbabilityMeasure M.P] :
    M.P[K0 M|M.FX] =ᵐ[M.P] M.P[fun ω => M.pos ω - ∫ ω', M.pos ω' ∂M.P|M.FX]
      - M.P[fun ω => M.rho / M.a * (1 - M.D ω)|M.FX] := by
  have e : K0 M = (fun ω => M.pos ω - ∫ ω', M.pos ω' ∂M.P)
      - fun ω => M.rho / M.a * (1 - M.D ω) := by
    funext ω
    have hEK : ∫ ω, M.K ω ∂M.P = ∫ ω, M.pos ω ∂M.P + M.rho / M.a := by
      unfold Market.K
      rw [integral_add ((memPos hS).integrable one_le_two)
        (((memD hS).integrable one_le_two).const_mul _), integral_const_mul, intD hS, mul_one]
    simp only [K0, Pi.sub_apply, hEK]
    simp only [Market.K]
    ring
  rw [e]
  exact condExp_sub (((memPos hS).integrable one_le_two).sub (integrable_const _))
    ((((integrable_const 1).sub ((memD hS).integrable one_le_two))).const_mul _) M.FX

/-- `E[K₀|M.FI] = E[π - Eπ|M.FI] - E[(ϱ/a)(1-D)|M.FI]` a.s. -/
lemma condExp_K0I [IsProbabilityMeasure M.P] :
    M.P[K0 M|M.FI] =ᵐ[M.P] M.P[fun ω => M.pos ω - ∫ ω', M.pos ω' ∂M.P|M.FI]
      - M.P[fun ω => M.rho / M.a * (1 - M.D ω)|M.FI] := by
  have e : K0 M = (fun ω => M.pos ω - ∫ ω', M.pos ω' ∂M.P)
      - fun ω => M.rho / M.a * (1 - M.D ω) := by
    funext ω
    have hEK : ∫ ω, M.K ω ∂M.P = ∫ ω, M.pos ω ∂M.P + M.rho / M.a := by
      unfold Market.K
      rw [integral_add ((memPos hS).integrable one_le_two)
        (((memD hS).integrable one_le_two).const_mul _), integral_const_mul, intD hS, mul_one]
    simp only [K0, Pi.sub_apply, hEK]
    simp only [Market.K]
    ring
  rw [e]
  exact condExp_sub (((memPos hS).integrable one_le_two).sub (integrable_const _))
    ((((integrable_const 1).sub ((memD hS).integrable one_le_two))).const_mul _) M.FI

lemma foc_iff [IsProbabilityMeasure M.P] {H₀ G₀ : Ω → ℝ} (hX : InCentered M.P M.FX H₀)
    (hI : InCentered M.P M.FI G₀) :
    M.FirstOrder H₀ G₀ ↔
      (M.P[K0 M + (H₀ + G₀)|M.FX] =ᵐ[M.P] 0 ∧ M.P[K0 M + (H₀ + G₀)|M.FI] =ᵐ[M.P] 0) := by
  have iK0 : Integrable (K0 M) M.P := (memK0 hS).integrable one_le_two
  have iH : Integrable H₀ M.P := hX.1.2.integrable one_le_two
  have iG : Integrable G₀ M.P := hI.1.2.integrable one_le_two
  have a1 := condExp_add (m := M.FX) iK0 (iH.add iG)
  have a2 := condExp_add (m := M.FX) iH iG
  have a3 : M.P[H₀|M.FX] = H₀ := condExp_of_stronglyMeasurable (hFX hS) hX.1.1 iH
  have b1 := condExp_add (m := M.FI) iK0 (iH.add iG)
  have b2 := condExp_add (m := M.FI) iH iG
  have b3 : M.P[G₀|M.FI] = G₀ := condExp_of_stronglyMeasurable (hFI hS) hI.1.1 iG
  have kX := condExp_K0X hS
  have kI := condExp_K0I hS
  unfold Market.FirstOrder
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · filter_upwards [h1, a1, a2, kX] with ω e1 e2 e3 e4
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at e1 e2 e3 e4 ⊢
      rw [a3] at e3
      rw [e2, e3, e4]; linarith
    · filter_upwards [h2, b1, b2, kI] with ω e1 e2 e3 e4
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at e1 e2 e3 e4 ⊢
      rw [b3] at e3
      rw [e2, e3, e4]; linarith
  · rintro ⟨h1, h2⟩
    constructor
    · filter_upwards [h1, a1, a2, kX] with ω e1 e2 e3 e4
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at e1 e2 e3 e4 ⊢
      rw [a3] at e3
      rw [e2, e3, e4] at e1; linarith
    · filter_upwards [h2, b1, b2, kI] with ω e1 e2 e3 e4
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply] at e1 e2 e3 e4 ⊢
      rw [b3] at e3
      rw [e2, e3, e4] at e1; linarith

lemma ms_ec_25 (H₀ G₀ : Ω → ℝ)
    (hH : InCentered M.P M.FX H₀) (hG : InCentered M.P M.FI G₀)
    (h5 : M.FirstOrder H₀ G₀) :
    H₀ =ᵐ[M.P] M.Pi0X + M.T H₀ := by
  haveI : IsProbabilityMeasure M.P := hS.1
  obtain ⟨f1, f2⟩ := (foc_iff hS hH hG).1 h5
  exact foc_fixed hS hH hG f1 f2

lemma ms_proposition_1 (H G : Ω → ℝ) (hopt : M.IsOptimal H G) :
    let H₀ : Ω → ℝ := fun ω => H ω - ∫ ω', H ω' ∂M.P
    let G₀ : Ω → ℝ := fun ω => G ω - ∫ ω', G ω' ∂M.P
    (H = fun ω => H₀ ω - M.EQ H₀) ∧ (G = fun ω => G₀ ω - M.EQ G₀) ∧
      ∫ ω, H₀ ω ∂M.P = 0 ∧ ∫ ω, G₀ ω ∂M.P = 0 ∧ M.FirstOrder H₀ G₀ := by
  haveI : IsProbabilityMeasure M.P := hS.1
  intro H₀ G₀
  have hX : InCentered M.P M.FX H₀ := cen_centeredX hopt.1.1
  have hI : InCentered M.P M.FI G₀ := cen_centeredI hopt.1.2.1
  have eq1 : ∀ {Z : Ω → ℝ}, MemLp Z 2 M.P → M.EQ Z = 0 →
      M.EQ (fun ω => Z ω - ∫ ω', Z ω' ∂M.P) = -∫ ω', Z ω' ∂M.P := by
    intro Z hZ hQ
    unfold Market.EQ at hQ ⊢
    have e : (fun ω => (Z ω - ∫ ω', Z ω' ∂M.P) * M.D ω) =
        fun ω => Z ω * M.D ω - (∫ ω', Z ω' ∂M.P) * M.D ω := by funext ω; ring
    rw [e, integral_sub (int_mul hZ (memD hS)) (((memD hS).integrable one_le_two).const_mul _),
      integral_const_mul, intD hS, hQ]
    ring
  refine ⟨?_, ?_, hX.2, hI.2, ?_⟩
  · funext ω
    show H ω = H ω - ∫ ω', H ω' ∂M.P - M.EQ (fun ω => H ω - ∫ ω', H ω' ∂M.P)
    rw [eq1 hopt.1.1.2 hopt.1.2.2.1]; ring
  · funext ω
    show G ω = G ω - ∫ ω', G ω' ∂M.P - M.EQ (fun ω => G ω - ∫ ω', G ω' ∂M.P)
    rw [eq1 hopt.1.2.1.2 hopt.1.2.2.2]; ring
  · exact (foc_iff hS hX hI).2 (min_foc hS hX hI (opt_min hS hopt))

lemma ms_ec_27_unique (hr : M.maxCorr < 1) :
    ∃ H₀ : Ω → ℝ, (InCentered M.P M.FX H₀ ∧ H₀ =ᵐ[M.P] M.Pi0X + M.T H₀) ∧
      ∀ H₀' : Ω → ℝ, InCentered M.P M.FX H₀' → H₀' =ᵐ[M.P] M.Pi0X + M.T H₀' →
        H₀' =ᵐ[M.P] H₀ := by
  haveI : IsProbabilityMeasure M.P := hS.1
  obtain ⟨H₀, hX, hfix⟩ := exists_fixed hS hr
  refine ⟨H₀, ⟨hX, hfix⟩, fun H₁ hX1 hfix1 => ?_⟩
  set Z : Ω → ℝ := H₁ - H₀
  have hZ : InCentered M.P M.FX Z := by
    refine ⟨⟨hX1.1.1.sub hX.1.1, hX1.1.2.sub hX.1.2⟩, ?_⟩
    show ∫ ω, (H₁ ω - H₀ ω) ∂M.P = 0
    rw [integral_sub (hX1.1.2.integrable one_le_two) (hX.1.2.integrable one_le_two), hX1.2, hX.2]
    simp
  have hTZ : Z =ᵐ[M.P] M.T Z := by
    have := T_sub (M := M) (hX1.1.2.integrable one_le_two) (hX.1.2.integrable one_le_two)
    filter_upwards [this, hfix, hfix1] with ω h1 h2 h3
    simp only [Pi.sub_apply, Pi.add_apply, Z] at h1 h2 h3 ⊢
    rw [← h1]; linarith
  have a1 := sq_condExp_le (hFX hS) (memLp_condExp (m := M.FI) hZ.1.2)
  have a2 := ec28 (hFI hS) hZ
  have e : ∫ ω, Z ω ^ 2 ∂M.P = ∫ ω, (M.T Z) ω ^ 2 ∂M.P := sq_congr hTZ
  unfold Market.T at e
  have hr0 : max M.maxCorr 0 < 1 := max_lt hr one_pos
  have hr1 : 0 ≤ max M.maxCorr 0 := le_max_right _ _
  have hsq : (max M.maxCorr 0) ^ 2 < 1 := by nlinarith
  unfold Market.maxCorr at hsq
  have hN0 : 0 ≤ ∫ ω, Z ω ^ 2 ∂M.P := integral_nonneg (fun ω => sq_nonneg _)
  have hN : ∫ ω, Z ω ^ 2 ∂M.P = 0 := by nlinarith
  have h0 := ae_zero_of_sq hZ.1.2 hN
  filter_upwards [h0] with ω h
  simp only [Z, Pi.sub_apply, Pi.zero_apply] at h
  linarith

end CHAux


theorem solution {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
    [MeasurableSpace EY] [MeasurableSpace EI] (M : Market Ω EX EY EI) (hS : M.Standing) (hr : M.maxCorr < 1) :
    ∃ H₀ : Ω → ℝ, (InCentered M.P M.FX H₀ ∧ H₀ =ᵐ[M.P] M.Pi0X + M.T H₀) ∧
      ∀ H₀' : Ω → ℝ, InCentered M.P M.FX H₀' → H₀' =ᵐ[M.P] M.Pi0X + M.T H₀' →
        H₀' =ᵐ[M.P] H₀ := CHAux.ms_ec_27_unique hS hr
