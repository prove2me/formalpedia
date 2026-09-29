-- Prove2me | solution 1 for DiazModulus.candidate_multiplier_module
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T09:16:59.102975+00:00
-- url     : https://prove2.me/submissions/9c460adb-7e30-4e83-8ac8-935ea2282ee4

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

-- The multiplier module of a hypothetical candidate, under Roy's strong six
-- exponentials theorem (carried as the hypothesis `hSSE`) and Hermite--Lindemann.
open DiazModulus in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    {z : ℂ | z ∈ LogAlgTilde ∧ u * z ∈ LogAlgTilde}
        = (Submodule.span Qbar ({1, u⁻¹} : Set ℂ) : Set ℂ)
      ∧ u ^ 2 ∉ LogAlgTilde
      ∧ ∀ a : ℂ, a ∈ Qbar → a ≠ 0 → (u - a)⁻¹ ∉ LogAlgTilde := by
  have isAlgebraic_conj : ∀ {a : ℂ}, IsAlgebraic ℚ a → IsAlgebraic ℚ (conj a) :=
    fun ha => ha.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
  have logAlg_conj : ∀ {w : ℂ}, w ∈ LogAlg → conj w ∈ LogAlg := by
    intro w hw
    have he : Complex.exp (conj w) = conj (Complex.exp w) := Complex.exp_conj w
    rw [LogAlg, Set.mem_setOf_eq, he]
    exact isAlgebraic_conj hw
  have conj_eq_normSq_div : ∀ w : ℂ, conj w = ((‖w‖ : ℝ) : ℂ) ^ 2 / w := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [eq_div_iff hw, mul_comm, Complex.mul_conj]
      norm_cast
      simp [Complex.normSq_eq_norm_sq]
  obtain ⟨hu, hnorm, hexp⟩ := h
  have hsmul : ∀ (c : ↥Qbar) (z : ℂ), c • z = (c : ℂ) * z := fun _ _ => rfl
  set lam : ℂ := ((‖u‖ : ℝ) : ℂ) with hlam_def
  have hlam0 : lam ≠ 0 := by simp [hlam_def, hu]
  have hlamQ : lam ∈ Qbar := mem_Qbar_iff.mpr hnorm
  have huQ : u ∉ Qbar := fun hq => hHL u hu (mem_Qbar_iff.mp hq) hexp
  -- memberships in `ℒ̃`
  have hone : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert _ _)
  have huT : u ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert_of_mem _ hexp)
  have hconjT : conj u ∈ LogAlgTilde :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (logAlg_conj hexp))
  have hinvT : u⁻¹ ∈ LogAlgTilde := by
    have hrw : u⁻¹ = ((lam ^ 2)⁻¹ : ℂ) * conj u := by
      rw [conj_eq_normSq_div u, ← hlam_def]
      field_simp
    have hmem : ((lam ^ 2)⁻¹ : ℂ) ∈ Qbar :=
      Subfield.inv_mem _ (Subfield.pow_mem _ hlamQ 2)
    have := Submodule.smul_mem LogAlgTilde (⟨((lam ^ 2)⁻¹ : ℂ), hmem⟩ : ↥Qbar) hconjT
    rw [hrw]; simpa [hsmul] using this
  -- no non-trivial quadratic over `Q̄` vanishes at `u`
  have hdeg2 : ∀ c₂ c₁ c₀ : ℂ, c₂ ∈ Qbar → c₁ ∈ Qbar → c₀ ∈ Qbar →
      ¬ (c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0) → c₂ * u ^ 2 + c₁ * u + c₀ ≠ 0 := by
    intro c₂ c₁ c₀ h2 h1 h0 hne heq
    by_cases hc2 : c₂ = 0
    · by_cases hc1 : c₁ = 0
      · exact hne ⟨hc2, hc1, by simpa [hc2, hc1] using heq⟩
      · refine huQ ?_
        have : u = -c₀ / c₁ := by field_simp; linear_combination heq - u ^ 2 * hc2
        rw [this]
        exact Subfield.div_mem _ (Subfield.neg_mem _ h0) h1
    · -- `w = 2u - c₁/c₂ + ...` : complete the square
      refine huQ ?_
      have hw : (2 * c₂ * u + c₁) ^ 2 = c₁ ^ 2 - 4 * c₂ * c₀ := by
        linear_combination (4 * c₂) * heq
      have hwQ : ((2 * c₂ * u + c₁) ^ 2) ∈ Qbar := by
        rw [hw]
        exact Subfield.sub_mem _ (Subfield.pow_mem _ h1 2)
          (Subfield.mul_mem _ (Subfield.mul_mem _ (by
            simpa using Subfield.natCast_mem Qbar 4) h2) h0)
      have hwalg : IsAlgebraic ℚ (2 * c₂ * u + c₁) :=
        IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hwQ)
      have hwmem : (2 * c₂ * u + c₁) ∈ Qbar := mem_Qbar_iff.mpr hwalg
      have : u = ((2 * c₂ * u + c₁) - c₁) / (2 * c₂) := by field_simp; ring
      rw [this]
      exact Subfield.div_mem _ (Subfield.sub_mem _ hwmem h1)
        (Subfield.mul_mem _ (by simpa using Subfield.natCast_mem Qbar 2) h2)
  -- the two independence facts, from one reason
  have key : ∀ s t : ↥Qbar, (s : ℂ) * u + (t : ℂ) = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    by_cases hs : (s : ℂ) = 0
    · have ht : (t : ℂ) = 0 := by rw [hs, zero_mul, zero_add] at hst; exact hst
      exact ⟨Subtype.ext hs, Subtype.ext ht⟩
    · refine absurd ?_ huQ
      have hueq : u = -(t : ℂ) / (s : ℂ) := by field_simp; linear_combination hst
      rw [hueq]
      exact Subfield.div_mem _ (Subfield.neg_mem _ t.2) s.2
  have hx : LinearIndependent (↥Qbar) ![(1 : ℂ), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [hsmul, mul_one] at hst
    have h' : (t : ℂ) * u + (s : ℂ) = 0 := by linear_combination hst
    exact ⟨(key t s h').2, (key t s h').1⟩
  have hpair : LinearIndependent (↥Qbar) ![(1 : ℂ), u⁻¹] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [hsmul, mul_one] at hst
    have h' : (s : ℂ) * u + (t : ℂ) = 0 := by field_simp at hst; linear_combination hst
    exact key s t h'
  have htriple : ∀ z : ℂ, z ∉ Submodule.span Qbar ({1, u⁻¹} : Set ℂ) →
      LinearIndependent (↥Qbar) ![z, (1 : ℂ), u⁻¹] := by
    intro z hz
    have hcons : ![z, (1 : ℂ), u⁻¹] = Fin.cons z ![(1 : ℂ), u⁻¹] := by
      funext i; fin_cases i <;> rfl
    rw [hcons, linearIndependent_finCons]
    refine ⟨hpair, ?_⟩
    have hrange : Set.range ![(1 : ℂ), u⁻¹] = ({1, u⁻¹} : Set ℂ) := by
      simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    rw [hrange]; exact hz
  -- forward inclusion: the strong six exponentials theorem
  have hfwd : ∀ z : ℂ, z ∈ LogAlgTilde → u * z ∈ LogAlgTilde →
      z ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ) := by
    intro z hz1 hz2
    by_contra hz
    refine hSSE ![(1 : ℂ), u] ![z, (1 : ℂ), u⁻¹] hx (htriple z hz) ?_
    intro i j
    have hlast : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
    fin_cases i <;> fin_cases j <;> simp <;>
      first
        | exact hz1
        | exact hone
        | exact hinvT
        | exact hz2
        | exact huT
        | (rw [hlast]; exact hone)
  -- reverse inclusion: elementary
  have hspan_le : Submodule.span Qbar ({1, u⁻¹} : Set ℂ) ≤ LogAlgTilde := by
    rw [Submodule.span_le]
    intro w hw
    rcases hw with hw | hw
    · rw [hw]; exact hone
    · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hinvT
  have hbwd : ∀ z ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ),
      z ∈ LogAlgTilde ∧ u * z ∈ LogAlgTilde := by
    intro z hz
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
    refine ⟨hspan_le hz, ?_⟩
    have hz' : z = (a : ℂ) + (b : ℂ) * u⁻¹ := by
      rw [← hab]; simp only [hsmul, mul_one]
    have hmul : u * z = (a : ℂ) * u + (b : ℂ) := by
      rw [hz']; field_simp
    rw [hmul]
    exact Submodule.add_mem _
      (by simpa [hsmul] using Submodule.smul_mem LogAlgTilde a huT)
      (by simpa [hsmul] using Submodule.smul_mem LogAlgTilde b hone)
  refine ⟨Set.ext fun z => ⟨fun hz => hfwd z hz.1 hz.2, fun hz => hbwd z hz⟩, ?_, ?_⟩
  · -- squares
    intro hsq
    have hmem := hfwd u huT (by rw [← pow_two]; exact hsq)
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    have hz' : (a : ℂ) + (b : ℂ) * u⁻¹ = u := by simpa only [hsmul, mul_one] using hab
    refine hdeg2 1 (-(a : ℂ)) (-(b : ℂ)) (one_mem _) (Subfield.neg_mem _ a.2)
      (Subfield.neg_mem _ b.2) (by simp) ?_
    field_simp at hz'
    linear_combination -hz'
  · -- shifted reciprocals
    intro a haQ ha0 hmem
    have hua : u - a ≠ 0 := by
      intro hzero
      exact huQ (by rw [sub_eq_zero.mp hzero]; exact haQ)
    have hz2 : u * (u - a)⁻¹ ∈ LogAlgTilde := by
      have hrw : u * (u - a)⁻¹ = 1 + a * (u - a)⁻¹ := by field_simp; ring
      rw [hrw]
      exact Submodule.add_mem _ hone
        (by simpa [hsmul] using
          Submodule.smul_mem LogAlgTilde (⟨a, haQ⟩ : ↥Qbar) hmem)
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp (hfwd _ hmem hz2)
    have hz' : (c : ℂ) + (d : ℂ) * u⁻¹ = (u - a)⁻¹ := by
      simpa only [hsmul, mul_one] using hcd
    refine hdeg2 (c : ℂ) ((d : ℂ) - (c : ℂ) * a - 1) (-((d : ℂ) * a)) c.2
      (Subfield.sub_mem _ (Subfield.sub_mem _ d.2 (Subfield.mul_mem _ c.2 haQ)) (one_mem _))
      (Subfield.neg_mem _ (Subfield.mul_mem _ d.2 haQ)) ?_ ?_
    · rintro ⟨hc, hd, hda⟩
      rw [hc] at hd
      have hd1 : (d : ℂ) = 1 := by linear_combination hd
      rw [hd1, one_mul, neg_eq_zero] at hda
      exact ha0 hda
    · field_simp at hz'
      linear_combination hz'

