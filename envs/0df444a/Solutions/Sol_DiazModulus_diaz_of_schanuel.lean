-- Prove2me | solution 1 for DiazModulus.diaz_of_schanuel
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T09:54:59.882507+00:00
-- url     : https://prove2.me/submissions/9f52c1d5-e114-4e1c-bcf9-4f5ef6619feb

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_conj_eq_norm_sq_div
import Theorems.Thm_DiazModulus_logAlg_conj_stable

open Complex ComplexConjugate
open scoped Cardinal
open IntermediateField.algebraAdjoinAdjoin

noncomputable section

namespace SchanuelDiaz

/-! ### Transcendence-degree bookkeeping

Two bounds, both obtained by comparing `IntermediateField.adjoin ℚ S` with a larger
intermediate field whose transcendence degree we can compute. -/

/-- Every algebraic number lies in the relative algebraic closure of `ℚ` in `ℂ`. -/
theorem mem_algClosure {z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.mpr h

/-- `trdeg ℚ Q̄ = 0`.  The `Algebra.IsAlgebraic` instance has to be supplied by hand. -/
theorem trdeg_algClosure : Algebra.trdeg ℚ ↥(algebraicClosure ℚ ℂ) = 0 :=
  @trdeg_eq_zero _ _ _ _ _ (algebraicClosure.isAlgebraic ℚ ℂ)

/-- A field generated over `ℚ` by algebraic numbers has transcendence degree `0`. -/
theorem trdeg_adjoin_eq_zero (S : Set ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    Algebra.trdeg ℚ ↥(IntermediateField.adjoin ℚ S) = 0 := by
  have hle : IntermediateField.adjoin ℚ S ≤ algebraicClosure ℚ ℂ :=
    IntermediateField.adjoin_le_iff.mpr fun z hz => mem_algClosure (hS z hz)
  have hmono := trdeg_le_of_injective (IntermediateField.inclusion hle)
    (IntermediateField.inclusion_injective _)
  exact le_antisymm (trdeg_algClosure ▸ hmono) zero_le

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
/-- **The reusable bound.**  `trdeg_{Q̄} Q̄(u) ≤ 1` for every `u : ℂ`. -/
theorem trdeg_adjoin_singleton_le_one (u : ℂ) :
    Algebra.trdeg (↥(algebraicClosure ℚ ℂ))
      ↥(IntermediateField.adjoin (↥(algebraicClosure ℚ ℂ)) ({u} : Set ℂ)) ≤ 1 := by
  set K : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ with hK
  set F : IntermediateField (↥K) ℂ := IntermediateField.adjoin (↥K) ({u} : Set ℂ) with hF
  set R : Subalgebra (↥K) ℂ := Algebra.adjoin (↥K) ({u} : Set ℂ) with hR
  -- `K[u]` is a quotient of the polynomial ring, so its transcendence degree is at most `1`
  have hrange : R = (Polynomial.aeval u : Polynomial (↥K) →ₐ[↥K] ℂ).range :=
    Algebra.adjoin_singleton_eq_range_aeval (↥K) u
  let f : Polynomial (↥K) →ₐ[↥K] ↥R :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toAlgHom.comp
      (Polynomial.aeval u : Polynomial (↥K) →ₐ[↥K] ℂ).rangeRestrict
  have hfsurj : Function.Surjective f :=
    (Subalgebra.equivOfEq _ _ hrange.symm).surjective.comp (AlgHom.rangeRestrict_surjective _)
  have h1 : Algebra.trdeg (↥K) ↥R ≤ 1 := by
    have := trdeg_le_of_surjective f hfsurj
    simpa [Polynomial.trdeg_of_isDomain] using this
  -- `K(u)` is the fraction field of `K[u]`, hence algebraic over it
  have h2 : Algebra.trdeg (↥R) ↥F = 0 := trdeg_eq_zero
  have hadd : Algebra.trdeg (↥K) ↥R + Algebra.trdeg (↥R) ↥F = Algebra.trdeg (↥K) ↥F :=
    trdeg_add_eq (↥K) (↥R) (A := ↥F)
  rw [← hadd, h2, add_zero]
  exact h1

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
/-- If every generator lies in `Q̄(u)` then the generated field has transcendence degree `≤ 1`. -/
theorem trdeg_adjoin_le_one (u : ℂ) (S : Set ℂ)
    (hS : ∀ z ∈ S, z ∈ IntermediateField.adjoin (↥(algebraicClosure ℚ ℂ)) ({u} : Set ℂ)) :
    Algebra.trdeg ℚ ↥(IntermediateField.adjoin ℚ S) ≤ 1 := by
  set K : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ with hK
  set F : IntermediateField (↥K) ℂ := IntermediateField.adjoin (↥K) ({u} : Set ℂ) with hF
  have hle : IntermediateField.adjoin ℚ S ≤ F.restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.mpr hS
  have hmono : Algebra.trdeg ℚ ↥(IntermediateField.adjoin ℚ S)
      ≤ Algebra.trdeg ℚ ↥(F.restrictScalars ℚ) :=
    trdeg_le_of_injective (IntermediateField.inclusion hle)
      (IntermediateField.inclusion_injective _)
  have heq : Algebra.trdeg ℚ ↥(F.restrictScalars ℚ) = Algebra.trdeg ℚ ↥F := rfl
  rw [heq] at hmono
  -- `trdeg ℚ Q̄(u) = trdeg ℚ Q̄ + trdeg_{Q̄} Q̄(u) = 0 + (≤ 1)`
  have hadd : Algebra.trdeg ℚ ↥K + Algebra.trdeg (↥K) ↥F = Algebra.trdeg ℚ ↥F :=
    trdeg_add_eq ℚ (↥K) (A := ↥F)
  rw [← hadd, trdeg_algClosure, zero_add] at hmono
  exact hmono.trans (trdeg_adjoin_singleton_le_one u)

end SchanuelDiaz

open SchanuelDiaz in
open DiazModulus in
theorem solution (hS : SchanuelConjecture) : DiazModulusConjecture := by
  -- Schanuel at `n = 1` *is* Hermite--Lindemann; no separate hypothesis is needed.
  have hHL : HermiteLindemann := by
    intro a ha halg hexpa
    have hli : LinearIndependent ℚ ![a] := by
      rw [linearIndependent_unique_iff]
      simpa using ha
    have h1 := hS 1 ![a] hli
    have hz := trdeg_adjoin_eq_zero
      (Set.range ![a] ∪ Set.range fun i => Complex.exp (![a] i)) ?_
    · rw [hz] at h1
      simp at h1
    · rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simpa using ‹_›
  intro u hu hnorm hexp
  set K : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ with hK
  by_cases hind : LinearIndependent ℚ ![u, conj u]
  · -- **Case A.** `u` and `conj u` are `ℚ`-linearly independent: Schanuel at `n = 2`.
    have h2 := hS 2 ![u, conj u] hind
    -- every generator lies in `Q̄(u)`
    have humem : u ∈ IntermediateField.adjoin (↥K) ({u} : Set ℂ) :=
      IntermediateField.subset_adjoin (↥K) _ rfl
    have hKmem : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ IntermediateField.adjoin (↥K) ({u} : Set ℂ) := by
      intro z hz
      have : (algebraMap (↥K) ℂ) ⟨z, mem_algClosure hz⟩ ∈
          IntermediateField.adjoin (↥K) ({u} : Set ℂ) :=
        IntermediateField.algebraMap_mem _ _
      exact this
    have hconj : conj u ∈ IntermediateField.adjoin (↥K) ({u} : Set ℂ) := by
      rw [conj_eq_norm_sq_div u]
      exact div_mem (hKmem _ (hnorm.pow 2)) humem
    have hexpconj : IsAlgebraic ℚ (Complex.exp (conj u)) := logAlg_conj_stable u hexp
    have hle := trdeg_adjoin_le_one u
      (Set.range ![u, conj u] ∪ Set.range fun i => Complex.exp (![u, conj u] i)) ?_
    · exact absurd (h2.trans hle) (by norm_num)
    · rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i
      · simpa using humem
      · simpa using hconj
      · exact hKmem _ (by simpa using hexp)
      · exact hKmem _ (by simpa using hexpconj)
  · -- **Case B.** `conj u = r * u` for a real `r`, so `u` sits on one of the two axes.
    rw [LinearIndependent.pair_iff] at hind
    push_neg at hind
    obtain ⟨s, t, hst, hnz⟩ := hind
    simp only [Rat.smul_def] at hst
    have ht : t ≠ 0 := by
      rintro rfl
      simp only [Rat.cast_zero, zero_mul, add_zero] at hst
      rcases mul_eq_zero.mp hst with h | h
      · exact hnz (by exact_mod_cast h) rfl
      · exact hu h
    set r : ℝ := ((-s / t : ℚ) : ℝ) with hr
    have hconj : conj u = (r : ℂ) * u := by
      have htc : ((t : ℚ) : ℂ) ≠ 0 := by exact_mod_cast ht
      rw [hr]
      push_cast
      field_simp
      linear_combination hst
    have hre : u.re = r * u.re := by
      have := congrArg Complex.re hconj
      simpa using this
    have him : -u.im = r * u.im := by
      have := congrArg Complex.im hconj
      simpa using this
    have hax : u.im = 0 ∨ u.re = 0 := by
      by_cases h1 : r = 1
      · left; rw [h1, one_mul] at him; linarith
      · right
        have : u.re * (1 - r) = 0 := by linarith [hre]
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linarith : r = 1) h1
    -- on either axis `u² = ± ‖u‖²`, so `u` is algebraic and Hermite--Lindemann applies
    have key : ((‖u‖ : ℝ) : ℂ) ^ 2 = u * conj u := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hq : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hnorm
    have hsq : u ^ 2 ∈ Qbar := by
      rcases hax with h | h
      · have hc : conj u = u := Complex.conj_eq_iff_im.mpr h
        have h2 : u ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by rw [key, hc]; ring
        rw [h2]; exact pow_mem hq 2
      · have hc : conj u = -u := by apply Complex.ext <;> simp [h]
        have h2 : u ^ 2 = -(((‖u‖ : ℝ) : ℂ) ^ 2) := by rw [key, hc]; ring
        rw [h2]; exact neg_mem (pow_mem hq 2)
    exact hHL u hu (IsAlgebraic.of_pow two_pos (mem_Qbar_iff.mp hsq)) hexp
