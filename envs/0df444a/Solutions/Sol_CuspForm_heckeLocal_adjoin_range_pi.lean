-- Prove2me | solution 1 for CuspForm.heckeLocal.adjoin_range_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/de25ca63-8a77-574d-ab14-8769d6e7380e

import Definitions.Def_CuspForm_HeckeLocal
import Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_adjoin_range_pi

open CuspForm
open scoped TensorProduct

private lemma sol_moduleFinite_base (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] :
    Module.Finite 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Module.Finite 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

private lemma sol_surjective_atPrime {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (P : MaximalSpectrum B) :
    Function.Surjective (algebraMap B (Localization.AtPrime P.asIdeal)) := by
  classical
  obtain ⟨-, hbij, -, -⟩ := Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := R) B
  intro z
  obtain ⟨b, hb⟩ := hbij.2 (Function.update 0 P z)
  refine ⟨b, ?_⟩
  have h := congrFun hb P
  simp at h
  exact h

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in
theorem solution (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪) (hint : CuspForm.HasIntegralStructure N 2) : Algebra.adjoin 𝒪 (Set.range (CuspForm.heckeLocal.π N S 𝒪 θ)) = ⊤ := by
  haveI : Fact (HasIntegralStructure N 2) := ⟨hint⟩
  classical
  haveI := sol_moduleFinite_base N S 𝒪
  have hsurjAt := sol_surjective_atPrime (R := 𝒪) (heckeBaseAlgebra N S 𝒪)
    ⟨heckeLocalIdeal N S 𝒪 θ, inferInstance⟩
  have e := IsLocalization.algEquiv (heckeLocalIdeal N S 𝒪 θ).primeCompl
    (Localization.AtPrime (heckeLocalIdeal N S 𝒪 θ)) (heckeLocal N S 𝒪 θ)
  have hsurj : Function.Surjective
      (algebraMap (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)) := by
    intro y
    obtain ⟨a, ha⟩ := hsurjAt (e.symm y)
    refine ⟨a, ?_⟩
    have h := congrArg e ha
    rwa [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] at h
  have hgen0 : ∀ x : 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S),
      x ∈ Algebra.adjoin 𝒪 (Set.range fun t : ↥(heckeAlgebra N 2 S) =>
        latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a s =>
      obtain ⟨t, rfl⟩ := latticeRestrictHom_surjective N S s
      have hmem : latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t) ∈
          Algebra.adjoin 𝒪 (Set.range fun t : ↥(heckeAlgebra N 2 S) =>
            latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t)) :=
        Algebra.subset_adjoin ⟨t, rfl⟩
      have hgenval : latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t) =
          ((1 : 𝒪) ⊗ₜ[ℤ] latticeRestrictHom N S t : 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)) := by
        rw [Algebra.TensorProduct.includeRight_apply, latticeBaseChange_tmul]
      have hsmul : (a ⊗ₜ[ℤ] latticeRestrictHom N S t : 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)) =
          a • ((1 : 𝒪) ⊗ₜ[ℤ] latticeRestrictHom N S t :
            𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hsmul, ← hgenval]
      exact Subalgebra.smul_mem _ hmem a
    | add x y hx hy => exact add_mem hx hy
  have hgen : Algebra.adjoin 𝒪 (Set.range fun t : ↥(heckeAlgebra N 2 S) =>
      latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t)) = ⊤ :=
    eq_top_iff.mpr fun x _ => hgen0 x
  have hπ : Set.range (heckeLocal.π N S 𝒪 θ) =
      ⇑(IsScalarTower.toAlgHom 𝒪 (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)) ''
        Set.range (fun t : ↥(heckeAlgebra N 2 S) =>
          latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t)) := by
    rw [← Set.range_comp]
    rfl
  have hmap := AlgHom.map_adjoin (IsScalarTower.toAlgHom 𝒪 (heckeBaseAlgebra N S 𝒪)
    (heckeLocal N S 𝒪 θ)) (Set.range fun t : ↥(heckeAlgebra N 2 S) =>
      latticeBaseChange N S 𝒪 (Algebra.TensorProduct.includeRight t))
  rw [hπ, ← hmap, hgen, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr hsurj

end S_CuspForm_heckeLocal_adjoin_range_pi
end P2MW
export P2MW.S_CuspForm_heckeLocal_adjoin_range_pi (solution)
