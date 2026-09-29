-- Prove2me | solution 1 for CerednikDrinfeld.nonempty_matching_classSetHeckeData_heckeData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/96cef282-75f0-5fa4-9785-e182f320e8e1

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
p2m_open "IsDedekindDomain QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData.CerednikDrinfeld ModularCurve"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Matching meetOrder classSetForget classSetShift classSetDegeneracyData classSetEdgeHecke ClassSetHeckeLaws classSetHeckeData"
namespace AssembleMatching
p2m_open "CerednikDrinfeld"

variable {a b : ℚ}

theorem classSetForget_mk {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (h : U ≤ U')
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    classSetForget U U' (ClassSet.mk U y) = ClassSet.mk U' y := by
  unfold classSetForget
  obtain ⟨c, k, hc, hk, e⟩ := DoubleCoset.mk_out_eq_mul
    ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    U y
  erw [e]
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hc
  rw [mul_assoc, ClassSet.mk_diagonal_mul, ClassSet.mk_mul_of_mem _ _ (h hk)]

theorem classSetForget_self {U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (x : ClassSet U) :
    classSetForget U U x = x := by
  obtain ⟨y, rfl⟩ := ClassSet.mk_surjective x
  exact classSetForget_mk le_rfl y

theorem classSetDegeneracyData_b_eq_a_classSetShift (R : Submodule ℤ ℍ[ℚ, a, b])
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hU : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R)
    (e : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))) :
    (classSetDegeneracyData R n).b e = (classSetDegeneracyData R n).a (classSetShift _ n e) := by
  show ClassSet.mk _ (e.out * n) = classSetForget _ _ (ClassSet.mk _ (e.out * n))
  rw [classSetForget_mk hU]

section Branches

variable (M s : ℕ) [Fact s.Prime] (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
  [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
  [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

theorem classSetHeckeData_T (hlaws : ClassSetHeckeLaws M s Λ R n) :
    (classSetHeckeData M s Λ R n).T = classSetEdgeHecke M s Λ R n := by
  unfold classSetHeckeData
  rw [dif_pos hlaws]

end Branches

theorem heckeData_T {q' : ℕ} [Fact q'.Prime] {K : Type} [Field K] [CharP K q'] [DecidableEq K] {M s : ℕ}
    [NeZero M] [Fact s.Prime]
    (X : SSLevelDatum q' K M s)
    [Fintype ↥(ssPlaces q' (M * s) K)] [Fintype ↥(ssPlaces q' M K)] [DecidableEq ↥(ssPlaces q' M K)]
    (hX : X.HeckeLaws) : X.heckeData.T = X.edgeHecke := by
  unfold SSLevelDatum.heckeData
  rw [dif_pos hX]

theorem main
    (M s q' : ℕ) [NeZero M] [Fact s.Prime] [Fact q'.Prime]
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hU : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R)
    (hlaws : ClassSetHeckeLaws M s Λ R n)
    (K : Type) [Field K] [CharP K q'] [DecidableEq K]
    (X : SSLevelDatum q' K M s)
    [Fintype ↥(ssPlaces q' (M * s) K)] [Fintype ↥(ssPlaces q' M K)] [DecidableEq ↥(ssPlaces q' M K)]
    (hX : X.HeckeLaws)
    (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃ ↥(ssPlaces q' (M * s) K))
    (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' M K))
    (ha : ∀ e, X.degeneracyData.a (eE e) = eV ((classSetDegeneracyData R n).a e))
    (hw : ∀ e, X.degeneracyData.w (eE e) = (classSetDegeneracyData R n).w e)
    (hT : ∀ (ℓ : Nat.Primes) (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ),
      (X.edgeHecke ℓ).mulVecLin (x ∘ eE.symm) = ((classSetEdgeHecke M s Λ R n ℓ).mulVecLin x) ∘ eE.symm)
    (hAL : ∀ e, eE (classSetShift _ n e) = X.atkinLehnerPerm (eE e)) :
    ∃ 𝓜 : Matching (classSetHeckeData M s Λ R n) X.heckeData,
      𝓜.eE = eE ∧ 𝓜.eV = eV ∧ 𝓜.bad = ∅ := by
  haveI : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  refine ⟨{ eE := eE
            eV := eV
            map_a := ha
            map_b := fun e => ?_
            map_w := hw
            bad := ∅
            away_intertwine := fun ℓ _ x => ?_
            bad_kernel_intertwine := fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ) }, rfl, rfl, rfl⟩
  ·
    rw [ModularCurve.SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm q' K M s X (eE e), ← hAL, ha,
      classSetDegeneracyData_b_eq_a_classSetShift R n hU e]
  · rw [heckeData_T X hX, classSetHeckeData_T M s Λ R n hlaws]
    exact hT ℓ x

end CerednikDrinfeld.AssembleMatching

end

theorem solution
    {a b : ℚ} (M s q' : ℕ) [NeZero M] [Fact s.Prime] [Fact q'.Prime]
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hU : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R)
    (hlaws : ClassSetHeckeLaws M s Λ R n)
    (K : Type) [Field K] [CharP K q'] [DecidableEq K]
    (X : SSLevelDatum q' K M s)
    [Fintype ↥(ssPlaces q' (M * s) K)] [Fintype ↥(ssPlaces q' M K)] [DecidableEq ↥(ssPlaces q' M K)]
    (hX : X.HeckeLaws)
    (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃ ↥(ssPlaces q' (M * s) K))
    (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' M K))
    (ha : ∀ e, X.degeneracyData.a (eE e) = eV ((classSetDegeneracyData R n).a e))
    (hw : ∀ e, X.degeneracyData.w (eE e) = (classSetDegeneracyData R n).w e)
    (hT : ∀ (ℓ : Nat.Primes) (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ),
      (X.edgeHecke ℓ).mulVecLin (x ∘ eE.symm) = ((classSetEdgeHecke M s Λ R n ℓ).mulVecLin x) ∘ eE.symm)
    (hAL : ∀ e, eE (classSetShift _ n e) = X.atkinLehnerPerm (eE e)) :
    ∃ 𝓜 : Matching (classSetHeckeData M s Λ R n) X.heckeData,
      𝓜.eE = eE ∧ 𝓜.eV = eV ∧ 𝓜.bad = ∅ :=
  CerednikDrinfeld.AssembleMatching.main M s q' Λ R n hU hlaws K X hX eE eV ha hw hT hAL

end S_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData
end P2MW
export P2MW.S_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData (solution)
