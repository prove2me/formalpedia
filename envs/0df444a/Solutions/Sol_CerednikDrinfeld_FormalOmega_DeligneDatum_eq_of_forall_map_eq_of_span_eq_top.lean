-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0a372283-cef6-537c-b7e1-eb7359898b44

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open TensorProduct LT.LatticeTree CerednikDrinfeld.FormalOmega

namespace OmegaSepSol

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable (L : Type) [CommRing L] [Algebra B L] [Algebra 𝒪 L] [IsScalarTower 𝒪 B L]

noncomputable def bcMap (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K L M :=
  AlgebraTensorModule.map (Algebra.linearMap B L) LinearMap.id

theorem bcMap_tmul (M : FullLattice 𝒪 K) (b : B) (v : ↥M.1) :
    bcMap L M (b ⊗ₜ[𝒪] v) = algebraMap B L b ⊗ₜ[𝒪] v := by
  simp [bcMap]

theorem bcMap_eq_rTensor (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    bcMap L M x = LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 B L).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => rw [bcMap_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem isBaseChange_bcMap (M : FullLattice 𝒪 K) : IsBaseChange L (bcMap (𝒪 := 𝒪) (K := K) (B := B) L M) := by
  refine IsBaseChange.of_equiv (AlgebraTensorModule.cancelBaseChange 𝒪 B L L (↥M.1)) fun x => ?_
  rw [bcMap_eq_rTensor, cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B L) (fun _ => rfl) M x]

theorem isLocalizedModule_bcMap (S : Submonoid B) [IsLocalization S L] (M : FullLattice 𝒪 K) :
    IsLocalizedModule S (bcMap (𝒪 := 𝒪) (K := K) (B := B) L M) :=
  (isLocalizedModule_iff_isBaseChange S L _).mpr (isBaseChange_bcMap L M)

theorem lineBaseChange_eq_localized' (S : Submonoid B) [IsLocalization S L] (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) L S M
    lineBaseChange (IsScalarTower.toAlgHom 𝒪 B L) M N = N.localized' L S (bcMap L M) := by
  haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) L S M
  rw [Submodule.localized'_eq_span, lineBaseChange]
  have himg : (LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 B L).toLinearMap) '' (N : Set (latticeBaseChange 𝒪 K B M)) =
      (bcMap (𝒪 := 𝒪) (K := K) L M) '' (N : Set (latticeBaseChange 𝒪 K B M)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, bcMap_eq_rTensor L M x⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (bcMap_eq_rTensor L M x).symm⟩
  rw [himg]

end OmegaSepSol

open OmegaSepSol in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    (n : ℕ) (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, Algebra 𝒪 (L i)]
    [∀ i, IsScalarTower 𝒪 B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (d d' : OmegaObj (K := K) π B)
    (h : ∀ i, DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d =
      DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B (L i)) d') : d = d' := by
  classical
  apply DeligneDatum.ext'
  funext M

  have hloc : ∀ i, haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) (L i) (Submonoid.powers (f i)) M
      (d.line M).localized₀ (Submonoid.powers (f i)) (bcMap (L i) M) =
        (d'.line M).localized₀ (Submonoid.powers (f i)) (bcMap (L i) M) := by
    intro i
    haveI := isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) (L i) (Submonoid.powers (f i)) M
    have hM : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (L i)) M (d.line M) =
        lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (L i)) M (d'.line M) :=
      congrArg (fun e : DeligneDatum (K := K) π (L i) => e.line M) (h i)
    rw [lineBaseChange_eq_localized' (L i) (Submonoid.powers (f i)) M,
      lineBaseChange_eq_localized' (L i) (Submonoid.powers (f i)) M] at hM
    rw [← Submodule.restrictScalars_localized' (L i), ← Submodule.restrictScalars_localized' (L i), hM]

  let idx : ↥(Set.range f) → Fin n := fun r => r.2.choose
  have hidx : ∀ r : ↥(Set.range f), f (idx r) = (r : B) := fun r => r.2.choose_spec
  haveI inst : ∀ r : ↥(Set.range f), IsLocalizedModule (Submonoid.powers (r : B)) (bcMap (𝒪 := 𝒪) (K := K) (L (idx r)) M) :=
    fun r => hidx r ▸ isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) (L (idx r)) (Submonoid.powers (f (idx r))) M
  refine Submodule.eq_of_isLocalized₀_span (Set.range f) hf (fun r => latticeBaseChange 𝒪 K (L (idx r)) M)
    (fun r => bcMap (L (idx r)) M) fun r => ?_
  have aux : ∀ (i : Fin n) (b : B) (e : f i = b),
      haveI : IsLocalizedModule (Submonoid.powers b) (bcMap (𝒪 := 𝒪) (K := K) (L i) M) :=
        e ▸ isLocalizedModule_bcMap (𝒪 := 𝒪) (K := K) (L i) (Submonoid.powers (f i)) M
      (d.line M).localized₀ (Submonoid.powers b) (bcMap (L i) M) =
        (d'.line M).localized₀ (Submonoid.powers b) (bcMap (L i) M) := by
    rintro i b rfl
    exact hloc i
  exact aux (idx r) r (hidx r)

#print axioms solution

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_eq_of_span_eq_top (solution)
