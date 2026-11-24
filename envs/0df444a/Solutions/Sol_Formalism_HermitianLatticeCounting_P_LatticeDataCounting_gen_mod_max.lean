-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.gen_mod_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:28.352073+00:00
-- url     : https://prove2.me/submissions/b014f2d3-f4ba-4ef0-a3d8-bb5d3cc4e5ad

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
open TensorProduct
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [hP : P.IsMaximal] :
    ∃ s : Fin (Module.finrank R M) → M,
      Submodule.span R (Set.range s) ⊔ P • (⊤ : Submodule R M) = ⊤ := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  have hrk : Module.finrank (R ⧸ P) ((R ⧸ P) ⊗[R] M) = Module.finrank R M := by
    let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
    rw [Module.rankAtStalk_eq_finrank_of_free] at h1
    have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
      rw [Module.rankAtStalk_eq]
      exact Ideal.finrank_fiber_eq_finrank _
    rw [← h2, ← h1]
    rfl
  let b := Module.finBasisOfFinrankEq (R ⧸ P) ((R ⧸ P) ⊗[R] M) hrk
  have hb : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ P) Ideal.Quotient.mk_surjective, b.span_eq]
    rfl
  choose s hs using fun i => Submodule.Quotient.mk_surjective (P • (⊤ : Submodule R M)) (e (b i))
  refine ⟨s, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have h3 : ((P • (⊤ : Submodule R M)).mkQ ∘ s) = e ∘ b := funext hs
  have h4 : Submodule.span R (e '' Set.range b) =
      (Submodule.span R (Set.range b)).map (e : _ →ₗ[R] _) := (Submodule.map_span _ _).symm
  rw [h3, Set.range_comp, h4, hb, Submodule.map_top, LinearMap.range_eq_top]
  exact e.surjective
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
