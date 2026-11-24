-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.card_quot_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:11.426927+00:00
-- url     : https://prove2.me/submissions/e114f21f-e862-49ca-a467-522da04f2fdb

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

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
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
open TensorProduct
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [hP : P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
