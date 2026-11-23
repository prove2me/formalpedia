-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:30.349872+00:00
-- url     : https://prove2.me/submissions/143cec63-8432-42c3-9619-5cdadaf5c0f6

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {M : Type*} [Monoid M]
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    (orderOf (primeToPart ℓ x)).Coprime ℓ := by
  have hn0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  have hm : orderOf x = ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ) :=
    (Nat.ordProj_mul_ordCompl_eq_self (orderOf x) ℓ).symm
  have key : ∀ u : ℕ, (x ^ (ℓ ^ (orderOf x).factorization ℓ * u)) ^
      (orderOf x / ℓ ^ (orderOf x).factorization ℓ) = 1 := fun u => by
    rw [← pow_mul, show ℓ ^ (orderOf x).factorization ℓ * u * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)
      = (ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) * u by ring,
      ← hm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hdvd : orderOf (primeToPart ℓ x) ∣ orderOf x / ℓ ^ (orderOf x).factorization ℓ :=
    orderOf_dvd_of_pow_eq_one (key _)
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_ordCompl hℓ hn0).symm
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
