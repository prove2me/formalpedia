-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_aQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:52:43.412815+00:00
-- url     : https://prove2.me/submissions/52392a7d-6423-4693-9d42-2d8df53a2f00

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aPsi_basis
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aPsi_eq_zero_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_quot_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
variable {R : Type*} [CommRing R] {V A B W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup W] [Module R W] {ι κ : Type*} [DecidableEq κ] {φ : κ → Type*}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (b : Basis ι R V) (s t : Set ι) (hst : s ⊆ t) (c : Basis ↥s R W) (P Q : Submodule R V)
    (hP : P = Submodule.span R (b '' t)) (hQ : Q = Submodule.span R (b '' (t \ s))) :
    ∃ Phi : (↥P ⧸ Q.comap P.subtype) ≃ₗ[R] W,
      ∀ (x : ↥P) (i : ι) (hi : i ∈ s), x.1 = b i → Phi (Submodule.Quotient.mk x) = c ⟨i, hi⟩ := by
  subst hP hQ
  have hker : LinearMap.ker (qb_aPsi b s c ∘ₗ (Submodule.span R (b '' t)).subtype) =
      (Submodule.span R (b '' (t \ s))).comap (Submodule.span R (b '' t)).subtype := by
    ext x
    have hx : ((b.repr x.1).support : Set ι) ⊆ t := (Basis.mem_span_image b).1 x.2
    rw [LinearMap.mem_ker, Submodule.mem_comap, Basis.mem_span_image]
    constructor
    · intro h y hy
      exact ⟨hx hy, fun hy' => (Finsupp.mem_support_iff.1 hy) ((qb_aPsi_eq_zero_iff b s c x.1).1 h y hy')⟩
    · intro h
      refine (qb_aPsi_eq_zero_iff b s c x.1).2 fun y hy => ?_
      by_contra hne
      exact (h (Finsupp.mem_support_iff.2 hne)).2 hy
  have hsurj : Function.Surjective (qb_aPsi b s c ∘ₗ (Submodule.span R (b '' t)).subtype) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← c.span_eq, Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact ⟨⟨b y, Submodule.subset_span ⟨y, hst hy, rfl⟩⟩, qb_aPsi_basis b s c y hy⟩
  obtain ⟨Phi, hPhi⟩ := qb_quot_equiv _ hsurj _ hker
  refine ⟨Phi, fun x i hi hx => ?_⟩
  rw [hPhi, LinearMap.comp_apply, Submodule.subtype_apply, hx, qb_aPsi_basis b s c i hi]
end Formalism.InvariantFactorPaths.ColumnFamilies
