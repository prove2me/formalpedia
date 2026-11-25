-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.jet_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:27.472521+00:00
-- url     : https://prove2.me/submissions/558d88e3-6d44-4704-a555-a18c6aa48879

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_dVar_eq_pderiv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_C
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_smul_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace VP
private theorem jetAt0_zero_left' {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  simp [jetAt0]
private theorem jetAt0_finset_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left']
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]
variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}
end VP
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv C (e w) G) := by
  rw [Finset.mul_sum, jetAt0_finset_sum_left, jet_sum_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, jet_mul_X, jet_mul_C, jet_smul_right, dVar_eq_pderiv]
end Formalism.L2.FormalSeriesBounds.VP
