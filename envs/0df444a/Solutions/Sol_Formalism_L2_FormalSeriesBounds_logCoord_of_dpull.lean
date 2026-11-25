-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.logCoord_of_dpull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:32.587868+00:00
-- url     : https://prove2.me/submissions/70d358f3-30a6-4668-af7f-764d2b116766

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_jet_list
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_pullPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_C
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_jet_mul_C

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
private theorem jetAt0_one_eq_constantCoeff {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, jet_C, one_mul]
private theorem jetAt0_C_mul' {σ : Type} (a : C) (q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a * q) G = a * jetAt0 q G := by
  rw [mul_comm, jet_mul_C]
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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)} (hD : DPullSt Y p) :
    LogCoordSt Y p := by
  classical
  intro n ι _ cp uv P Q hQ F
  obtain ⟨co, hco, rfl⟩ := hQ
  have hcc : ∀ H : PS C n dd, MvPowerSeries.constantCoeff (pullN Y p H) = MvPowerSeries.constantCoeff H :=
    fun H => VP.cc_subst_eq (fun q => VP.cc_pullPt (Y := Y) (p := p) q) H
  have hmon : ∀ m ∈ P.support, MvPowerSeries.constantCoeff (DmonN (Y.B.FK C) cp uv m F) =
      jetAt0 (∏ ℓ, (∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) ^ m ℓ) (pullN Y p F) := by
    intro m hm
    have hv : ∀ ℓ ∈ (Finset.univ : Finset ι).toList, m ℓ ≠ 0 →
        uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2 := fun ℓ _ hℓ =>
      hco ℓ ((MvPolynomial.mem_vars ℓ).2 ⟨m, hm, Finsupp.mem_support_iff.2 hℓ⟩)
    have h1 := VP.jet_list hD cp uv co m F _ hv 1
    rw [one_mul, Finset.prod_map_toList, jetAt0_one_eq_constantCoeff, hcc] at h1
    exact h1
  rw [DpolyN, map_sum, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', VP.jetAt0_finset_sum_left]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, hmon m hm, MvPolynomial.algebraMap_eq, jetAt0_C_mul']
  simp
end Formalism.L2.FormalSeriesBounds
