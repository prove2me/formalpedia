-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.const_mem_type_set_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:07.175418+00:00
-- url     : https://prove2.me/submissions/17e60c5b-ffb5-4fc6-b97c-e2dfba62f74b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_constantCoeff_sg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
section TyS
variable {l : ℕ} (hl : 2 ≤ l)
include hl
end TyS
section Repar
end Repar
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
private theorem ge_zero_lemma (V : VF C) : V.Ge 0 (0 : C) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top
end RawChart
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) (ζ : JJ I g → C) (hζ : ∀ q, V.Ge 0 (ζ q)) :
    const0 (Sum.elim 0 ζ) ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hinl : ∀ c : I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = 0 := by
    intro c
    rw [show (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = fun _ => (0 : C) by
      funext s
      simp [const0]]
    exact tyS_zero
  have hinr : ∀ q : JJ I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inr q : I g ⊕ JJ I g)) =
      ζ q • PowerSeries.X := by
    intro q
    refine tyS_eq hl _ _ (fun s => ?_) (fun m hm => ?_)
    · cases s with
      | zero => simp [const0]
      | succ s =>
        have h1 : 1 < V.l ^ (s + 1) :=
          calc 1 < V.l := by omega
            _ = V.l ^ 1 := (pow_one _).symm
            _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hl1 : V.l ≠ 1 := by omega
        simp [const0, PowerSeries.coeff_X, h1.ne', hl1]
    · have hm1 : m ≠ 1 := fun h => hm 0 (by simp [h])
      simp [PowerSeries.coeff_X, hm1]
  refine ⟨fun _ => 0, fun q => ζ q • PowerSeries.X, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    refine ⟨by simp, fun n => ?_⟩
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_X]
    split_ifs
    · simpa using hζ q
    · simpa using ge_zero_lemma V
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [hinl]
  · intro q
    rw [hinr, alongCv_zero (X.constantCoeff_sg hh _)]
    simp [hinl]
end Formalism.L2.FormalSeriesBounds.RawChart
