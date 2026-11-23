-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.lit_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:08.161923+00:00
-- url     : https://prove2.me/submissions/bc576500-d5b9-4cdf-9a19-ebd76ebf75e6

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_formalSum
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_ne_zero_of_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace CubeThreeAlt
open WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
end Alg
section Mser
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
private theorem hasSubst_of_cc_zero_lemma {τ : Type} [Finite τ] {a : τ → MvPowerSeries σ K} (ha : ∀ i, cc (a i) = 0) :
    MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
variable {w : PowerSeries K}
end Mser
end CubeThreeAlt
end Formalism.ELL
namespace Formalism.ELL
open CubeThreeAlt WeierstrassChordSeries
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
variable {w : PowerSeries K}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (hw : WFixed W w) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
      (F2 W w) ≠ 0 ∧
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
      (F2 W w) ≠ MvPowerSeries.X 2 ∧
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ MvPowerSeries.X 1 := by
  classical
  have hX01 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ MvPowerSeries.X 1 := by
    intro h
    have h' := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
    rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg] at h'
    · exact one_ne_zero h'
    · intro h2
      exact absurd ((Finsupp.single_left_inj one_ne_zero).mp h2) (by decide)
  have hb0 : ∀ i, cc ((![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) i) = 0 := by
    intro i
    fin_cases i <;> simp
  have ha0 : ∀ i, cc ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) i) = 0 := by
    intro i
    fin_cases i <;> simp
  have hb : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K) :=
    hasSubst_of_cc_zero_lemma hb0
  have ha : MvPowerSeries.HasSubst (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) :=
    hasSubst_of_cc_zero_lemma ha0
  have hid : (fun i : Fin 2 => MvPowerSeries.subst
      (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) K) i)) = MvPowerSeries.X := by
    funext i
    fin_cases i <;> simp [MvPowerSeries.subst_X hb]
  have key : MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] (Formalism.ELL.WeierstrassChordSeries.F2 W w))
      = Formalism.ELL.WeierstrassChordSeries.F2 W w := by
    rw [MvPowerSeries.subst_comp_subst_apply ha hb]
    rw [hid]
    exact congrFun MvPowerSeries.subst_self (Formalism.ELL.WeierstrassChordSeries.F2 W w)
  have hF : Formalism.ELL.WeierstrassChordSeries.F2 W w ≠ 0 :=
    Formalism.ELL.WeierstrassChordSeries.ne_zero_of_L (i := 0) (by rw [Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw]; exact one_ne_zero)
  have hX2 : MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0 := by
    simp [MvPowerSeries.subst_X hb]
  refine ⟨fun h => hF ?_, fun h => hF ?_, hX01⟩
  · rw [← key, h, ← MvPowerSeries.coe_substAlgHom hb, map_zero]
  · rw [← key, h, hX2]
end Formalism.ELL.CubeThreeAlt
