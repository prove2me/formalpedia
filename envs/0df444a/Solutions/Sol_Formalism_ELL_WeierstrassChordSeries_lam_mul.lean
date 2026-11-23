-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.lam_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:33.893941+00:00
-- url     : https://prove2.me/submissions/fa49d11d-3509-4467-8e36-e560505208ae

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_eq_single_iff
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_lam
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi
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
namespace WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
section maps
variable {R' : Type*} [CommRing R'] (φ : R →+* R')
end maps
section mem
variable (T : Subring R)
end mem
end Alg
section Fld
variable {F : Type*} [Field F]
end Fld
section Wser
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}
end Wser
section Mser
variable {K : Type u} [Field K]
private theorem coeff_mul_X_fin_two (φ : MvPowerSeries (Fin 2) K) (j : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (φ * MvPowerSeries.X j) =
      if Finsupp.single j 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single j 1) φ else 0 := by
  rw [show (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.monomial (Finsupp.single j 1) 1 from rfl, MvPowerSeries.coeff_mul_monomial]
  try simp only [mul_one]
private theorem single_one_le_iff_ne_zero (j : Fin 2) (e : Fin 2 →₀ ℕ) : Finsupp.single j 1 ≤ e ↔ e j ≠ 0 := by
  first
    | (rw [Finsupp.single_le_iff]
       exact Nat.one_le_iff_ne_zero)
    | (rw [Finsupp.le_def]
       constructor
       · intro h
         have := h j
         simp at this
         omega
       · intro h k
         by_cases hk : j = k
         · subst hk
           simp
           omega
         · simp [Finsupp.single_apply, hk])
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
end Mser
end WeierstrassChordSeries
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (w : PowerSeries K) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam w = Wi w 1 - Wi w 0 := by
  have key : ∀ a b : ℕ, a = b → coeff a w = coeff b w := fun a b h => h ▸ rfl
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (MvPowerSeries.X 1), mul_comm (MvPowerSeries.X 0), coeff_mul_X_fin_two,
    coeff_mul_X_fin_two, coeff_Wi, coeff_Wi, coeff_lam, coeff_lam]
  simp only [(eq_single_iff e).1, (eq_single_iff e).2, single_one_le_iff_ne_zero]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;>
    simp [h0, h1] <;>
    first
      | (apply key; omega)
      | (rw [sub_eq_zero]; apply key; omega)
      | (rw [neg_inj]; apply key; omega)
      | (apply Eq.symm; apply key; omega)
end Formalism.ELL.WeierstrassChordSeries
