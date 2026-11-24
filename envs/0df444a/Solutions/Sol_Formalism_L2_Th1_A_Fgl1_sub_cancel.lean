-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.sub_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:37.204289+00:00
-- url     : https://prove2.me/submissions/516acf3d-9681-47f0-9e85-4d3df4564588

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution {f : MvPowerSeries (Fin 2) R}
    (h : f * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = 0) : f = 0 := by
  have key : ∀ e : Fin 2 →₀ ℕ,
      (if Finsupp.single 0 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single 0 1) f else 0) =
      (if Finsupp.single 1 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0) := by
    intro e
    have h1 := congrArg (MvPowerSeries.coeff e) h
    rw [mul_sub, map_sub, map_zero, sub_eq_zero,
      show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 from rfl,
      show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 1 1) 1 from rfl,
      MvPowerSeries.coeff_mul_monomial, MvPowerSeries.coeff_mul_monomial] at h1
    simpa using h1
  let mk : ℕ → ℕ → (Fin 2 →₀ ℕ) := fun a b => Finsupp.single 0 a + Finsupp.single 1 b
  have hall : ∀ b a, MvPowerSeries.coeff (mk a b) f = 0 := by
    intro b
    induction b with
    | zero =>
      intro a
      have h := key (mk (a + 1) 0)
      have hp : Finsupp.single 0 1 ≤ mk (a + 1) 0 := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      have hn : ¬ Finsupp.single 1 1 ≤ mk (a + 1) 0 := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      rw [if_pos hp, if_neg hn] at h
      have e1 : mk (a + 1) 0 - Finsupp.single 0 1 = mk a 0 := by
        ext i
        fin_cases i <;> simp [mk]
      rw [e1] at h
      exact h
    | succ b ih =>
      intro a
      have h := key (mk (a + 1) (b + 1))
      have hp : Finsupp.single 0 1 ≤ mk (a + 1) (b + 1) := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      have hq : Finsupp.single 1 1 ≤ mk (a + 1) (b + 1) := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      rw [if_pos hp, if_pos hq] at h
      have e1 : mk (a + 1) (b + 1) - Finsupp.single 0 1 = mk a (b + 1) := by
        ext i
        fin_cases i <;> simp [mk]
      have e2 : mk (a + 1) (b + 1) - Finsupp.single 1 1 = mk (a + 1) b := by
        ext i
        fin_cases i <;> simp [mk]
      rw [e1, e2, ih (a + 1)] at h
      exact h
  ext e
  have he : e = mk (e 0) (e 1) := by
    ext i
    fin_cases i <;> simp [mk]
  rw [he, hall]
  simp
end Formalism.L2.Th1.A.Fgl1
