-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.L_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:30.71947+00:00
-- url     : https://prove2.me/submissions/24fcf8b8-1a70-41e4-9256-85822e254a38

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (φ ψ : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    (L i) (φ * ψ) = cc φ * (L i) ψ + (L i) φ * cc ψ := by
  first
    | (rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
       simp [Finset.Nat.sum_antidiagonal_succ, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
       try ring
       done)
    | (rw [MvPowerSeries.coeff_mul, Finset.sum_eq_add (0, Finsupp.single i 1) (Finsupp.single i 1, 0)]
       · simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
         try ring
       · simp
       · rintro ⟨a, b⟩ hab hne
         rw [Finset.mem_antidiagonal] at hab
         exfalso
         have hj : ∀ j, a j + b j = (Finsupp.single i 1) j := fun j => by rw [← Finsupp.add_apply, hab]
         by_cases ha : a i = 0
         · apply hne.1
           have a0 : a = 0 := by
             ext j
             have := hj j
             by_cases hij : i = j
             · subst hij
               simp [ha]
             · simp [Finsupp.single_apply, hij] at this
               simp
               omega
           subst a0
           simp at hab
           rw [hab]
         · apply hne.2
           have b0 : b = 0 := by
             ext j
             have := hj j
             by_cases hij : i = j
             · subst hij
               simp at this
               simp
               omega
             · simp [Finsupp.single_apply, hij] at this
               simp
               omega
           subst b0
           simp at hab
           rw [hab]
       · intro h
         exfalso
         apply h
         simp [Finset.mem_antidiagonal]
       · intro h
         exfalso
         apply h
         simp [Finset.mem_antidiagonal]
       done)
end Formalism.ELL.WeierstrassChordSeries
