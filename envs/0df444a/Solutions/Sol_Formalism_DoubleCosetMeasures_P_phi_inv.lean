-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.phi_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:52.469801+00:00
-- url     : https://prove2.me/submissions/c45deb9c-bb6a-456e-be14-562ddc46cf3c

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_sLow_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_sUp_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (hIntInv : IntInv) (hIsoInv : IsoInv) (hSA : SimpleAdd)
    {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    ∀ a ∈ intSub R (lowW K s t), ∀ b ∈ intSub R (upUniG K s.sum), ∀ x : lowW K s t,
      ∀ y : upUniG K s.sum, phi R s t ψ C e lam (a * x, y * b) = phi R s t ψ C e lam (x, y) := by
  intro a ha b hb x y
  have haI : IsInt R (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := ha.1
  have hbI : IsInt R (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := hb.1
  have haL : IsLowUni (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := a.2.1
  have hxL : IsLowUni (((x : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := x.2.1
  have hbU : IsUpUni (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := b.2
  have hyU : IsUpUni (((y : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := y.2
  unfold phi
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hM : ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
        (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
          ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
      ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
          ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) *
        ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
    simp only [Matrix.mul_assoc]
  rw [(hSA K _ _ _).1 haL hxL, (hSA K _ _ _).2 hyU hbU]
  have hI : IsInt R (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) ↔ IsInt R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    rw [hM]; exact hIntInv K R _ _ _ _ haL hbU haI hbI
  have hC : Nat.card (isoSet R (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) C e lam) =
      Nat.card (isoSet R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) C e lam) := by
    rw [hM]; exact hIsoInv K R _ _ _ _ haL hbU haI hbI C e lam
  have hψ' : ψ (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + (sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) = ψ (sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    rw [show sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + (sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
        (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) + (sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) by ring,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψ (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)),
      hψ _ (sLow_mem R _ haI), hψ _ (sUp_mem R _ hbI), one_mul, one_mul]
  rw [hψ']
  congr 1
  by_cases h : IsInt R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))
  · rw [if_pos (hI.2 h), if_pos h, hC]
  · rw [if_neg (fun h' => h (hI.1 h')), if_neg h]
end Formalism.DoubleCosetMeasures.P
