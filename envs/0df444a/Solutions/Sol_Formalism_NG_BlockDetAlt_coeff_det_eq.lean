-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.coeff_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:21.331207+00:00
-- url     : https://prove2.me/submissions/7b0620b6-1c12-4761-9b01-b1089be9899d

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Theorems.Thm_Formalism_NG_BlockDetAlt_coeff_det_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (a : Matrix d d (PowerSeries (X' → FractionRing O))) (ha : a ∈ goodM R') (n : ℕ) (x' : X') :
    PowerSeries.coeff n a.det x' = PowerSeries.coeff (n + Fintype.card d) (psi (n + Fintype.card d)
      (Matrix.det (∑ j : Fin (n + Fintype.card d),
        (MvPolynomial.X j : MvPolynomial _ (FractionRing O)) •
          (((⟨coefMat j.1 a, ha j.1⟩ : R') : X' → Matrix d d (FractionRing O)) x').map
            MvPolynomial.C))) := by
  classical
  have hL : PowerSeries.coeff n a.det x' =
      PowerSeries.coeff n ((PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix a).det := by
    rw [← RingHom.map_det, PowerSeries.coeff_map]
    rfl
  have hmat : (psi (n + Fintype.card d)).mapMatrix (∑ j : Fin (n + Fintype.card d),
      (MvPolynomial.X j : MvPolynomial _ (FractionRing O)) •
        (((⟨coefMat j.1 a, ha j.1⟩ : R') : X' → Matrix d d (FractionRing O)) x').map MvPolynomial.C) =
      (PowerSeries.X : PowerSeries (FractionRing O)) • ∑ j : Fin (n + Fintype.card d),
        (PowerSeries.X : PowerSeries (FractionRing O)) ^ j.1 • (coefMat j.1 a x').map PowerSeries.C := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, psi, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hL, RingHom.map_det, hmat, Matrix.det_smul, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    Nat.add_sub_cancel]
  symm
  apply coeff_det_congr
  intro i j k hk
  have hd0 : 0 < Fintype.card d := Fintype.card_pos_iff.2 ⟨i⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    RingHom.mapMatrix_apply, PowerSeries.coeff_map]
  rw [Finset.sum_eq_single ⟨k, by omega⟩]
  · rw [mul_comm, PowerSeries.coeff_C_mul_X_pow, if_pos rfl]
    rfl
  · intro b _ hb
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow, if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.NG.BlockDetAlt
