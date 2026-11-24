-- Prove2me | solution 1 for Formalism.UG.P.covolume_of_dual_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:07:04.439383+00:00
-- url     : https://prove2.me/submissions/eb08ca64-deec-411d-b561-6a41f7950a11

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
import Theorems.Thm_Formalism_UG_P_csCovol_sq_eq_det_gram
import Theorems.Thm_Formalism_UG_P_csCovol_det_le
import Theorems.Thm_Formalism_UG_P_csCovol_int_mult
import Theorems.Thm_Formalism_UG_P_csCovol_mem_zmap
import Theorems.Thm_Formalism_UG_P_csCovol_column

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.CovolOfDual := by
  intro K V _ _ _ _ _ _ _ _ h _ _ N ι hι e he
  obtain ⟨n, hn0, c, hc⟩ := csCovol_int_mult e he
  set D : ℤ := n * discr K with hD
  have hD0 : D ≠ 0 := mul_ne_zero hn0 (NumberField.discr_ne_zero K)
  refine ⟨|(D : ℝ)| ^ N, ?_⟩
  intro M _ hdual _ _
  classical
  have hrank : Module.finrank ℤ (Formalism.HermitianLatticesTheory.zmap ι M) = N := by
    rw [ZLattice.rank ℝ, finrank_euclideanSpace_fin]
  let b := Module.finBasisOfFinrankEq ℤ (Formalism.HermitianLatticesTheory.zmap ι M) hrank
  have hm' : ∀ i, ∃ y ∈ M, ι y = b i := fun i => (csCovol_mem_zmap ι M _).mp (b i).2
  choose m _ hm using hm'
  set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef
  have hsq := csCovol_sq_eq_det_gram _ b
  have hGR : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) =
      (Rat.castHom ℝ).mapMatrix G := by
    ext i k
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hGdef]
    rw [← hm, ← hm, hι]
    rfl
  have hsq' : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 = (G.det : ℝ) := by
    rw [hsq, hGR, ← RingHom.map_det]
    rfl
  clear hsq
  have hsq := hsq'
  have hcov : 0 < ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) := ZLattice.covolume_pos _ _
  have hGpos : 0 < G.det := by
    have : (0 : ℝ) < (G.det : ℝ) := by rw [← hsq]; positivity
    exact_mod_cast this
  have hcol := fun j => csCovol_column h ι hι M b m hm e hdual n c hc hGpos.ne' j
  choose aa haa using hcol
  let P : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun k j => aa j k
  have hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1 := by
    ext i j
    have := congrFun (haa j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [this, hD]
    simp [Pi.single_apply, eq_comm]
  have hle := csCovol_det_le G hGpos D hD0 P hP
  have hleR : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 ≤ |(D : ℝ)| ^ N := by
    rw [hsq]
    have : ((G.det : ℚ) : ℝ) ≤ (((|D| : ℚ) ^ N : ℚ) : ℝ) := by exact_mod_cast hle
    simpa using this
  have hD1 : (1 : ℝ) ≤ |(D : ℝ)| ^ N := by
    apply one_le_pow₀
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD0
    exact_mod_cast this
  nlinarith
end Formalism.UG.P
