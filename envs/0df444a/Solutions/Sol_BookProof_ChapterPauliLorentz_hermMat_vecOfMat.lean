-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.hermMat_vecOfMat
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:29.665981+00:00
-- url     : https://prove2.me/submissions/6dce0335-7c8a-4b48-89ce-ca8e9ca6cf77

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.hermMat_vecOfMat
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) :
    hermMat (vecOfMat H) = H := by

  unfold hermMat vecOfMat;
  ext i j; fin_cases i <;> fin_cases j <;> simp [ Complex.ext_iff ];
  · exact ⟨ by ring, by
    have := congr_fun ( congr_fun hH 0 ) 0; norm_num [ Complex.ext_iff ] at this; linarith ⟩;
  · have := congr_fun ( congr_fun hH 1 ) 0;    norm_num [ Complex.ext_iff ] at this; constructor <;>
      linarith;
  · have := congr_fun ( congr_fun hH 0 ) 1;    norm_num [ Complex.ext_iff ] at this; constructor <;>
      linarith;
  · have := congr_fun ( congr_fun hH 1 ) 1;    norm_num [ Complex.ext_iff ] at this; constructor <;>
      linarith;
