-- Prove2me | solution 1 for EditGV897.Main.main_programs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:26.249274+00:00
-- url     : https://prove2.me/submissions/165f237b-b5c6-4d21-89cf-637a59000dee

import Theorems.Thm_EditGV897_Main_constructor_program
import Theorems.Thm_EditGV897_Main_codec_input_programs

import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Closure

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
 theorem Runs.mono {P : Program} {input output : List Bool} {s t : ℕ}
    (h : Runs P input output s) (hst : s ≤ t) : Runs P input output t := by
  obtain ⟨k, hk, c, hc, hhalt, hout⟩ := h
  exact ⟨k, hk.trans hst, c, hc, hhalt, hout⟩




 theorem main_program_runtime (t : ℕ) (ht : 1 ≤ t) :
    ∃ (constructor encoder decoder : Program) (A d : ℕ), 0 < A ∧
      ∀ n : ℕ, 1 ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        (parametersCode P).length ≤ polyBudget A d n ∧
        Runs constructor (unary n) (parametersCode P) (polyBudget A d n) ∧
        (∀ u : Word (messageLength P),
          Runs encoder (editEncoderInput P u) (wordCode (encodeWord F P u)) (polyBudget A d n)) ∧
        (∀ y : List Bit, y.length ≤ n + t →
          Runs decoder (editDecoderInput P y) (bitCode ((decodeList t P y).getD []))
            (polyBudget A d n)) := by
  obtain ⟨constructor,cc,dc,hcc,hc⟩ := constructor_program t
  obtain ⟨encoder,decoder,ce,de,cd,dd,hce,hcd,hcodec⟩ := codec_input_programs t
  let S := fun n => (parametersCode (setup t n)).length
  have hS (n : ℕ) : S n ≤ cc*(n+1)^dc := (hc n).1
  have hSpoly : Cslib.PolynomiallyBounded S :=
    (show Cslib.PolynomiallyBounded (fun n => cc*(n+1)^dc) by fun_prop).mono_of_le hS
  let B := fun n => S n+3*n+2*t+3
  let H := fun n => S n + cc*(n+1)^dc + ce*(B n)^de + cd*(B n)^dd + 1
  have hHpoly : Cslib.PolynomiallyBounded H := by dsimp [H,B]; fun_prop
  obtain ⟨A,d,hH⟩ := Cslib.polynomiallyBounded_iff_le.mp hHpoly
  have hfinal (n : ℕ) : H n ≤ polyBudget (A+1) d n :=
    (hH n).trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨constructor,encoder,decoder,A+1,d,by omega,?_⟩
  intro n hn
  let P := setup t n
  have hparams : S n ≤ H n := by dsimp [H]; omega
  have hconstructor := (hc n).2
  have hcb : polyBudget cc dc n ≤ H n := by dsimp [polyBudget,H]; omega
  refine ⟨hparams.trans (hfinal n),hconstructor.mono (hcb.trans (hfinal n)),?_,?_⟩
  · intro u
    have hrun := (hcodec n P).1 u
    have hK : messageLength P ≤ n := by unfold messageLength; omega
    have hlen : (editEncoderInput P u).length+1 ≤ B n := by
      simp only [editEncoderInput,List.length_append,unary,List.length_replicate,List.length_singleton,
        frame,wordCode,bitCode,List.length_map,wordList,DeletionHash.MixedEdit.letters,List.length_ofFn]
      dsimp [B,S,P] at *
      omega
    have hb : polyBudget ce de (editEncoderInput P u).length ≤ ce*(B n)^de :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    have hceH : ce*(B n)^de ≤ H n := by dsimp [H]; omega
    exact hrun.mono (hb.trans (hceH.trans (hfinal n)))
  · intro y hy
    have hrun := (hcodec n P).2 y
    have hlen : (editDecoderInput P y).length+1 ≤ B n := by
      simp only [editDecoderInput,List.length_append,unary,List.length_replicate,List.length_singleton,
        frame,bitCode,List.length_map]
      dsimp [B,S,P] at *
      omega
    have hb : polyBudget cd dd (editDecoderInput P y).length ≤ cd*(B n)^dd :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    have hcdH : cd*(B n)^dd ≤ H n := by dsimp [H]; omega
    exact hrun.mono (hb.trans (hcdH.trans (hfinal n)))

end EditGV897.Main

open EditGV897.Main
theorem solution (t : ℕ) (ht : 1 ≤ t) :
    ∃ (constructor encoder decoder : Program) (A d : ℕ), 0 < A ∧
      ∀ n : ℕ, 1 ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        (parametersCode P).length ≤ polyBudget A d n ∧
        Runs constructor (unary n) (parametersCode P) (polyBudget A d n) ∧
        (∀ u : Word (messageLength P),
          Runs encoder (editEncoderInput P u) (wordCode (encodeWord F P u)) (polyBudget A d n)) ∧
        (∀ y : List Bit, y.length ≤ n + t →
          Runs decoder (editDecoderInput P y) (bitCode ((decodeList t P y).getD []))
            (polyBudget A d n)) := EditGV897.Main.main_program_runtime t ht