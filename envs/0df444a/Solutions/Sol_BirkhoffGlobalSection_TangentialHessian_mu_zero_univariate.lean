-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.mu_zero_univariate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T17:35:15.629613+00:00
-- url     : https://prove2.me/submissions/b0ef687e-f824-401d-b125-9b949a57c767

import Definitions.Def_BirkhoffGlobalSection_IntervalChecker_Dense
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace BirkhoffGlobalSection.TangentialHessian.Checker.Mu0
open Checker NP
set_option maxRecDepth 100000
noncomputable section

def mu0_goals : List (Poly Dy) := [[((⟨224, 0⟩ : Dy), [7, 0, 0]), ((⟨-224, 0⟩ : Dy), [5, 1, 0]), ((⟨148, 0⟩ : Dy), [4, 0, 0]), ((⟨24, 0⟩ : Dy), [3, 2, 0]), ((⟨-20, 0⟩ : Dy), [2, 1, 0]), ((⟨-4, 0⟩ : Dy), [1, 0, 0]), ((⟨1, 0⟩ : Dy), [0, 2, 0])],
  [((⟨-180224, 0⟩ : Dy), [14, 0, 0]), ((⟨352768, 0⟩ : Dy), [12, 1, 0]), ((⟨-175616, 0⟩ : Dy), [11, 0, 0]), ((⟨-254976, 0⟩ : Dy), [10, 2, 0]), ((⟨251904, 0⟩ : Dy), [9, 1, 0]), ((⟨79616, 0⟩ : Dy), [8, 3, 0]), ((⟨-62832, 0⟩ : Dy), [8, 0, 0]), ((⟨-115968, 0⟩ : Dy), [7, 2, 0]), ((⟨-8448, 0⟩ : Dy), [6, 4, 0]), ((⟨58080, 0⟩ : Dy), [6, 1, 0]), ((⟨13824, 0⟩ : Dy), [5, 3, 0]), ((⟨-10400, 0⟩ : Dy), [5, 0, 0]), ((⟨288, 0⟩ : Dy), [4, 5, 0]), ((⟨-7944, 0⟩ : Dy), [4, 2, 0]), ((⟨-480, 0⟩ : Dy), [3, 4, 0]), ((⟨1696, 0⟩ : Dy), [3, 1, 0]), ((⟨280, 0⟩ : Dy), [2, 3, 0]), ((⟨16, 0⟩ : Dy), [2, 0, 0]), ((⟨-72, 0⟩ : Dy), [1, 2, 0]), ((⟨1, 0⟩ : Dy), [0, 4, 0])]]

def mu0_box : List (Iv Dy) := [((⟨0, 0⟩ : Dy), (⟨5, 4⟩ : Dy)), ((⟨1127428915, 29⟩ : Dy), (⟨2254858905, 30⟩ : Dy))]

def mu0_tree : Tree Dy := (.node 0 (.leaf .ok (⟨1, 0⟩ : Dy) (⟨1, 0⟩ : Dy)) (.leaf .ok (⟨1, 0⟩ : Dy) (⟨1, 0⟩ : Dy)))

def mu0_cert : Cert Dy (DPoly Dy) where
  box := mu0_box
  rSq := ⟨2, NP.ofFlat 2 [((⟨1, 0⟩ : Dy), [0, 0])]⟩
  hyps := []
  goals := mu0_goals.map fun p => ⟨3, NP.ofFlat 3 p⟩
  tree := mu0_tree

end

theorem mu0_check : check NP.centredEnc mu0_cert = true := by decide +kernel

end BirkhoffGlobalSection.TangentialHessian.Checker.Mu0

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (Z c : ℝ) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 3 / 10)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    0 < (224 * Z ^ 7 - 224 * c * Z ^ 5 + 148 * Z ^ 4 + 24 * c ^ 2 * Z ^ 3 - 20 * c * Z ^ 2 - 4 * Z + c ^ 2) ∧ 16 * Z * (60 * Z ^ 5 - 44 * c * Z ^ 3 + 24 * Z ^ 2 + 3 * c ^ 2 * Z - 2 * c) ^ 2 * (1 - 2 * c * Z + 4 * Z ^ 3) < (224 * Z ^ 7 - 224 * c * Z ^ 5 + 148 * Z ^ 4 + 24 * c ^ 2 * Z ^ 3 - 20 * c * Z ^ 2 - 4 * Z + c ^ 2) ^ 2 := by
  have hflat : ∀ (n : ℕ) (p : Checker.Poly Checker.Dy) (x : List ℝ), x.length = n →
      Checker.NP.DPoly.eval (⟨n, Checker.NP.ofFlat n p⟩ : Checker.NP.DPoly Checker.Dy) x =
        Checker.evalR p x := fun n p x h => Checker.NP.eval_ofFlat n p x h
  have hx : Checker.InBox [Z, c] Checker.Mu0.mu0_cert.box := by
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil) <;>
    · unfold Checker.Mem; simp only [Checker.Dy.cnum_toReal_mk]
      constructor <;> norm_num <;> linarith
  have hr2' : (1 : ℝ) ^ 2 = Checker.NP.DPoly.eval Checker.Mu0.mu0_cert.rSq [Z, c] := by
    show (1 : ℝ) ^ 2 = Checker.NP.DPoly.eval ⟨2, Checker.NP.ofFlat 2 _⟩ _
    rw [hflat 2 _ _ rfl]; simp [Checker.evalR, Checker.monoR]
  have hg := Checker.check_sound Checker.NP.centredEnc_sound Checker.Mu0.mu0_cert
    Checker.Mu0.mu0_check _ hx 1 one_pos hr2' (by simp [Checker.Mu0.mu0_cert])
  have hP := hg _ (List.mem_map_of_mem List.mem_cons_self)
  have hW := hg _ (List.mem_map_of_mem (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [hflat 3 _ _ rfl] at hP hW
  constructor
  · convert hP using 1; simp [Checker.evalR, Checker.monoR]; ring
  · have : 0 < (224 * Z ^ 7 - 224 * c * Z ^ 5 + 148 * Z ^ 4 + 24 * c ^ 2 * Z ^ 3 - 20 * c * Z ^ 2 - 4 * Z + c ^ 2) ^ 2 - 16 * Z * (60 * Z ^ 5 - 44 * c * Z ^ 3 + 24 * Z ^ 2 + 3 * c ^ 2 * Z - 2 * c) ^ 2 * (1 - 2 * c * Z + 4 * Z ^ 3) := by
      convert hW using 1; simp [Checker.evalR, Checker.monoR]; ring
    linarith
