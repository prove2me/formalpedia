-- Prove2me | solution 1 for Erdos20.f_0_1
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-09-26T15:50:13.393159+00:00
-- url     : https://prove2.me/submissions/d529410a-0dc5-49a3-b093-4c153b57ac12

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted from `Erdos20.f_0_1` in Formal Conjectures:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/20.lean
The only imported project module supplies the platform's definitions.
-/
import Definitions.Def_Erdos20_defs

/-- A first verified supporting lemma for the sunflower mission. -/
theorem solution : Erdos20.f 0 1 = 1 := by
  refine IsLeast.csInf_eq ⟨fun F hF ↦ ?_, fun n hn ↦ n.pos_of_ne_zero fun hn₀ ↦ ?_⟩
  · obtain ⟨A, hA⟩ :=
      F.nonempty_of_ncard_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hF.2))
    exact ⟨{A}, by simpa using ⟨hA, Erdos20.isSunflower_singleton _⟩⟩
  · obtain ⟨S, hS⟩ := hn (α := ℕ) {} (by simpa)
    simp_all [bot_unique hS.1]
