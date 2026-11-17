-- Prove2me | solution 1 for DetANN.HPIM.hpim_query_program
-- status  : ACCEPTED   (disprove)
-- author  : @milia
-- created : 2026-11-16T19:17:38.65548+00:00
-- url     : https://prove2.me/submissions/bfd2227d-01b1-4ba0-9063-408000a3f44f

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout

/-!
# `hpim_query_program` is false as stated

The layout does not store the number `n` of local points of a node. One integer memory stores both
`T0` (`n = 0`) and `T1` (`n = 1`, child `single 5`), whose lookup `Z_0 = leaf (some 0)` is the same. The
search gives `0` on `T0` (the answer is out of range) and `5` on `T1`, but a deterministic program has
one run on the common query state, and a halted run stutters, so its pointer register `0` cannot be both.
-/

namespace DetANN.HPIM.QDis

open DetANN.HPIM

/-- Integer memory: one inner node at 10 with `M = 1`, `t₀ = 0`, `Z_0 = leaf (some 0)`. -/
def imem : ℤ → ℤ := fun z =>
  if z = 1 then 1 else if z = 2 then 10 else if z = 3 then 100 else if z = 100 then 1 else
  if z = 10 then 1 else if z = 11 then 1 else if z = 12 then 20 else if z = 13 then 30 else
  if z = 14 then 40 else if z = 15 then 80 else if z = 16 then 0 else if z = 20 then 60 else
  if z = 60 then 0 else if z = 61 then 1 else if z = 30 then 7 else if z = 40 then 70 else
  if z = 70 then 0 else if z = 71 then 5 else if z = 80 then 0 else
  if z = 81 then 0 else 0

noncomputable def st : PNormReg.State := ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, imem, 0, false, 0⟩

def Zs : Fin 1 → BoxTree 1 := fun _ => .leaf (some 0)

/-- `n = 0`: the answer `0` of `Z_0` is out of range, so the search returns `0`. -/
def T0 : HTree 1 := .node 0 1 0 Zs Fin.elim0 Fin.elim0 (.single 0)
/-- `n = 1`: the answer `0` leads to the child `single 5`. -/
def T1 : HTree 1 := .node 1 1 0 Zs (fun _ => 7) (fun _ => .single 5) (.single 0)

lemma zs_at : ∀ i : Fin 1, BoxTreeAt 1 st (st.integerMemory (st.integerMemory (10 + 2) + i)) (Zs i) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact BoxTreeAt.leaf _ _ (by simp [st, imem]) (by simp [st, imem])

lemma reps_at : HTreeAt 1 st (st.integerMemory (10 + 5)) (.single 0) :=
  HTreeAt.single _ _ (by simp [st, imem]) (by simp [st, imem])

lemma pow_tab : ∀ t ≤ (0 : ℕ), st.integerMemory (st.integerMemory 3 + t) = 2 ^ t := by
  intro t ht
  have : t = 0 := by omega
  subst this; simp [st, imem]

lemma T0_at : HTreeAt 1 st (st.integerMemory 2) T0 := by
  have h2 : st.integerMemory 2 = 10 := by simp [st, imem]
  rw [h2]
  exact HTreeAt.node 10 0 1 0 Zs Fin.elim0 Fin.elim0 (.single 0) (by simp [st, imem])
    (by simp [st, imem]) (by simp [st, imem]) pow_tab zs_at (fun i => i.elim0) (fun i => i.elim0) reps_at

lemma T1_at : HTreeAt 1 st (st.integerMemory 2) T1 := by
  have h2 : st.integerMemory 2 = 10 := by simp [st, imem]
  rw [h2]
  refine HTreeAt.node 10 1 1 0 Zs (fun _ => 7) (fun _ => .single 5) (.single 0) (by simp [st, imem])
    (by simp [st, imem]) (by simp [st, imem]) pow_tab zs_at ?_ ?_ reps_at
  · intro i; have hi : i = 0 := Subsingleton.elim _ _; subst hi; simp [st, imem]
  · intro i; have hi : i = 0 := Subsingleton.elim _ _; subst hi
    exact HTreeAt.single _ _ (by simp [st, imem]) (by simp [st, imem])

lemma search_T0 (q : Fin 1 → ℝ) : T0.search q = 0 := by
  simp [T0, HTree.search, lookup, Zs, BoxTree.eval]

lemma search_T1 (q : Fin 1 → ℝ) : T1.search q = 5 := by
  simp [T1, HTree.search, lookup, Zs, BoxTree.eval]

lemma run_halted_stable (P : PNormReg.Program) (s₀ : PNormReg.State) (ω : ℕ → Bool) (t : ℕ)
    (h : (PNormReg.run P s₀ ω t).halted = true) : ∀ k, PNormReg.run P s₀ ω (t + k) = PNormReg.run P s₀ ω t := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have : PNormReg.run P s₀ ω (t + (k + 1)) = PNormReg.step P ω (PNormReg.run P s₀ ω (t + k)) := by
      simp only [PNormReg.run, ← add_assoc, Function.iterate_succ_apply']
    rw [this, ih]
    simp [PNormReg.step, h]

/-- The published statement of `hpim_query_program` is false. -/
theorem not_hpim_query_program :
    ¬ ∃ Qry : PNormReg.Program, DetProgram Qry ∧ ∃ c₀ : ℕ,
      ∀ (m : ℕ) (s : PNormReg.State) (T : HTree m) (q : EuclideanSpace ℝ (Fin m)),
        1 ≤ m → s.integerMemory 1 = m → HTreeAt m s (s.integerMemory 2) T →
        ∃ t : ℕ,
          (PNormReg.run Qry (queryState m s q) detTape t).halted = true ∧
          (PNormReg.run Qry (queryState m s q) detTape t).work ≤ c₀ * (m + 1) * T.cost q ∧
          (PNormReg.run Qry (queryState m s q) detTape t).core.ptrs 0 = T.search q := by
  rintro ⟨Qry, -, c₀, h⟩
  have hm1 : st.integerMemory 1 = (1 : ℕ) := by simp [st, imem]
  obtain ⟨t0, h0, -, p0⟩ := h 1 st T0 0 le_rfl hm1 T0_at
  obtain ⟨t1, h1, -, p1⟩ := h 1 st T1 0 le_rfl hm1 T1_at
  have e0 := run_halted_stable Qry (queryState 1 st 0) detTape t0 h0 t1
  have e1 := run_halted_stable Qry (queryState 1 st 0) detTape t1 h1 t0
  rw [add_comm] at e1
  rw [e1] at e0
  rw [← e0, p1] at p0
  rw [search_T0, search_T1] at p0
  norm_num at p0

end DetANN.HPIM.QDis

open DetANN DetANN.HPIM in
theorem solution :
    ¬ ∃ Qry : PNormReg.Program, DetProgram Qry ∧ ∃ c₀ : ℕ,
      ∀ (m : ℕ) (s : PNormReg.State) (T : HTree m) (q : EuclideanSpace ℝ (Fin m)),
        1 ≤ m → s.integerMemory 1 = m → HTreeAt m s (s.integerMemory 2) T →
        ∃ t : ℕ,
          (PNormReg.run Qry (queryState m s q) detTape t).halted = true ∧
          (PNormReg.run Qry (queryState m s q) detTape t).work ≤ c₀ * (m + 1) * T.cost q ∧
          (PNormReg.run Qry (queryState m s q) detTape t).core.ptrs 0 = T.search q :=
  DetANN.HPIM.QDis.not_hpim_query_program
