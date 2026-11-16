-- Prove2me | solution 1 for DetANN.reloc_sim_cells
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:47:05.134304+00:00
-- url     : https://prove2.me/submissions/55900cc7-d6e5-4541-bb2a-eb8223daa600

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_PNormRegLib_step_eq_exec
import Theorems.Thm_PNormRegLib_bounded_run
import Theorems.Thm_PNormRegLib_sim_exec
import Theorems.Thm_PNormRegLib_sim_halt
import Definitions.Def_PNormRegLib_Exec

open PNormReg PNormRegLib SmaleNinth DetANN

namespace DetANNSimCellsAux

lemma stepE {P : Program} {ω : ℕ → Bool} {s : State} {ins : Instr}
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s :=
  step_eq_exec P ω s ins hh h

lemma bounded_step {P : Program} {ω : ℕ → Bool} {X : ℤ} {s : State} (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) : PBounded (2 * X) (step P ω s) := by
  have := bounded_run P ω X s hs hlit hX 1
  rwa [pow_one, mul_comm] at this

lemma LitBound.mono' {P : Program} {L L' : ℤ} (h : LitBound P L) (hL : L ≤ L') : LitBound P L' :=
  fun q c hc => (h q c hc).trans hL

/-- At a missing or `accept`/`reject` instruction the machine is stuck: only `work` changes. -/
def Stuck (P : Program) (pc : ℕ) : Prop :=
  P[pc]? = none ∨ P[pc]? = some (.core .accept) ∨ P[pc]? = some (.core .reject)

lemma run_stuck {P : Program} {ω : ℕ → Bool} {s : State} (hh : s.halted = false)
    (hs : Stuck P s.core.pc) : ∀ t, (run P s ω t).halted = false ∧ (run P s ω t).core.pc = s.core.pc
  | 0 => ⟨hh, rfl⟩
  | t + 1 => by
    obtain ⟨h1, h2⟩ := run_stuck (ω := ω) hh hs t
    have key : ∀ u : State, u.halted = false → u.core.pc = s.core.pc →
        (step P ω u).halted = false ∧ (step P ω u).core.pc = s.core.pc := by
      intro u hu hp
      rcases hs with h | h | h
      · rw [← hp] at h; simp [step, hu, h]; exact hp
      · rw [← hp] at h; rw [stepE hu h]; simp [exec, coreExec, hu, hp]
      · rw [← hp] at h; rw [stepE hu h]; simp [exec, coreExec, hu, hp]
    have : run P s ω (t + 1) = step P ω (run P s ω t) := by
      simp only [run, Function.iterate_succ_apply']
    rw [this]
    exact key _ h1 h2

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = run P (step P ω s) ω t := by
  simp only [run, Function.iterate_succ_apply]

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (t u : ℕ) :
    run P s ω (t + u) = run P (run P s ω u) ω t := by
  simp only [run, Function.iterate_add_apply]

/-- A halted state stutters forever. -/
lemma run_of_halted {P : Program} {ω : ℕ → Bool} {s : State} (h : s.halted = true) :
    ∀ t, run P s ω t = s
  | 0 => rfl
  | t + 1 => by rw [run_succ, show step P ω s = s by simp [step, h]]; exact run_of_halted h t

lemma getElem?_pairs {α β : Type*} (f g : α → β) :
    ∀ (L : List α) (i : ℕ), (L.flatMap fun x => [f x, g x])[2 * i]? = L[i]?.map f ∧
      (L.flatMap fun x => [f x, g x])[2 * i + 1]? = L[i]?.map g
  | [], i => by simp
  | a :: L, 0 => by simp
  | a :: L, i + 1 => by
    obtain ⟨h1, h2⟩ := getElem?_pairs f g L i
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl,
      List.getElem?_cons_succ, List.length_cons]
    exact ⟨h1, h2⟩

lemma reloc_fetch {p : RelocParams} {P Q : Program} {pc : ℕ} {ins : Instr}
    (hE : Embeds Q (reloc p P) p.cOff) (h : P[pc]? = some ins) :
    Q[p.cOff + 2 * pc]? = some (p.pair ins).1 ∧ Q[p.cOff + 2 * pc + 1]? = some (p.pair ins).2 := by
  obtain ⟨h1, h2⟩ := getElem?_pairs (fun ins => (p.pair ins).1) (fun ins => (p.pair ins).2) P pc
  rw [h] at h1 h2
  exact ⟨hE _ _ h1, by rw [add_assoc]; exact hE _ _ h2⟩

/-- The preparation instruction only advances the program counter (and may set `tmp`). -/
lemma prep_exec (p : RelocParams) (ω : ℕ → Bool) (ins : Instr) (r : State) :
    (exec ω (p.pair ins).1 r).halted = r.halted ∧
      (exec ω (p.pair ins).1 r).core.pc = r.core.pc + 1 := by
  cases ins with
  | core i => cases i <;> simp [RelocParams.pair, RelocParams.noop, exec, coreExec]
  | _ => simp [RelocParams.pair, RelocParams.noop, exec, coreExec]

lemma cellsWritten_succ (P : Program) (s : State) (t : ℕ) :
    cellsWritten P s (t + 1) =
      (writtenCell P s).toFinset ∪ cellsWritten P (step P detTape s) t := by
  ext x
  simp only [cellsWritten, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    cases i with
    | zero => exact Or.inl hx
    | succ j => exact Or.inr ⟨j, by omega, by rwa [run_succ] at hx⟩
  · rintro (hx | ⟨j, hj, hx⟩)
    · exact ⟨0, by omega, hx⟩
    · exact ⟨j + 1, by omega, by rwa [run_succ]⟩

lemma cellsWritten_zero (P : Program) (s : State) : cellsWritten P s 0 = ∅ := by
  simp [cellsWritten]

lemma cellsWritten_halted {P : Program} {s : State} (h : s.halted = true) (t : ℕ) :
    cellsWritten P s t = ∅ := by
  ext x; simp [cellsWritten, run_of_halted h, writtenCell, h]

/-- The two real steps of one relocated instruction write exactly the shifted virtual cell. -/
lemma cells_pair {p : RelocParams} {F : Frame} {P Q : Program} {ins : Instr} {r v : State}
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hok : InstrOK F.nR F.nQ ins)
    (hA : Agree p F r v) (hrh : r.halted = false) (hvh : v.halted = false)
    (hpc : r.core.pc = p.cOff + 2 * v.core.pc) (hins : P[v.core.pc]? = some ins) :
    (writtenCell Q r).toFinset ∪ (writtenCell Q (step Q detTape r)).toFinset =
      (writtenCell P v).toFinset.image (fun c => (c.1, F.b + c.2)) := by
  obtain ⟨hf1, hf2⟩ := reloc_fetch hE hins
  obtain ⟨hp1, hp2⟩ := prep_exec p detTape ins r
  rw [stepE hrh (by rw [hpc]; exact hf1)]
  have e1 : writtenCell Q r = writtenCell [(p.pair ins).1] { r with core := { r.core with pc := 0 } } := by
    simp [writtenCell, hrh, hpc, hf1]
  have e2 : writtenCell Q (exec detTape (p.pair ins).1 r) =
      writtenCell [(p.pair ins).2]
        { exec detTape (p.pair ins).1 r with core := { (exec detTape (p.pair ins).1 r).core with pc := 0 } } := by
    simp [writtenCell, hp1, hrh, hp2, hpc, hf2]
  have e3 : writtenCell P v = writtenCell [ins] { v with core := { v.core with pc := 0 } } := by
    simp [writtenCell, hvh, hins]
  rw [e1, e2, e3]
  obtain ⟨⟨rpc, rr, rp, rm⟩, ri, rc, rh, rw⟩ := r
  obtain ⟨⟨vpc, vr, vp, vm⟩, vi, vc, vh, vw⟩ := v
  obtain ⟨hR, hQ, hB0, -, -, -, -, -, -⟩ := hA
  obtain ⟨hbt, hqv⟩ := hV
  simp only at hR hQ hB0 hrh hvh
  subst hrh hvh
  cases ins with
  | core i =>
    cases i with
    | store q i =>
      simp only [InstrOK] at hok
      simp [writtenCell, RelocParams.pair, exec, hQ q hok.1, hB0, add_comm F.b]
    | _ => simp [writtenCell, RelocParams.pair, RelocParams.noop, exec, coreExec]
  | integerStore a b =>
    simp only [InstrOK] at hok
    simp [writtenCell, RelocParams.pair, exec, hQ a hok.1, hB0, add_comm F.b]
  | _ => simp [writtenCell, RelocParams.pair, RelocParams.noop, exec, coreExec]

end DetANNSimCellsAux

open DetANNSimCellsAux in
theorem solution (p : RelocParams) (F : Frame) (P Q : Program) (X : ℤ)
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hU : UsesBelow P F.nR F.nQ)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (Y : ℤ) (r v : State) (hS : Sim p F r v)
    (hB : PBounded Y v) (hXY : X ≤ Y) (hR : Y * 2 ^ t ≤ F.R)
    (hh : (run P v detTape t).halted = true) :
    ∃ t', Agree p F (run Q r detTape t') (run P v detTape t) ∧
      (run Q r detTape t').core.pc = p.exit ∧ (run Q r detTape t').halted = false ∧
      cellsWritten Q r t' = (cellsWritten P v t).image (fun c => (c.1, F.b + c.2)) := by
  have htape : (fun i => detTape (i + F.k)) = detTape := rfl
  induction t generalizing Y r v with
  | zero =>
    simp [run, hS.2.2.1] at hh
  | succ t ih =>
    obtain ⟨hA, hrh, hvh, hpc⟩ := hS
    have hY1 : (1 : ℤ) ≤ Y := hX.trans hXY
    have hYR : Y ≤ F.R := by
      have : Y ≤ Y * 2 ^ (t + 1) := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
      linarith
    have hlive : ¬ Stuck P v.core.pc := by
      intro hst
      have := (run_stuck (ω := detTape) hvh hst (t + 1)).1
      rw [hh] at this; exact Bool.noConfusion this
    obtain ⟨ins, hins⟩ : ∃ ins, P[v.core.pc]? = some ins := by
      cases h : P[v.core.pc]? with
      | none => exact absurd (Or.inl h) hlive
      | some ins => exact ⟨ins, rfl⟩
    have hna : ins ≠ .core .accept := fun e => hlive (Or.inr (Or.inl (e ▸ hins)))
    have hnr : ins ≠ .core .reject := fun e => hlive (Or.inr (Or.inr (e ▸ hins)))
    have hok := hU ins (List.mem_of_getElem? hins)
    obtain ⟨hf1, hf2⟩ := reloc_fetch hE hins
    obtain ⟨hp1, hp2⟩ := prep_exec p detTape ins r
    have hr2 : run Q r detTape 2 = exec detTape (p.pair ins).2 (exec detTape (p.pair ins).1 r) := by
      show step Q detTape (step Q detTape r) = _
      rw [stepE hrh (by rw [hpc]; exact hf1)]
      exact stepE (by rw [hp1, hrh]) (by rw [hp2, hpc]; exact hf2)
    have hv1 : step P detTape v = exec detTape ins v := stepE hvh hins
    have hcells := cells_pair hE hV hok hA hrh hvh hpc hins
    -- real cells over `t' + 2` steps: the pair, then the rest
    have hsplit : ∀ t', cellsWritten Q r (t' + 2) =
        ((writtenCell Q r).toFinset ∪ (writtenCell Q (step Q detTape r)).toFinset) ∪
          cellsWritten Q (run Q r detTape 2) t' := by
      intro t'
      rw [show t' + 2 = (t' + 1) + 1 from rfl, cellsWritten_succ, cellsWritten_succ,
        Finset.union_assoc]
      rfl
    rw [cellsWritten_succ, hv1, Finset.image_union, ← hcells]
    rw [run_succ, hv1] at hh ⊢
    by_cases hhalt : ins = .halt
    · subst hhalt
      obtain ⟨hA', hpc', hrh', hvh'⟩ := sim_halt p F detTape r v hA
      rw [htape] at hA' hvh'
      refine ⟨2, ?_⟩
      rw [hr2, run_of_halted hvh', cellsWritten_halted hvh']
      refine ⟨hA', hpc', hrh'.trans hrh, ?_⟩
      rw [Finset.image_empty, Finset.union_empty]
      simpa [cellsWritten_zero] using hsplit 0
    · obtain ⟨hA', hpc', hrh', hvh'⟩ :=
        sim_exec p F detTape ins Y r v hV hok hA hpc hB hYR ⟨hna, hnr, hhalt⟩
      rw [htape] at hA' hpc' hvh'
      have hB' : PBounded (2 * Y) (exec detTape ins v) := by
        rw [← hv1]; exact bounded_step hB (LitBound.mono' hlit hXY) hY1
      obtain ⟨t', ht'A, ht'pc, ht'h, ht'c⟩ := ih (2 * Y) _ _
        ⟨hA', hrh'.trans hrh, hvh'.trans hvh, hpc'⟩ hB' (by linarith)
        (by rw [pow_succ] at hR; linarith) hh
      refine ⟨t' + 2, ?_⟩
      rw [run_add, hsplit, hr2, ht'c]
      exact ⟨ht'A, ht'pc, ht'h, rfl⟩
