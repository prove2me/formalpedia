-- Prove2me | solution 1 for DetDLP.m89_s1_word_pipe
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T01:12:24.169075+00:00
-- url     : https://prove2.me/submissions/069e509e-7f65-4618-9b19-cfe5f95c77fd

import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.m89_s1_pipe.Permuted

open MachineComposition

variable {m n : ℕ} (P : Program m) (e : Fin m ≃ Fin n)

/-- Place source tape `i` at physical tape `e i`, without changing finite control. -/
def program : Program n where
  stateCount := P.stateCount
  start := P.start
  scan q := e (P.scan q)
  transition := P.transition

@[simp] theorem program_scan (q : Fin P.stateCount) :
    (program P e).scan q = e (P.scan q) := rfl

@[simp] theorem program_transition (q : Fin P.stateCount) (s : Option Bool) :
    (program P e).transition q s = P.transition q s := rfl

variable (src : Fin m) (dst : Fin n)

def positionedCfg (c : (P.machine src).Cfg) : ((program P e).machine dst).Cfg where
  state := c.state
  tapes := c.tapes ∘ e.symm

/-- Relocate an existing configuration, including its entire visit history. Neither
`src` nor `dst` is read: they designate the input tapes only at initialization. -/
def positioned (c : LocatedCfg (P.machine src)) : LocatedCfg ((program P e).machine dst) where
  config := positionedCfg P e src dst c.config
  position := c.position ∘ e.symm
  lower := c.lower ∘ e.symm
  upper := c.upper ∘ e.symm

section Readout

variable (c : LocatedCfg (P.machine src))

@[simp] theorem positioned_state : (positioned P e src dst c).config.state = c.config.state := rfl

theorem positioned_tapes_at (j : Fin n) :
    (positioned P e src dst c).config.tapes j = c.config.tapes (e.symm j) := rfl

theorem positioned_position_at (j : Fin n) :
    (positioned P e src dst c).position j = c.position (e.symm j) := rfl

theorem positioned_lower_at (j : Fin n) :
    (positioned P e src dst c).lower j = c.lower (e.symm j) := rfl

theorem positioned_upper_at (j : Fin n) :
    (positioned P e src dst c).upper j = c.upper (e.symm j) := rfl

@[simp] theorem positioned_tapes (i : Fin m) :
    (positioned P e src dst c).config.tapes (e i) = c.config.tapes i := by
  rw [positioned_tapes_at, e.symm_apply_apply]

@[simp] theorem positioned_position (i : Fin m) :
    (positioned P e src dst c).position (e i) = c.position i := by
  rw [positioned_position_at, e.symm_apply_apply]

@[simp] theorem positioned_lower (i : Fin m) :
    (positioned P e src dst c).lower (e i) = c.lower i := by
  rw [positioned_lower_at, e.symm_apply_apply]

@[simp] theorem positioned_upper (i : Fin m) :
    (positioned P e src dst c).upper (e i) = c.upper i := by
  rw [positioned_upper_at, e.symm_apply_apply]

@[simp] theorem positioned_space : visitedSpace (positioned P e src dst c) = visitedSpace c :=
  e.symm.sum_comp (fun i => (c.upper i - c.lower i + 1).toNat)

end Readout

/-- The primitive move or write updates `e (P.scan q)` and leaves every other tape alone. -/
@[simp] theorem positionedCfg_step (c : (P.machine src).Cfg) :
    ((program P e).machine dst).step (positionedCfg P e src dst c) =
      ((P.machine src).step c).map (positionedCfg P e src dst) := by
  rcases c with ⟨s, tapes⟩
  cases s with
  | inl b => rfl
  | inr q =>
    simp only [PrimitiveMachine.step, positionedCfg, Program.machine, program,
      Function.comp_apply, Equiv.symm_apply_apply]
    cases ht : P.transition q (tapes (P.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨next, action⟩
      cases action <;> simp [positionedCfg] <;>
        exact (Function.update_comp_equiv tapes e.symm (P.scan q) _).symm

/-- The monitor performs the same displacement and extends the same interval on the
permuted scanned tape. It never reinitializes an interval. -/
@[simp] theorem positioned_monitor (c : LocatedCfg (P.machine src)) (d : (P.machine src).Cfg) :
    (positioned P e src dst c).monitor (positionedCfg P e src dst d) =
      positioned P e src dst (c.monitor d) := by
  rcases c with ⟨⟨s, tapes⟩, pos, lo, hi⟩
  cases s with
  | inl b => rfl
  | inr q =>
    simp only [LocatedCfg.monitor, positioned, positionedCfg, Program.machine, program,
      Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    cases ht : P.transition q (tapes (P.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨next, action⟩
      simp [Function.update_comp_equiv]

@[simp] theorem positioned_step (c : LocatedCfg (P.machine src)) :
    locatedStep ((program P e).machine dst) (positioned P e src dst c) =
      (locatedStep (P.machine src) c).map (positioned P e src dst) := by
  unfold locatedStep
  rw [show (positioned P e src dst c).config = positionedCfg P e src dst c.config from rfl,
    positionedCfg_step]
  cases hs : (P.machine src).step c.config <;> simp

theorem positioned_step_some (a b : LocatedCfg (P.machine src))
    (h : locatedStep (P.machine src) a = some b) :
    locatedStep ((program P e).machine dst) (positioned P e src dst a) =
      some (positioned P e src dst b) := by
  simp only [positioned_step, h, Option.map_some]

theorem positioned_trace {a b : LocatedCfg (P.machine src)} {nstep : ℕ}
    (h : Computation.Trace (locatedStep (P.machine src)) nstep a b) :
    Computation.Trace (locatedStep ((program P e).machine dst)) nstep
      (positioned P e src dst a) (positioned P e src dst b) :=
  MachineComposition.Trace.map _ (positioned_step_some P e src dst) h

/-- Both endpoints and every prefix retain their physical tapes and recorded intervals
up to the same permutation, with the original step count and space bound. -/
theorem positioned_segment {a b : LocatedCfg (P.machine src)} {nstep : ℕ} {σ : ℝ}
    (h : Segment (P.machine src) a b nstep σ) :
    Segment ((program P e).machine dst) (positioned P e src dst a)
      (positioned P e src dst b) nstep σ := by
  refine ⟨positioned_trace P e src dst h.1, ?_⟩
  intro k c hk hc
  obtain ⟨d, hd, rfl⟩ := MachineComposition.Trace.prefix_of_map _
    (positioned_step_some P e src dst) h.1 hk hc
  simpa only [positioned_space] using h.2 k d hk hd

end DetDLP.m89_s1_pipe.Permuted
namespace DetDLP.m89_s1_pipe.Rel
open MachineComposition
variable {M : PrimitiveMachine}

/-- Compare the caller's physical monitor to the callee's relative monitor. -/
structure Corr (old phys rel : LocatedCfg M) : Prop where
  cfg : phys.config = rel.config
  pos : ∀ i, phys.position i = old.position i + rel.position i
  lo : ∀ i, min (old.lower i) (old.position i + rel.lower i) ≤ phys.lower i
  hi : ∀ i, phys.upper i ≤ max (old.upper i) (old.position i + rel.upper i)

private theorem next_monitor {old c d : LocatedCfg M} (h : Corr old c d) (q : M.Cfg) :
    Corr old (c.monitor q) (d.monitor q) := by
  have hh := h.cfg
  rcases c with ⟨cc,pc,lc,uc⟩; rcases d with ⟨dc,pd,ld,ud⟩
  change cc = dc at hh; subst dc
  rcases cc with ⟨s,t⟩
  cases s with
  | inl b => exact ⟨rfl,h.pos,h.lo,h.hi⟩
  | inr l =>
    unfold LocatedCfg.monitor
    simp only [Sum.elim_inr]
    cases ht : M.transition l (t (M.scan l)).head with
    | inl b => exact ⟨rfl,h.pos,h.lo,h.hi⟩
    | inr act =>
      simp only [Sum.elim_inr]
      refine ⟨rfl,?_,?_,?_⟩
      · intro i; have hp := h.pos i
        dsimp at hp ⊢; by_cases hx : i = M.scan l
        · subst i; simp only [Function.update_self]; omega
        · simpa only [Function.update_of_ne hx] using hp
      · intro i; have hp := h.pos i; have hl := h.lo i
        dsimp at hp hl ⊢; by_cases hx : i = M.scan l
        · subst i; simp only [Function.update_self]; omega
        · simpa only [Function.update_of_ne hx] using hl
      · intro i; have hp := h.pos i; have hu := h.hi i
        dsimp at hp hu ⊢; by_cases hx : i = M.scan l
        · subst i; simp only [Function.update_self]; omega
        · simpa only [Function.update_of_ne hx] using hu

private theorem next {old c d e : LocatedCfg M} (h : Corr old c d) (he : locatedStep M d = some e) :
    ∃ f, locatedStep M c = some f ∧ Corr old f e := by
  unfold locatedStep at he ⊢
  rw [h.cfg]
  cases hm : M.step d.config with
  | none => simp [hm] at he
  | some q =>
    have he' : d.monitor q = e := by simpa [hm] using he
    subst e; exact ⟨_,rfl,next_monitor h q⟩

private theorem travel {old c d e : LocatedCfg M} {n : ℕ} (h : Corr old c d)
    (ht : Computation.Trace (locatedStep M) n d e) :
    ∃ f, Computation.Trace (locatedStep M) n c f ∧ Corr old f e := by
  induction ht generalizing c with
  | refl => exact ⟨_,.refl _,h⟩
  | cons he _ ih =>
    obtain ⟨c',hs,hr⟩ := next h he
    obtain ⟨f,hf,hcorr⟩ := ih hr
    exact ⟨f,.cons hs hf,hcorr⟩

theorem call {a start finish : LocatedCfg M} {n : ℕ} {σ : ℝ} (hw : LocatedWellFormed a)
    (hc : a.config = start.config) (hp : ∀ i, start.position i = 0)
    (hz : OriginCovered start) (hs : Segment M start finish n σ) :
    ∃ f, f.config = finish.config ∧ Segment M a f n ((visitedSpace a : ℝ)+σ) := by
  have h0 : Corr a a start := ⟨hc,fun i => by rw [hp,add_zero],
    fun _ => min_le_left .., fun _ => le_max_left ..⟩
  obtain ⟨f,tr,hr⟩ := travel h0 hs.1
  have hf := originCovered_trace hz hs.1
  have hb : visitedSpace f ≤ visitedSpace a + visitedSpace finish := by
    unfold visitedSpace; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum
    intro i _; have hlo := hr.lo i; have hhi := hr.hi i; have hw' := hw i; have hz' := hf i
    omega
  refine ⟨f,hr.cfg,segment_iff_final_space.2 ⟨tr,?_⟩⟩
  have hb' : (visitedSpace f : ℝ) ≤ visitedSpace a + (visitedSpace finish : ℝ) := by exact_mod_cast hb
  linarith [(segment_iff_final_space.mp hs).2]
end DetDLP.m89_s1_pipe.Rel
namespace DetDLP.m89_s1_pipe.Wiring
open MachineComposition

def wire {m n : ℕ} (a : Fin m) (b : Fin n) : Fin (n+m) ≃ Fin (m+n) :=
  finAddFlip.trans (Equiv.swap (Fin.natAdd m b) (Fin.castAdd n a))

def saved {m : ℕ} (t : Fin m → Turing.Tape (Option Bool)) (a : Fin m) : TapeFrame m where
  tapes i := if i = a then Turing.Tape.mk₁ [] else t i
  position _ := 0
  lower _ := 0
  upper _ := 0

@[simp] theorem saved_space {m : ℕ} (t : Fin m → Turing.Tape (Option Bool)) (a : Fin m) :
    (saved t a).space = m := by simp [saved,TapeFrame.space]

private theorem sep {m n : ℕ} (x : Fin m) (y : Fin n) : Fin.castAdd n x ≠ Fin.natAdd m y := by
  intro h; have hh := congrArg Fin.val h; simp only [Fin.val_castAdd,Fin.val_natAdd] at hh; omega

theorem transfer {m : ℕ} (t : Fin m → Turing.Tape (Option Bool)) (a : Fin m) (B : PrimitiveMachine)
    (w : List Bool) (h : t a = Turing.Tape.mk₁ (w.map some)) (j : Fin (B.tapeCount+m)) :
    Fin.append t (fun _ : Fin B.tapeCount => Turing.Tape.mk₁ []) (wire a B.inputTape j) =
      Fin.append (B.init w).tapes (saved t a).tapes j := by
  induction j using Fin.addCases with
  | left i =>
    simp only [wire,Equiv.trans_apply,finAddFlip_apply_castAdd,Fin.append_left,PrimitiveMachine.init]
    by_cases hi : i = B.inputTape
    · subst i; simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun he => hi ((Fin.natAdd_inj m).mp he)) (Ne.symm (sep a i))]
      simp [hi]
  | right i =>
    simp only [wire,Equiv.trans_apply,finAddFlip_apply_natAdd,Fin.append_right,saved]
    by_cases hi : i = a
    · subst i; simp
    · rw [Equiv.swap_apply_of_ne_of_ne (sep i B.inputTape) (fun he => hi (Fin.castAdd_inj.mp he))]
      simp [hi]
end DetDLP.m89_s1_pipe.Wiring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.m89_s1_pipe.Pipeline

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open MachineComposition

def tail (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine) :
    Program (A.tapeCount+B.tapeCount) :=
  Permuted.program (.ofMachine (addTapes B A.tapeCount)) (Wiring.wire out B.inputTape)

def machine (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine) : PrimitiveMachine :=
  thenMachine (addTapes A B.tapeCount) (tail A out B)

def resultPort (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine)
    (bout : Fin B.tapeCount) : Fin (machine A out B).tapeCount :=
  Wiring.wire out B.inputTape (Fin.castAdd A.tapeCount bout)

/-- Sequential ordinary word computation with arbitrary work tape counts and arbitrary
    garbage on the producer's final tapes. Step counts add. Visited-cell budgets add up
    to a fixed number of tapes, independently of the (possibly very large) step counts. -/
theorem run (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine) (bout : Fin B.tapeCount)
    {input mid result : List Bool} {tA sA tB sB : ℝ}
    (ha : RunsWithin A out input mid tA sA) (hb : RunsWithin B bout mid result tB sB) :
    RunsWithin (machine A out B) (resultPort A out B bout) input result (tA+tB)
      (sA+B.tapeCount+(sB+A.tapeCount)) := by
  let A' := addTapes A B.tapeCount
  let B' := addTapes B A.tapeCount
  let P := Program.ofMachine B'
  let e := Wiring.wire out B.inputTape
  let Q := Permuted.program P e
  obtain ⟨n,a,ht,hh,ho,hn,hs⟩ := (runsWithin_iff_final_space _ _ _ _ _ _).1 ha
  obtain ⟨m,b,hbseg,hbh,hbo,hm⟩ := (runsWithin_iff_segment _ _ _ _ _ _).1 hb
  let a' := addTapesLocated A B.tapeCount a
  have hat : Computation.Trace (locatedStep A') n (locatedInit A' input) a' := by
    rw [addTapesLocated_init]
    apply MachineComposition.Trace.map (addTapesLocated A B.tapeCount) _ ht
    intro c d h
    rw [addTapesLocated_step,h]; rfl
  have hsa : (visitedSpace a' : ℝ) ≤ sA+B.tapeCount := by
    rw [show visitedSpace a' = visitedSpace a+B.tapeCount from addTapesLocated_space .., Nat.cast_add]
    linarith
  have ha' : Segment A' (locatedInit A' input) a' n (sA+B.tapeCount) := segment_iff_final_space.mpr ⟨hat,hsa⟩
  let fr := Wiring.saved a.config.tapes out
  let start := frameLocated B fr (locatedInit B mid)
  let finish := frameLocated B fr b
  have hseg : Segment (P.machine B'.inputTape) start finish m (sB + fr.space) := frameLocated_segment B fr hbseg
  let move := Permuted.positioned P e B'.inputTape A'.inputTape
  have hseg' : Segment (Q.machine A'.inputTape) (move start) (move finish) m (sB+A.tapeCount) := by
    change Segment ((Permuted.program P e).machine A'.inputTape) _ _ _ _
    simpa only [move,fr,Wiring.saved_space] using Permuted.positioned_segment P e B'.inputTape A'.inputTape hseg
  let entry := restartCfg A' Q a'
  have hw : LocatedWellFormed entry := fun i => locatedWellFormed_reachable hat i
  have hc : entry.config = (move start).config := by
    change (⟨.inr _,_⟩ : (Q.machine A'.inputTape).Cfg) = ⟨.inr _,_⟩
    congr 1
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    change Fin.append a.config.tapes (fun _ : Fin B.tapeCount => Turing.Tape.mk₁ []) (e j) =
      Fin.append (B.init mid).tapes fr.tapes (e.symm (e j))
    rw [e.symm_apply_apply]
    exact Wiring.transfer a.config.tapes out B mid ho j
  have hp : ∀ i, (move start).position i = 0 := by
    intro i
    change Fin.append (fun _ : Fin B.tapeCount => (0 : ℤ)) (fun _ : Fin A.tapeCount => (0 : ℤ)) (e.symm i) = 0
    generalize e.symm i = j; induction j using Fin.addCases <;> simp
  have hz : OriginCovered (move start) := by
    intro i
    change Fin.append (locatedInit B mid).lower (fun _ : Fin A.tapeCount => (0:ℤ)) (e.symm i) ≤ 0 ∧
      0 ≤ Fin.append (locatedInit B mid).upper (fun _ : Fin A.tapeCount => (0:ℤ)) (e.symm i)
    generalize e.symm i = j
    induction j using Fin.addCases with
    | left k => simpa only [Fin.append_left] using originCovered_init B mid k
    | right k => simp
  obtain ⟨actual,he,seg⟩ := Rel.call hw hc hp hz hseg'
  have hs' : Segment (Q.machine A'.inputTape) entry actual m (sA+B.tapeCount+(sB+A.tapeCount)) :=
    seg.mono (by change (visitedSpace a' : ℝ) + _ ≤ _; linarith)
  have halt : ∃ b, actual.config.state = Sum.inl b := by rw [he]; exact hbh
  have hout : actual.config.tapes (resultPort A out B bout) = Turing.Tape.mk₁ (result.map some) := by
    rw [he]
    change Fin.append b.config.tapes fr.tapes (e.symm (e (Fin.castAdd A.tapeCount bout))) = _
    rwa [e.symm_apply_apply,Fin.append_left]
  have hrun := thenMachine_runsWithin_add A' Q (resultPort A out B bout) input result ha' hh hs' halt hout hn hm
  have hsB : 0 ≤ sB := (Nat.cast_nonneg (visitedSpace b)).trans (segment_iff_final_space.mp hbseg).2
  exact runsWithin_mono hrun le_rfl (max_le (by linarith [Nat.cast_nonneg (α:=ℝ) A.tapeCount]) le_rfl)

end DetDLP.m89_s1_pipe.Pipeline


namespace DetDLP.m89_s1_pipe
private theorem scale_ge_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ (b : ℝ) / (logSafe b)^((1:ℝ)/4) := by
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hl : logSafe b ≤ (b:ℝ) := by
    apply max_le hbr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    rw [Real.rpow_natCast]; apply max_le
    · exact_mod_cast (show 2 ≤ 2^b by exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) hb))
    · exact_mod_cast (show b < 2^b from Nat.lt_two_pow_self).le
  have hg : 1 ≤ logSafe (b:ℝ) := le_max_left _ _
  have hp : (logSafe (b:ℝ))^((1:ℝ)/4) ≤ logSafe b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hg (by norm_num : (1:ℝ)/4 ≤ 1)
  apply (one_le_div (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hg) _)).mpr
  exact hp.trans hl
private theorem absorb (K k b : ℕ) (hb : 1 ≤ b) : (K:ℝ) * (mainSpaceBound k b)^3 ≤ mainSpaceBound (K+3*k) b := by
  let s := (b:ℝ)/(logSafe b)^((1:ℝ)/4)
  have hs : 1 ≤ s := scale_ge_one hb
  have rwW (j : ℕ) : mainSpaceBound j b = (2:ℝ)^((j:ℝ)*s) := by unfold mainSpaceBound s; congr 1; ring
  rw [rwW,rwW,← Real.rpow_mul_natCast (by norm_num)]
  have hK : (K:ℝ) ≤ (2:ℝ)^((K:ℝ)*s) := by
    calc (K:ℝ) ≤ (2:ℝ)^(K:ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast (show K < 2^K from Nat.lt_two_pow_self).le
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α:=ℝ) K])
  calc _ ≤ (2:ℝ)^((K:ℝ)*s) * (2:ℝ)^((k:ℝ)*s*(3:ℕ)) := mul_le_mul_of_nonneg_right hK (by positivity)
       _ = _ := by rw [← Real.rpow_add (by norm_num)]; push_cast; congr 1; ring

end DetDLP.m89_s1_pipe
open DetDLP DetDLP.MachineComposition DetDLP.m89_s1_pipe

private theorem DetDLP.m89_s1_pipe.main_mono {i j b : ℕ} (h : i ≤ j) : mainSpaceBound i b ≤ mainSpaceBound j b := by
  unfold mainSpaceBound
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)) (Real.rpow_nonneg ((le_max_left 1 _).trans' zero_le_one) _)

theorem solution (A : PrimitiveMachine) (a : Fin A.tapeCount) (B : PrimitiveMachine) (d : Fin B.tapeCount)
    (i j : ℕ) (small : Bool) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (K : ℕ),
      ∀ (b : ℕ), 1 ≤ b → ∀ x y z : List Bool,
        RunsWithin A a x y (mainSpaceBound i b) (if small then polyBound i b else mainSpaceBound i b) →
        RunsWithin B d y z (mainSpaceBound j b) (if small then polyBound j b else mainSpaceBound j b) →
        RunsWithin M o x z (mainSpaceBound K b) (if small then polyBound K b else mainSpaceBound K b) := by
  let k := max i j
  let r := A.tapeCount+B.tapeCount+2
  let K := r+3*k
  refine ⟨Pipeline.machine A a B, Pipeline.resultPort A a B d,K,?_⟩
  intro b hb x y z ha hB
  let W := mainSpaceBound k b
  have hw : 1 ≤ W := by
    apply Real.one_le_rpow (by norm_num)
    apply div_nonneg (by positivity)
    exact Real.rpow_nonneg ((le_max_left 1 _).trans' zero_le_one) _
  have hI : mainSpaceBound i b ≤ W := main_mono (le_max_left i j)
  have hJ : mainSpaceBound j b ≤ W := main_mono (le_max_right i j)
  have hscale : mainSpaceBound i b + B.tapeCount + (mainSpaceBound j b + A.tapeCount) ≤ mainSpaceBound K b := by
    apply le_trans _ (absorb r k b hb)
    have hcube : 1 ≤ W^3 := one_le_pow₀ hw
    have hlinear : W ≤ W^3 := by simpa only [pow_one] using pow_le_pow_right₀ hw (show 1 ≤ 3 by decide)
    have hconst : ((A.tapeCount:ℝ)+B.tapeCount) ≤ ((A.tapeCount:ℝ)+B.tapeCount)*W^3 := le_mul_of_one_le_right (by positivity) hcube
    change _ ≤ (r:ℝ)*W^3
    dsimp [r]; push_cast; nlinarith
  have htime : mainSpaceBound i b + mainSpaceBound j b ≤ mainSpaceBound K b := by
    linarith [Nat.cast_nonneg (α := ℝ) A.tapeCount, Nat.cast_nonneg (α := ℝ) B.tapeCount]
  have hraw := Pipeline.run A a B d ha hB
  apply runsWithin_mono hraw htime
  cases small with
  | false => exact hscale
  | true =>
    change polyBound i b + B.tapeCount + (polyBound j b + A.tapeCount) ≤ polyBound K b
    have hbase : (1:ℝ) ≤ (b:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
    have hn : i+j+A.tapeCount+B.tapeCount ≤ K := by dsimp [K,r,k]; omega
    have hi : i ≤ K := by omega
    have hj : j ≤ K := by omega
    have h1 := one_le_pow₀ hbase (n := K)
    have hi' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hi) (Nat.cast_nonneg (α := ℝ) i)
    have hj' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hj) (Nat.cast_nonneg (α := ℝ) j)
    have hsum : (A.tapeCount:ℝ)+B.tapeCount ≤ ((A.tapeCount:ℝ)+B.tapeCount)*((b:ℝ)+1)^K := le_mul_of_one_le_right (by positivity) h1
    have htot := mul_le_mul_of_nonneg_right (show (i:ℝ)+j+A.tapeCount+B.tapeCount ≤ K by exact_mod_cast hn) (show 0 ≤ ((b:ℝ)+1)^K by positivity)
    unfold polyBound; nlinarith
