-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.general_domain_adapter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:46:45.458721+00:00
-- url     : https://prove2.me/submissions/76fad5b6-c2bd-4f01-97be-51eeca732f55

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Machine
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_exact_small_accuracy_sssp
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_normal_domain_sssp_adapter
section s0
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma log_size_positive (m : ℕ) : 0 < Real.log (max 2 m : ℕ) := by
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (le_max_left 2 m))
lemma log_size_tendsto : Tendsto (fun m : ℕ => Real.log (max 2 m : ℕ)) atTop atTop := by
  have hh : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  simp only [max_eq_right hm]
lemma subpolynomial_constant (c : ℝ) (hc : 0 < c) : Subpolynomial (fun _ => c) :=
  ⟨fun _ => hc, log_size_tendsto.const_div_atTop (Real.log c)⟩
lemma subpolynomial_mul (a b : ℕ → ℝ) (ha : Subpolynomial a) (hb : Subpolynomial b) :
    Subpolynomial (fun m => a m * b m) := by
  refine ⟨fun m => mul_pos (ha.1 m) (hb.1 m), ?_⟩
  have hfun : (fun m => Real.log (a m * b m) / Real.log (max 2 m : ℕ)) =
      fun m => Real.log (a m) / Real.log (max 2 m : ℕ) + Real.log (b m) / Real.log (max 2 m : ℕ) := by
    funext m
    rw [Real.log_mul (ha.1 m).ne' (hb.1 m).ne', add_div]
  rw [hfun]
  simpa only [add_zero] using ha.2.add hb.2
lemma subpolynomial_exp (f : ℕ → ℝ)
    (hf : Tendsto (fun m => f m / Real.log (max 2 m : ℕ)) atTop (nhds 0)) :
    Subpolynomial (fun m => Real.exp (f m)) := by
  exact ⟨fun m => Real.exp_pos _, by simpa only [Real.log_exp] using hf⟩
lemma subpolynomial_add (a b : ℕ → ℝ) (ha : Subpolynomial a) (hb : Subpolynomial b) :
    Subpolynomial (fun m => a m + b m) := by
  refine ⟨fun m => add_pos (ha.1 m) (hb.1 m), ?_⟩
  have hu : Tendsto (fun m => Real.log 2 / Real.log (max 2 m : ℕ) +
      max (Real.log (a m) / Real.log (max 2 m : ℕ))
        (Real.log (b m) / Real.log (max 2 m : ℕ))) atTop (nhds 0) := by
    simpa only [max_self, add_zero] using (log_size_tendsto.const_div_atTop (Real.log 2)).add (ha.2.max hb.2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ha.2 hu
  · intro m
    exact div_le_div_of_nonneg_right (Real.log_le_log (ha.1 m) (le_add_of_nonneg_right (hb.1 m).le)) (log_size_positive m).le
  · intro m
    have hsum : a m + b m ≤ 2 * max (a m) (b m) := by
      have h1 := le_max_left (a m) (b m)
      have h2 := le_max_right (a m) (b m)
      linarith
    have hmax : Real.log (max (a m) (b m)) = max (Real.log (a m)) (Real.log (b m)) := by
      rcases le_total (a m) (b m) with hab | hba
      · rw [max_eq_right hab, max_eq_right (Real.log_le_log (ha.1 m) hab)]
      · rw [max_eq_left hba, max_eq_left (Real.log_le_log (hb.1 m) hba)]
    have hl := Real.log_le_log (add_pos (ha.1 m) (hb.1 m)) hsum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt ((ha.1 m).trans_le (le_max_left _ _))), hmax] at hl
    have hh := div_le_div_of_nonneg_right hl (log_size_positive m).le
    simpa only [add_div, max_div_div_right (log_size_positive m).le] using hh
end DecrAlmostLinearSSSP.Decremental
end s0
section s1
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma ram_query_nine (p : Program)
    (h0 : p.code[p.query]? = some (.loadN 6 5))
    (h1 : p.code[p.query + 1]? = some (.load 1 5))
    (h2 : p.code[p.query + 2]? = some .halt)
    (c : Machine) (v : ℕ) :
    ∃ d, Ends p {resume c p.query with natReg := Function.update c.natReg 5 v} d ∧
      d.work + 6 ≤ c.work + 9 ∧ d.natReg 6 = c.natMem v ∧ d.realReg 1 = c.realMem v ∧
      d.realMem = c.realMem ∧ d.natMem = c.natMem := by
  classical
  let start : Machine := {resume c p.query with natReg := Function.update c.natReg 5 v}
  let c1 : Machine := { start with pc := p.query + 1, natReg := Function.update start.natReg 6 (c.natMem v), work := c.work + 1 }
  let c2 : Machine := { c1 with pc := p.query + 2, realReg := Function.update c.realReg 1 (c.realMem v), work := c.work + 2 }
  let finish : Machine := { c2 with pc := p.query + 3, halted := true, work := c.work + 3 }
  have hs1 : step p start = c1 := by
    simp [step, start, c1, resume, h0]
  have hs2 : step p c1 = c2 := by
    simp [step, start, c1, c2, resume, h1]
  have hs3 : step p c2 = finish := by
    simp [step, start, c1, c2, finish, resume, h2]
  have hex : execute p start 3 = finish := by
    change step p (step p (step p start)) = finish
    rw [hs1, hs2, hs3]
  refine ⟨finish, ⟨3, hex, rfl, rfl⟩, ?_, ?_, ?_, rfl, rfl⟩
  · change c.work + 3 + 6 ≤ c.work + 9
    omega
  · simp [finish, c2, c1, start]
  · simp [finish, c2]
end DecrAlmostLinearSSSP.Decremental
end s1
section s2
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def singletonProgram : Program where
  code := [.halt, .loadN 6 5, .load 1 5, .halt]
  initPC := 0
  update := 0
  query := 1
def haltState (c : Machine) : Machine :=
  {c with pc := c.pc + 1, work := c.work + 1, halted := true}
lemma singleton_halt (c : Machine) (hc : c.pc = 0) (hh : c.halted = false)
    (hf : c.fault = false) : Ends singletonProgram c (haltState c) := by
  refine ⟨1, ?_, rfl, hf⟩
  change step singletonProgram c = _
  simp [step, singletonProgram, haltState, hc, hh]
lemma distance_self {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ≥0∞) (s : Fin n) : distance g active w s s = 0 := by
  apply le_antisymm _ bot_le
  exact iInf_le_of_le [] (iInf_le_of_le (Walk.nil s) (by simp))
lemma singleton_vertex (i : Input) (hn : i.n = 1) (v : Fin i.n) : v = i.source := by
  apply Fin.ext
  have hv := v.isLt
  have hs := i.source.isLt
  have hv0 : v.val = 0 := by omega
  have hs0 : i.source.val = 0 := by omega
  omega
lemma singleton_input_memory (i : Input) (v : Fin i.n) :
    (initialMachine singletonProgram i).natMem v.val = 0 := by
  simp only [initialMachine]
  have hh : ¬ (i.n ≤ v.val ∧ (v.val - i.n) / 3 < i.k) := fun h => (not_le.mpr v.isLt) h.1
  simp only [dif_neg hh]
lemma singleton_online (i : Input) (ds : List (Fin i.k)) :
    ∃ (cs : List Machine) (c : Machine), OnlineRun singletonProgram i ds cs ∧
      cs.length = ds.length + 1 ∧ cs.getLast? = some c ∧ c.work = ds.length + 1 ∧
      (∀ d ∈ cs, (∀ v : Fin i.n, d.natMem v.val = 0) ∧ d.realMem = fun _ => 0) := by
  classical
  induction ds using List.reverseRecOn with
  | nil =>
    let c := haltState (initialMachine singletonProgram i)
    refine ⟨[c], c, .init (singleton_halt _ rfl rfl rfl), rfl, rfl, rfl, ?_⟩
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact ⟨singleton_input_memory i, rfl⟩
  | append_singleton ds e ih =>
    obtain ⟨cs, c, hr, hl, hc, hw, hm⟩ := ih
    let start := deletionMachine singletonProgram c e.val
    let d := haltState start
    have hd : Ends singletonProgram start d := singleton_halt start rfl rfl rfl
    have hc_mem : c ∈ cs := List.mem_of_getLast? hc
    obtain ⟨hcm, hcr⟩ := hm c hc_mem
    refine ⟨cs ++ [d], d, .next hr hc e hd, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, hl]
    · simp
    · simpa only [d, haltState, start, deletionMachine, resume, List.length_append, List.length_singleton] using congrArg (· + 1) hw
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hm z hz
      · simp only [List.mem_singleton] at hz
        subst z
        exact ⟨hcm, hcr⟩
lemma singleton_maintains (i : Input) (hi : i.Valid) (hn : i.n = 1) :
    Maintains singletonProgram 8 (fun _ => 1) 9 false i := by
  classical
  intro ds hd
  obtain ⟨cs, last, hr, hl, hlast, hw, hm⟩ := singleton_online i ds
  refine ⟨cs, hr, hl, ?_, ?_, ?_⟩
  · intro j c hc
    obtain ⟨hcm, hcr⟩ := hm c (List.mem_of_getElem? hc)
    have hstored (v : Fin i.n) : stored c v.val = 0 := by simp [stored, hcm v, hcr]
    refine ⟨hstored i.source, ?_, ?_⟩
    · intro v
      refine ⟨by rw [hcm v]; omega, ?_⟩
      intro _
      rw [hcr]
    · intro v
      have hv := singleton_vertex i hn v
      have hdist : i.dist (ds.take j) v = 0 := by rw [hv]; exact distance_self _ _ _ _
      have hreach : Reachable i.graph (live (ds.take j)) i.source v := by rw [hv]; exact ⟨[], .nil _⟩
      simp [hdist, hstored v, hreach]
  · intro c hc
    have heq : c = last := Option.some.inj (hc.symm.trans hlast)
    subst c
    rw [hw]
    have hlen : ds.length ≤ i.size := by
      have hh := hd.length_le_card
      simp only [Fintype.card_fin] at hh
      exact hh.trans hi.2.1
    have hmpos : 1 ≤ i.size := by rw [← hn]; exact hi.1
    have ha : 0 < i.accuracy := hi.2.2.2.1
    have heps : i.accuracy ≤ 1 := hi.2.2.2.2.1
    simp only [Bool.false_eq_true, if_false, mul_one]
    apply (le_div_iff₀ ha).mpr
    push_cast
    have hln : (ds.length : ℝ) ≤ i.size := by exact_mod_cast hlen
    have hmn : (1 : ℝ) ≤ i.size := by exact_mod_cast hmpos
    have hp : 0 ≤ (ds.length : ℝ) + 1 + 6 * ds.length := by positivity
    nlinarith
  · intro c hc v
    exact ram_query_nine singletonProgram rfl rfl rfl c v.val
end DecrAlmostLinearSSSP.Decremental
end s2
section s3
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def guestReg (j : ℕ) : ℕ := 7 + 2 * j
def guestAddress (base a : ℕ) : ℕ := base + 2 * a + 1
def decodeGuest (c : Machine) : Machine where
  pc := c.natReg 2
  realReg := fun j => c.realReg (guestReg j)
  natReg := fun j => c.natReg (guestReg j)
  realMem := fun a => c.realMem (guestAddress (c.natReg 0) a)
  natMem := fun a => c.natMem (guestAddress (c.natReg 0) a)
  halted := c.natReg 4 == 1
  fault := c.natReg 5 == 1
  work := c.natReg 3
lemma guestAddress_injective (base : ℕ) : Function.Injective (guestAddress base) := by
  intro a b hab
  dsimp [guestAddress] at hab
  omega
lemma guestReg_injective : Function.Injective guestReg := by
  intro a b hab
  dsimp [guestReg] at hab
  omega
lemma update_guest_register {α : Type} (f : ℕ → α) (a : ℕ) (v : α) :
    (fun j => Function.update f (guestReg a) v (guestReg j)) =
      Function.update (fun j => f (guestReg j)) a v := by
  classical
  funext j
  by_cases hj : j = a
  · subst j; simp
  · have hh : guestReg j ≠ guestReg a := guestReg_injective.ne hj
    simp only [Function.update_of_ne hj, Function.update_of_ne hh]
lemma update_guest_memory {α : Type} (f : ℕ → α) (base a : ℕ) (v : α) :
    (fun j => Function.update f (guestAddress base a) v (guestAddress base j)) =
      Function.update (fun j => f (guestAddress base j)) a v := by
  classical
  funext j
  by_cases hj : j = a
  · subst j; simp
  · have hh : guestAddress base j ≠ guestAddress base a := (guestAddress_injective base).ne hj
    simp only [Function.update_of_ne hj, Function.update_of_ne hh]
lemma guestReg_ne_meta (j k : ℕ) (hk : k < 7) : guestReg j ≠ k := by
  dsimp [guestReg]
  omega
lemma guest_reg_write_preserves_even {α : Type} (f : ℕ → α) (a b : ℕ) (v : α) :
    Function.update f (guestReg a) v (2 * b) = f (2 * b) := by
  classical
  apply Function.update_of_ne
  dsimp [guestReg]
  omega
lemma guest_write_preserves_even {α : Type} (f : ℕ → α) (base a b : ℕ) (v : α) :
    Function.update f (guestAddress base a) v (base + 2 * b) = f (base + 2 * b) := by
  classical
  apply Function.update_of_ne
  dsimp [guestAddress]
  omega
lemma guest_write_preserves_prefix {α : Type} (f : ℕ → α) (base a b : ℕ) (v : α)
    (hb : b < base) : Function.update f (guestAddress base a) v b = f b := by
  classical
  apply Function.update_of_ne
  dsimp [guestAddress]
  omega
def embeddedInstruction (offset returnPC pc : ℕ) (ins : Instruction) : List Instruction :=
  let next := offset + 8 * (pc + 1)
  let header := [Instruction.natural 2 (pc + 1), .nadd 3 3 1]
  let simple := fun ins => header ++ [ins, .jump next, .jump next, .jump next, .jump next, .jump next]
  let mem := fun ins a => header ++ [.nadd 6 (guestReg a) (guestReg a), .nadd 6 6 0,
    .nadd 6 6 1, ins, .jump next, .jump next]
  match ins with
  | .rational d q => simple (.rational (guestReg d) q)
  | .natural d a => simple (.natural (guestReg d) a)
  | .cast d a => simple (.cast (guestReg d) (guestReg a))
  | .add d a b => simple (.add (guestReg d) (guestReg a) (guestReg b))
  | .sub d a b => simple (.sub (guestReg d) (guestReg a) (guestReg b))
  | .mul d a b => simple (.mul (guestReg d) (guestReg a) (guestReg b))
  | .div d a b => simple (.div (guestReg d) (guestReg a) (guestReg b))
  | .log d a => simple (.log (guestReg d) (guestReg a))
  | .nadd d a b => simple (.nadd (guestReg d) (guestReg a) (guestReg b))
  | .nsub d a b => simple (.nsub (guestReg d) (guestReg a) (guestReg b))
  | .load d a => mem (.load (guestReg d) 6) a
  | .store a d => mem (.store 6 (guestReg d)) a
  | .loadN d a => mem (.loadN (guestReg d) 6) a
  | .storeN a d => mem (.storeN 6 (guestReg d)) a
  | .jump t => header ++ [.natural 2 t, .jump (offset + 8 * t), .jump next, .jump next, .jump next, .jump next]
  | .less a b t => header ++ [.less (guestReg a) (guestReg b) (offset + 8 * pc + 5), .jump next,
    .jump next, .natural 2 t, .jump (offset + 8 * t), .jump next]
  | .lessN a b t => header ++ [.lessN (guestReg a) (guestReg b) (offset + 8 * pc + 5), .jump next,
    .jump next, .natural 2 t, .jump (offset + 8 * t), .jump next]
  | .halt => header ++ [.natural 4 1, .jump returnPC, .jump next, .jump next, .jump next, .jump next]
lemma embeddedInstruction_length (offset returnPC pc : ℕ) (ins : Instruction) :
    (embeddedInstruction offset returnPC pc ins).length = 8 := by
  cases ins <;> rfl
end DecrAlmostLinearSSSP.Decremental
end s3
section s4
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma machine_ext {c d : Machine} (hpc : c.pc = d.pc) (hreal : c.realReg = d.realReg)
    (hnat : c.natReg = d.natReg) (hrmem : c.realMem = d.realMem) (hnmem : c.natMem = d.natMem)
    (hhalt : c.halted = d.halted) (hfault : c.fault = d.fault) (hwork : c.work = d.work) : c = d := by
  cases c
  cases d
  simp_all
lemma decodeGuest_metadata (c : Machine) (pc work hostPC : ℕ) :
    decodeGuest {c with pc := hostPC, natReg := Function.update (Function.update c.natReg 2 pc) 3 work} =
      {decodeGuest c with pc := pc, work := work} := by
  classical
  have hg2 (j : ℕ) : guestReg j ≠ 2 := guestReg_ne_meta j 2 (by norm_num)
  have hg3 (j : ℕ) : guestReg j ≠ 3 := guestReg_ne_meta j 3 (by norm_num)
  apply machine_ext
  · simp [decodeGuest]
  · rfl
  · funext j
    simp only [decodeGuest, Function.update_of_ne (hg2 j), Function.update_of_ne (hg3 j)]
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [decodeGuest]
lemma embedded_header (host : Program) (c : Machine) (pc : ℕ)
    (hhalt : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1)) :
    decodeGuest (execute host c 2) = {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} := by
  classical
  let c1 : Machine := {c with pc := c.pc + 1, natReg := Function.update c.natReg 2 (pc + 1), work := c.work + 1}
  let c2 : Machine := {c1 with pc := c.pc + 2, natReg := Function.update c1.natReg 3 (c.natReg 3 + 1), work := c.work + 2}
  have hs1 : step host c = c1 := by simp [step, c1, hhalt, h0]
  have hs2 : step host c1 = c2 := by simp [step, c1, c2, hhalt, h1, hone]
  have hex : execute host c 2 = c2 := by
    change step host (step host c) = c2
    rw [hs1, hs2]
  rw [hex]
  exact decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
end DecrAlmostLinearSSSP.Decremental
end s4
section s5
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
noncomputable def instructionEffect (ins : Instruction) (c : Machine) : Machine := by
  classical
  exact match ins with
  | .rational a q => {c with realReg := Function.update c.realReg a (q : ℝ)}
  | .natural a b => {c with natReg := Function.update c.natReg a b}
  | .cast a b => {c with realReg := Function.update c.realReg a (c.natReg b : ℝ)}
  | .add a b e => {c with realReg := Function.update c.realReg a (c.realReg b + c.realReg e)}
  | .sub a b e => {c with realReg := Function.update c.realReg a (c.realReg b - c.realReg e)}
  | .mul a b e => {c with realReg := Function.update c.realReg a (c.realReg b * c.realReg e)}
  | .div a b e => {c with realReg := Function.update c.realReg a (c.realReg b / c.realReg e)}
  | .log a b => {c with realReg := Function.update c.realReg a (Real.log (c.realReg b))}
  | .nadd a b e => {c with natReg := Function.update c.natReg a (c.natReg b + c.natReg e)}
  | .nsub a b e => {c with natReg := Function.update c.natReg a (c.natReg b - c.natReg e)}
  | .load a b => {c with realReg := Function.update c.realReg a (c.realMem (c.natReg b))}
  | .store a b => {c with realMem := Function.update c.realMem (c.natReg a) (c.realReg b)}
  | .loadN a b => {c with natReg := Function.update c.natReg a (c.natMem (c.natReg b))}
  | .storeN a b => {c with natMem := Function.update c.natMem (c.natReg a) (c.natReg b)}
  | .jump t => {c with pc := t}
  | .less a b t => if c.realReg a < c.realReg b then {c with pc := t} else c
  | .lessN a b t => if c.natReg a < c.natReg b then {c with pc := t} else c
  | .halt => {c with halted := true}
lemma step_eq_effect (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) :
    step p c = instructionEffect ins {c with pc := c.pc + 1, work := c.work + 1} := by
  cases ins <;> simp only [step, hh, Bool.false_eq_true, if_false, hc, instructionEffect]
lemma decodeGuest_host_clock (c : Machine) (pc work : ℕ) :
    decodeGuest {c with pc := pc, work := work} = decodeGuest c := rfl
lemma decodeGuest_step_effect (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) :
    decodeGuest (step p c) = decodeGuest (instructionEffect ins c) := by
  rw [step_eq_effect p c ins hh hc]
  cases ins <;> simp only [instructionEffect]
  all_goals try split_ifs
  all_goals rfl
lemma decodeGuest_real_register (c : Machine) (a : ℕ) (value : ℝ) :
    decodeGuest {c with realReg := Function.update c.realReg (guestReg a) value} =
      {decodeGuest c with realReg := Function.update (decodeGuest c).realReg a value} := by
  classical
  apply machine_ext
  · rfl
  · exact update_guest_register _ _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
lemma decodeGuest_nat_register (c : Machine) (a value : ℕ) :
    decodeGuest {c with natReg := Function.update c.natReg (guestReg a) value} =
      {decodeGuest c with natReg := Function.update (decodeGuest c).natReg a value} := by
  classical
  have hm (k : ℕ) (hk : k < 7) :
      Function.update c.natReg (guestReg a) value k = c.natReg k :=
    Function.update_of_ne (guestReg_ne_meta a k hk).symm _ _
  apply machine_ext
  · exact hm 2 (by norm_num)
  · rfl
  · exact update_guest_register _ _ _
  · simp only [decodeGuest, hm 0 (by norm_num)]
  · simp only [decodeGuest, hm 0 (by norm_num)]
  · simp only [decodeGuest, hm 4 (by norm_num)]
  · simp only [decodeGuest, hm 5 (by norm_num)]
  · exact hm 3 (by norm_num)
lemma decodeGuest_real_memory (c : Machine) (a : ℕ) (value : ℝ) :
    decodeGuest {c with realMem := Function.update c.realMem (guestAddress (c.natReg 0) a) value} =
      {decodeGuest c with realMem := Function.update (decodeGuest c).realMem a value} := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · rfl
  · exact update_guest_memory _ _ _ _
  · rfl
  · rfl
  · rfl
  · rfl
lemma decodeGuest_nat_memory (c : Machine) (a value : ℕ) :
    decodeGuest {c with natMem := Function.update c.natMem (guestAddress (c.natReg 0) a) value} =
      {decodeGuest c with natMem := Function.update (decodeGuest c).natMem a value} := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact update_guest_memory _ _ _ _
  · rfl
  · rfl
  · rfl
lemma decodeGuest_scratch (c : Machine) (a : ℕ) :
    decodeGuest {c with natReg := Function.update c.natReg 6 a} = decodeGuest c := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · funext j
    exact Function.update_of_ne (guestReg_ne_meta j 6 (by norm_num)) _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
end DecrAlmostLinearSSSP.Decremental
end s5
section s6
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
def scalarTranslation : Instruction → Option Instruction
  | .rational d q => some (.rational (guestReg d) q)
  | .natural d a => some (.natural (guestReg d) a)
  | .cast d a => some (.cast (guestReg d) (guestReg a))
  | .add d a b => some (.add (guestReg d) (guestReg a) (guestReg b))
  | .sub d a b => some (.sub (guestReg d) (guestReg a) (guestReg b))
  | .mul d a b => some (.mul (guestReg d) (guestReg a) (guestReg b))
  | .div d a b => some (.div (guestReg d) (guestReg a) (guestReg b))
  | .log d a => some (.log (guestReg d) (guestReg a))
  | .nadd d a b => some (.nadd (guestReg d) (guestReg a) (guestReg b))
  | .nsub d a b => some (.nsub (guestReg d) (guestReg a) (guestReg b))
  | _ => none
lemma decodeGuest_scalar (ins translated : Instruction) (h : scalarTranslation ins = some translated)
    (c : Machine) : decodeGuest (instructionEffect translated c) = instructionEffect ins (decodeGuest c) := by
  cases ins <;> simp only [scalarTranslation] at h
  all_goals cases h
  all_goals simp only [instructionEffect, decodeGuest_real_register, decodeGuest_nat_register]
  all_goals rfl
lemma decodeGuest_load (c : Machine) (d a : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.load (guestReg d) 6) c) =
      instructionEffect (.load d a) (decodeGuest c) := by
  simp only [instructionEffect, decodeGuest_real_register, ha]
  rfl
lemma decodeGuest_loadN (c : Machine) (d a : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.loadN (guestReg d) 6) c) =
      instructionEffect (.loadN d a) (decodeGuest c) := by
  simp only [instructionEffect, decodeGuest_nat_register, ha]
  rfl
lemma decodeGuest_store (c : Machine) (a d : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.store 6 (guestReg d)) c) =
      instructionEffect (.store a d) (decodeGuest c) := by
  simp only [instructionEffect, ha, decodeGuest_real_memory]
  rfl
lemma decodeGuest_storeN (c : Machine) (a d : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.storeN 6 (guestReg d)) c) =
      instructionEffect (.storeN a d) (decodeGuest c) := by
  simp only [instructionEffect, ha, decodeGuest_nat_memory]
  rfl
end DecrAlmostLinearSSSP.Decremental
end s6
section s7
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma execute_add (p : Program) (c : Machine) (a b : ℕ) :
    execute p c (a + b) = execute p (execute p c a) b := by
  unfold execute
  rw [Nat.add_comm a b, Function.iterate_add_apply]
lemma host_jump (host : Program) (c : Machine) (target : ℕ)
    (hh : c.halted = false) (hc : host.code[c.pc]? = some (.jump target)) :
    execute host c 1 = {c with pc := target, work := c.work + 1} := by
  change step host c = _
  simp only [step, hh, Bool.false_eq_true, if_false, hc]
lemma host_scalar (host : Program) (c : Machine) (ins translated : Instruction)
    (htranslation : scalarTranslation ins = some translated)
    (hh : c.halted = false) (hc : host.code[c.pc]? = some translated) :
    decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) ∧
      (execute host c 1).pc = c.pc + 1 ∧ (execute host c 1).halted = false ∧
      (execute host c 1).work = c.work + 1 := by
  have hdecode : decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) := by
    change decodeGuest (step host c) = _
    rw [decodeGuest_step_effect host c translated hh hc, decodeGuest_scalar ins translated htranslation c]
  refine ⟨hdecode, ?_, ?_, ?_⟩
  all_goals cases ins <;> simp only [scalarTranslation] at htranslation
  all_goals cases htranslation
  all_goals simp only [execute, Function.iterate_one, step, hh, Bool.false_eq_true, if_false, hc]
end DecrAlmostLinearSSSP.Decremental
end s7
section s8
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma embedded_address (host : Program) (c : Machine) (a : ℕ)
    (hhalt : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.nadd 6 (guestReg a) (guestReg a)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 6 6 0))
    (h2 : host.code[c.pc + 2]? = some (.nadd 6 6 1)) :
    ∃ d, execute host c 3 = d ∧ decodeGuest d = decodeGuest c ∧
      d.natReg 6 = guestAddress (d.natReg 0) (d.natReg (guestReg a)) ∧
      d.pc = c.pc + 3 ∧ d.halted = false ∧ d.work = c.work + 3 ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let c1 : Machine := { c with pc := c.pc + 1, natReg := Function.update c.natReg 6 (c.natReg (guestReg a) + c.natReg (guestReg a)), work := c.work + 1 }
  let c2 : Machine := { c1 with pc := c.pc + 2, natReg := Function.update c1.natReg 6 (c1.natReg 6 + c1.natReg 0), work := c.work + 2 }
  let c3 : Machine := { c2 with pc := c.pc + 3, natReg := Function.update c2.natReg 6 (c2.natReg 6 + 1), work := c.work + 3 }
  have hs1 : step host c = c1 := by simp [step, c1, hhalt, h0]
  have hs2 : step host c1 = c2 := by simp [step, c1, c2, hhalt, h1]
  have hs3 : step host c2 = c3 := by simp [step, c1, c2, c3, hhalt, h2, hone]
  have hex : execute host c 3 = c3 := by
    change step host (step host (step host c)) = c3
    rw [hs1, hs2, hs3]
  have hd1 : decodeGuest c1 = decodeGuest c := decodeGuest_scratch c _
  have hd2 : decodeGuest c2 = decodeGuest c1 := decodeGuest_scratch c1 _
  have hd3 : decodeGuest c3 = decodeGuest c2 := decodeGuest_scratch c2 _
  refine ⟨c3, hex, hd3.trans (hd2.trans hd1), ?_, rfl, hhalt, rfl, rfl, rfl⟩
  have ha6 : guestReg a ≠ 6 := guestReg_ne_meta a 6 (by norm_num)
  simp [c3, c2, c1, guestAddress, ha6, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
end DecrAlmostLinearSSSP.Decremental
end s8
section s9
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def embeddedCodeAux (offset returnPC : ℕ) : ℕ → List Instruction → List Instruction
  | _, [] => []
  | pc, ins :: rest => embeddedInstruction offset returnPC pc ins ++ embeddedCodeAux offset returnPC (pc + 1) rest
def embeddedCode (offset returnPC : ℕ) (code : List Instruction) : List Instruction :=
  embeddedCodeAux offset returnPC 0 code
lemma embeddedCodeAux_length (offset returnPC start : ℕ) (code : List Instruction) :
    (embeddedCodeAux offset returnPC start code).length = 8 * code.length := by
  induction code generalizing start with
  | nil => rfl
  | cons ins rest ih =>
    simp only [embeddedCodeAux, List.length_append, embeddedInstruction_length, ih, List.length_cons]
    omega
lemma embeddedCode_length (offset returnPC : ℕ) (code : List Instruction) :
    (embeddedCode offset returnPC code).length = 8 * code.length := embeddedCodeAux_length _ _ _ _
lemma embeddedCodeAux_get (offset returnPC start : ℕ) (code : List Instruction)
    (pc slot : ℕ) (ins : Instruction) (hslot : slot < 8) (hins : code[pc]? = some ins) :
    (embeddedCodeAux offset returnPC start code)[8 * pc + slot]? =
      (embeddedInstruction offset returnPC (start + pc) ins)[slot]? := by
  induction code generalizing start pc with
  | nil => simp at hins
  | cons first rest ih =>
    cases pc with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hins
      subst ins
      simp only [embeddedCodeAux, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      rw [List.getElem?_append_left (by simpa only [embeddedInstruction_length] using hslot)]
    | succ pc =>
      simp only [List.getElem?_cons_succ] at hins
      rw [embeddedCodeAux, List.getElem?_append_right (by rw [embeddedInstruction_length]; omega)]
      have hidx : 8 * (pc + 1) + slot - 8 = 8 * pc + slot := by omega
      rw [embeddedInstruction_length, hidx]
      have hh := ih (start + 1) pc hins
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
lemma embeddedCode_get (offset returnPC : ℕ) (code : List Instruction)
    (pc slot : ℕ) (ins : Instruction) (hslot : slot < 8) (hins : code[pc]? = some ins) :
    (embeddedCode offset returnPC code)[8 * pc + slot]? = (embeddedInstruction offset returnPC pc ins)[slot]? := by
  simpa only [embeddedCode, Nat.zero_add] using embeddedCodeAux_get offset returnPC 0 code pc slot ins hslot hins
end DecrAlmostLinearSSSP.Decremental
end s9
section s10
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def headerState (c : Machine) (pc : ℕ) : Machine :=
  { c with
    pc := c.pc + 2
    work := c.work + 2
    natReg := Function.update (Function.update c.natReg 2 (pc + 1)) 3 (c.natReg 3 + 1) }
lemma embedded_header_exact (host : Program) (c : Machine) (pc : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1)) :
    execute host c 2 = headerState c pc := by
  classical
  change step host (step host c) = _
  simp [step, hh, h0, h1, hone, headerState]
lemma scalar_metadata (ins translated : Instruction) (ht : scalarTranslation ins = some translated)
    (c : Machine) :
    (instructionEffect translated c).natReg 0 = c.natReg 0 ∧
      (instructionEffect translated c).natReg 1 = c.natReg 1 ∧
      (instructionEffect translated c).fault = c.fault := by
  classical
  cases ins <;> simp only [scalarTranslation] at ht
  all_goals cases ht
  all_goals simp only [instructionEffect]
  all_goals try exact ⟨rfl, rfl, rfl⟩
  all_goals simp [Function.update_of_ne (guestReg_ne_meta _ 0 (by norm_num)).symm,
    Function.update_of_ne (guestReg_ne_meta _ 1 (by norm_num)).symm]
lemma embedded_scalar_macro (host : Program) (c : Machine) (pc offset : ℕ)
    (ins translated : Instruction) (ht : scalarTranslation ins = some translated)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some translated)
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1)))) :
    ∃ d, execute host c 4 = d ∧
      decodeGuest d = instructionEffect ins {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * (pc + 1) ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hbdecode : decodeGuest b = {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} :=
    decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
  have hbhalt : b.halted = false := hh
  have hbc : host.code[b.pc]? = some translated := h2
  obtain ⟨hdec, hpc, hh3, hw3⟩ := host_scalar host b ins translated ht hbhalt hbc
  let t := execute host b 1
  have hjc : host.code[t.pc]? = some (.jump (offset + 8 * (pc + 1))) := by
    change host.code[(execute host b 1).pc]? = _
    rw [hpc]
    simpa [b, headerState, Nat.add_assoc] using h3
  have hj := host_jump host t (offset + 8 * (pc + 1)) hh3 hjc
  let d : Machine := {t with pc := offset + 8 * (pc + 1), work := t.work + 1}
  have hd : execute host c 4 = d := by
    rw [show 4 = 2 + (1 + 1) by omega, execute_add, hb, execute_add]
    exact hj
  refine ⟨d, hd, ?_, rfl, ?_, hh3, ?_, ?_⟩
  · change decodeGuest t = _
    exact hdec.trans (congrArg (instructionEffect ins) hbdecode)
  · change (execute host b 1).work + 1 = c.work + 4
    rw [hw3]
    simp [b, headerState]
  · change (execute host b 1).natReg 0 = c.natReg 0
    change (step host b).natReg 0 = _
    rw [step_eq_effect host b translated hbhalt hbc]
    exact (scalar_metadata ins translated ht _).1
  · change (execute host b 1).natReg 1 = c.natReg 1
    change (step host b).natReg 1 = _
    rw [step_eq_effect host b translated hbhalt hbc]
    exact (scalar_metadata ins translated ht _).2.1
end DecrAlmostLinearSSSP.Decremental
end s10
section s11
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma decodeGuest_pc (c : Machine) (pc : ℕ) :
    decodeGuest {c with natReg := Function.update c.natReg 2 pc} = {decodeGuest c with pc := pc} := by
  classical
  apply machine_ext
  · simp [decodeGuest]
  · rfl
  · funext j
    exact Function.update_of_ne (guestReg_ne_meta j 2 (by norm_num)) _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
lemma decodeGuest_halt (c : Machine) :
    decodeGuest {c with natReg := Function.update c.natReg 4 1} = {decodeGuest c with halted := true} := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · funext j
    exact Function.update_of_ne (guestReg_ne_meta j 4 (by norm_num)) _ _
  · rfl
  · rfl
  · simp [decodeGuest]
  · rfl
  · rfl
lemma host_natural_jump (host : Program) (c : Machine) (reg value target : ℕ)
    (hh : c.halted = false)
    (h0 : host.code[c.pc]? = some (.natural reg value))
    (h1 : host.code[c.pc + 1]? = some (.jump target)) :
    execute host c 2 = {c with
      pc := target
      work := c.work + 2
      natReg := Function.update c.natReg reg value} := by
  classical
  change step host (step host c) = _
  simp [step, hh, h0, h1]
lemma embedded_jump_macro (host : Program) (c : Machine) (pc offset target : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural 2 target))
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * target))) :
    ∃ d, execute host c 4 = d ∧
      decodeGuest d = instructionEffect (.jump target) {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * target ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  let d : Machine := {b with pc := offset + 8 * target, work := b.work + 2, natReg := Function.update b.natReg 2 target}
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hd : execute host b 2 = d := host_natural_jump host b 2 target (offset + 8 * target) hh h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  refine ⟨d, ?_, ?_, rfl, ?_, hh, rfl, rfl⟩
  · rw [show 4 = 2 + 2 by omega, execute_add, hb, hd]
  · change decodeGuest {b with natReg := Function.update b.natReg 2 target} = _
    rw [decodeGuest_pc]
    have hbdec := decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
    change decodeGuest b = _ at hbdec
    rw [hbdec]
    rfl
  · dsimp [d, b, headerState]
lemma embedded_halt_macro (host : Program) (c : Machine) (pc returnPC : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural 4 1))
    (h3 : host.code[c.pc + 3]? = some (.jump returnPC)) :
    ∃ d, execute host c 4 = d ∧
      decodeGuest d = instructionEffect .halt {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = returnPC ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  let d : Machine := {b with pc := returnPC, work := b.work + 2, natReg := Function.update b.natReg 4 1}
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hd : execute host b 2 = d := host_natural_jump host b 4 1 returnPC hh h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  refine ⟨d, ?_, ?_, rfl, ?_, hh, rfl, rfl⟩
  · rw [show 4 = 2 + 2 by omega, execute_add, hb, hd]
  · change decodeGuest {b with natReg := Function.update b.natReg 4 1} = _
    rw [decodeGuest_halt]
    have hbdec := decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
    change decodeGuest b = _ at hbdec
    rw [hbdec]
    rfl
  · dsimp [d, b, headerState]
end DecrAlmostLinearSSSP.Decremental
end s11
section s12
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
def branchInstruction (natural : Bool) (a b target : ℕ) : Instruction :=
  if natural then .lessN a b target else .less a b target
def branchTest (natural : Bool) (c : Machine) (a b : ℕ) : Prop :=
  if natural then c.natReg a < c.natReg b else c.realReg a < c.realReg b
lemma host_branch (host : Program) (c : Machine) (natural : Bool) (a b target : ℕ)
    (hh : c.halted = false)
    (hc : host.code[c.pc]? = some (branchInstruction natural (guestReg a) (guestReg b) target)) :
    execute host c 1 = {c with
      pc := if branchTest natural (decodeGuest c) a b then target else c.pc + 1
      work := c.work + 1} := by
  cases natural <;> simp [execute, step, branchInstruction, branchTest, hh, hc, decodeGuest]
  all_goals split_ifs <;> rfl
lemma branchTest_header (natural : Bool) (c : Machine) (pc a b : ℕ) :
    branchTest natural (decodeGuest (headerState c pc)) a b = branchTest natural (decodeGuest c) a b := by
  cases natural
  · rfl
  · simp [branchTest, decodeGuest, headerState,
      Function.update_of_ne (guestReg_ne_meta a 2 (by norm_num)),
      Function.update_of_ne (guestReg_ne_meta a 3 (by norm_num)),
      Function.update_of_ne (guestReg_ne_meta b 2 (by norm_num)),
      Function.update_of_ne (guestReg_ne_meta b 3 (by norm_num))]
lemma branch_effect (natural : Bool) (c : Machine) (a b target : ℕ) :
    instructionEffect (branchInstruction natural a b target) c =
      if branchTest natural c a b then {c with pc := target} else c := by
  cases natural <;> simp [instructionEffect, branchInstruction, branchTest]
lemma embedded_branch_macro (host : Program) (c : Machine) (pc offset target : ℕ)
    (natural : Bool) (a b : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (branchInstruction natural (guestReg a) (guestReg b) (c.pc + 5)))
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))))
    (h5 : host.code[c.pc + 5]? = some (.natural 2 target))
    (h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * target))) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 5 ∧ execute host c steps = d ∧
      decodeGuest d = instructionEffect (branchInstruction natural a b target) {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * (decodeGuest d).pc ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let s := headerState c pc
  let g : Machine := {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1}
  have hs : execute host c 2 = s := embedded_header_exact host c pc hh hone h0 h1
  have hsdec : decodeGuest s = g := decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
  by_cases htake : branchTest natural g a b
  · let t : Machine := {s with pc := c.pc + 5, work := s.work + 1}
    have ht : execute host s 1 = t := by
      rw [host_branch host s natural a b (c.pc + 5) hh h2, hsdec, if_pos htake]
    let d : Machine := {t with pc := offset + 8 * target, work := t.work + 2, natReg := Function.update t.natReg 2 target}
    have hd : execute host t 2 = d := host_natural_jump host t 2 target (offset + 8 * target) hh h5 (by simpa [t, Nat.add_assoc] using h6)
    refine ⟨5, d, le_rfl, ?_, ?_, ?_, ?_, hh, rfl, rfl⟩
    · rw [show 5 = 2 + (1 + 2) by omega, execute_add, hs, execute_add, ht, hd]
    · change decodeGuest {t with natReg := Function.update t.natReg 2 target} = _
      rw [decodeGuest_pc, branch_effect, if_pos htake]
      exact congrArg (fun m : Machine => {m with pc := target}) hsdec
    · change offset + 8 * target = offset + 8 * (decodeGuest {t with natReg := Function.update t.natReg 2 target}).pc
      rw [decodeGuest_pc]
    · dsimp [d, t, s, headerState]
  · let t : Machine := {s with pc := c.pc + 3, work := s.work + 1}
    have ht : execute host s 1 = t := by
      rw [host_branch host s natural a b (c.pc + 5) hh h2, hsdec, if_neg htake]
      simp [t, s, headerState, Nat.add_assoc]
    let d : Machine := {t with pc := offset + 8 * (pc + 1), work := t.work + 1}
    have hd : execute host t 1 = d := host_jump host t (offset + 8 * (pc + 1)) hh h3
    refine ⟨4, d, by omega, ?_, ?_, ?_, ?_, hh, rfl, rfl⟩
    · rw [show 4 = 2 + (1 + 1) by omega, execute_add, hs, execute_add, ht, hd]
    · change decodeGuest s = _
      rw [branch_effect, if_neg htake]
      exact hsdec
    · change offset + 8 * (pc + 1) = offset + 8 * (decodeGuest s).pc
      rw [hsdec]
    · dsimp [d, t, s, headerState]
end DecrAlmostLinearSSSP.Decremental
end s12
section s13
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def memoryTranslation : Instruction → Option (Instruction × ℕ)
  | .load d a => some (.load (guestReg d) 6, a)
  | .loadN d a => some (.loadN (guestReg d) 6, a)
  | .store a d => some (.store 6 (guestReg d), a)
  | .storeN a d => some (.storeN 6 (guestReg d), a)
  | _ => none
lemma decodeGuest_memory (ins translated : Instruction) (a : ℕ)
    (ht : memoryTranslation ins = some (translated, a)) (c : Machine)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect translated c) = instructionEffect ins (decodeGuest c) := by
  cases ins <;> simp only [memoryTranslation] at ht
  all_goals cases ht
  · exact decodeGuest_load c _ _ ha
  · exact decodeGuest_store c _ _ ha
  · exact decodeGuest_loadN c _ _ ha
  · exact decodeGuest_storeN c _ _ ha
lemma host_memory (host : Program) (c : Machine) (ins translated : Instruction) (a : ℕ)
    (ht : memoryTranslation ins = some (translated, a))
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a)))
    (hh : c.halted = false) (hc : host.code[c.pc]? = some translated) :
    decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) ∧
      (execute host c 1).pc = c.pc + 1 ∧ (execute host c 1).halted = false ∧
      (execute host c 1).work = c.work + 1 ∧
      (execute host c 1).natReg 0 = c.natReg 0 ∧ (execute host c 1).natReg 1 = c.natReg 1 := by
  have hd : decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) := by
    change decodeGuest (step host c) = _
    rw [decodeGuest_step_effect host c translated hh hc, decodeGuest_memory ins translated a ht c ha]
  refine ⟨hd, ?_, ?_, ?_, ?_, ?_⟩
  all_goals cases ins <;> simp only [memoryTranslation] at ht
  all_goals cases ht
  all_goals simp [execute, step, hh, hc,
    Function.update_of_ne (guestReg_ne_meta _ 0 (by norm_num)).symm,
    Function.update_of_ne (guestReg_ne_meta _ 1 (by norm_num)).symm]
lemma embedded_memory_macro (host : Program) (c : Machine) (pc offset : ℕ)
    (ins translated : Instruction) (a : ℕ) (ht : memoryTranslation ins = some (translated, a))
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.nadd 6 (guestReg a) (guestReg a)))
    (h3 : host.code[c.pc + 3]? = some (.nadd 6 6 0))
    (h4 : host.code[c.pc + 4]? = some (.nadd 6 6 1))
    (h5 : host.code[c.pc + 5]? = some translated)
    (h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * (pc + 1)))) :
    ∃ d, execute host c 7 = d ∧
      decodeGuest d = instructionEffect ins {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * (pc + 1) ∧ d.work = c.work + 7 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hbdec : decodeGuest b = {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} :=
    decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
  obtain ⟨t, htx, htdec, hta, htpc, hth, htw, ht0, ht1⟩ :=
    embedded_address host b a hh hone h2
      (by simpa [b, headerState, Nat.add_assoc] using h3)
      (by simpa [b, headerState, Nat.add_assoc] using h4)
  have htc : host.code[t.pc]? = some translated := by
    rw [htpc]
    simpa [b, headerState, Nat.add_assoc] using h5
  obtain ⟨hdec, hpc, hhalt, hwork, hmeta0, hmeta1⟩ := host_memory host t ins translated a ht hta hth htc
  let u := execute host t 1
  have hjc : host.code[u.pc]? = some (.jump (offset + 8 * (pc + 1))) := by
    change host.code[(execute host t 1).pc]? = _
    rw [hpc, htpc]
    simpa [b, headerState, Nat.add_assoc] using h6
  have hj := host_jump host u (offset + 8 * (pc + 1)) hhalt hjc
  let d : Machine := {u with pc := offset + 8 * (pc + 1), work := u.work + 1}
  refine ⟨d, ?_, ?_, rfl, ?_, hhalt, ?_, ?_⟩
  · rw [show 7 = 2 + (3 + (1 + 1)) by omega, execute_add, hb, execute_add, htx, execute_add]
    exact hj
  · change decodeGuest u = _
    exact hdec.trans (congrArg (instructionEffect ins) (htdec.trans hbdec))
  · change (execute host t 1).work + 1 = c.work + 7
    rw [hwork, htw]
    simp [b, headerState]
  · change (execute host t 1).natReg 0 = c.natReg 0
    rw [hmeta0, ht0]
    rfl
  · change (execute host t 1).natReg 1 = c.natReg 1
    rw [hmeta1, ht1]
    rfl
end DecrAlmostLinearSSSP.Decremental
end s13
section s14
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def embeddedDestination (offset returnPC : ℕ) (g : Machine) : ℕ :=
  if g.halted then returnPC else offset + 8 * g.pc
lemma scalar_effect_control (ins tr : Instruction) (ht : scalarTranslation ins = some tr)
    (c : Machine) : (instructionEffect ins c).pc = c.pc ∧ (instructionEffect ins c).halted = c.halted := by
  cases ins <;> simp only [scalarTranslation] at ht
  all_goals cases ht
  all_goals exact ⟨rfl, rfl⟩
lemma memory_effect_control (ins tr : Instruction) (a : ℕ) (ht : memoryTranslation ins = some (tr, a))
    (c : Machine) : (instructionEffect ins c).pc = c.pc ∧ (instructionEffect ins c).halted = c.halted := by
  cases ins <;> simp only [memoryTranslation] at ht
  all_goals cases ht
  all_goals exact ⟨rfl, rfl⟩
lemma embedded_instruction_header (offset returnPC pc : ℕ) (ins : Instruction) :
    (embeddedInstruction offset returnPC pc ins)[0]? = some (.natural 2 (pc + 1)) ∧
    (embeddedInstruction offset returnPC pc ins)[1]? = some (.nadd 3 3 1) := by
  cases ins <;> exact ⟨rfl, rfl⟩
lemma embedded_macro (host : Program) (c : Machine) (pc offset returnPC : ℕ) (ins : Instruction)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hgh : (decodeGuest c).halted = false)
    (hpos : c.pc = offset + 8 * pc)
    (hcode : ∀ slot < 8, host.code[c.pc + slot]? = (embeddedInstruction offset returnPC pc ins)[slot]?) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 7 ∧ execute host c steps = d ∧
      decodeGuest d = instructionEffect ins {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = embeddedDestination offset returnPC (decodeGuest d) ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  have h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)) := by
    simpa only [Nat.add_zero] using (hcode 0 (by omega)).trans (embedded_instruction_header offset returnPC pc ins).1
  have h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1) :=
    (hcode 1 (by omega)).trans (embedded_instruction_header offset returnPC pc ins).2
  let g : Machine := {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1}
  by_cases hscalar : ∃ tr, scalarTranslation ins = some tr
  · obtain ⟨tr, ht⟩ := hscalar
    have h2 : host.code[c.pc + 2]? = some tr := by
      rw [hcode 2 (by omega)]
      cases ins <;> simp only [scalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))) := by
      rw [hcode 3 (by omega)]
      cases ins <;> simp only [scalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_scalar_macro host c pc offset ins tr ht hh hone h0 h1 h2 h3
    refine ⟨4, d, by omega, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
    rw [hpc, hdec]
    have hg := scalar_effect_control ins tr ht g
    change offset + 8 * (pc + 1) = embeddedDestination offset returnPC (instructionEffect ins g)
    simp only [embeddedDestination, hg.1, hg.2]
    simp [g, hgh]
  · by_cases hmemory : ∃ tr a, memoryTranslation ins = some (tr, a)
    · obtain ⟨tr, a, ht⟩ := hmemory
      have h2 : host.code[c.pc + 2]? = some (.nadd 6 (guestReg a) (guestReg a)) := by
        rw [hcode 2 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h3 : host.code[c.pc + 3]? = some (.nadd 6 6 0) := by
        rw [hcode 3 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h4 : host.code[c.pc + 4]? = some (.nadd 6 6 1) := by
        rw [hcode 4 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h5 : host.code[c.pc + 5]? = some tr := by
        rw [hcode 5 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * (pc + 1))) := by
        rw [hcode 6 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_memory_macro host c pc offset ins tr a ht hh hone h0 h1 h2 h3 h4 h5 h6
      refine ⟨7, d, le_rfl, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
      rw [hpc, hdec]
      have hg := memory_effect_control ins tr a ht g
      change offset + 8 * (pc + 1) = embeddedDestination offset returnPC (instructionEffect ins g)
      simp only [embeddedDestination, hg.1, hg.2]
      simp [g, hgh]
    · cases ins with
      | jump target =>
        have h2 : host.code[c.pc + 2]? = some (.natural 2 target) := by simpa [embeddedInstruction] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * target)) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_jump_macro host c pc offset target hh hone h0 h1 h2 h3
        refine ⟨4, d, by omega, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        rw [hpc, hdec]
        simp [embeddedDestination, instructionEffect, hgh]
      | halt =>
        have h2 : host.code[c.pc + 2]? = some (.natural 4 1) := by simpa [embeddedInstruction] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump returnPC) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_halt_macro host c pc returnPC hh hone h0 h1 h2 h3
        refine ⟨4, d, by omega, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        rw [hpc, hdec]
        simp [embeddedDestination, instructionEffect]
      | less a b target =>
        have h2 : host.code[c.pc + 2]? = some (branchInstruction false (guestReg a) (guestReg b) (c.pc + 5)) := by
          simpa [embeddedInstruction, branchInstruction, hpos] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        have h5 : host.code[c.pc + 5]? = some (.natural 2 target) := by simpa [embeddedInstruction] using hcode 5 (by omega)
        have h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * target)) := by simpa [embeddedInstruction] using hcode 6 (by omega)
        obtain ⟨t, d, ht, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_branch_macro host c pc offset target false a b hh hone h0 h1 h2 h3 h5 h6
        refine ⟨t, d, ht.trans (by omega), hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        have hdh : (decodeGuest d).halted = false := by
          rw [hdec, branch_effect]
          split_ifs <;> exact hgh
        simpa [embeddedDestination, hdh] using hpc
      | lessN a b target =>
        have h2 : host.code[c.pc + 2]? = some (branchInstruction true (guestReg a) (guestReg b) (c.pc + 5)) := by
          simpa [embeddedInstruction, branchInstruction, hpos] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        have h5 : host.code[c.pc + 5]? = some (.natural 2 target) := by simpa [embeddedInstruction] using hcode 5 (by omega)
        have h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * target)) := by simpa [embeddedInstruction] using hcode 6 (by omega)
        obtain ⟨t, d, ht, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_branch_macro host c pc offset target true a b hh hone h0 h1 h2 h3 h5 h6
        refine ⟨t, d, ht.trans (by omega), hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        have hdh : (decodeGuest d).halted = false := by
          rw [hdec, branch_effect]
          split_ifs <;> exact hgh
        simpa [embeddedDestination, hdh] using hpc
      | _ => simp_all [scalarTranslation, memoryTranslation]
end DecrAlmostLinearSSSP.Decremental
end s14
section s15
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def EmbedsCode (host guest : Program) (offset returnPC : ℕ) : Prop :=
  ∀ pc ins, guest.code[pc]? = some ins → ∀ slot < 8,
    host.code[offset + 8 * pc + slot]? = (embeddedInstruction offset returnPC pc ins)[slot]?
lemma embedded_single_step (host guest : Program) (offset returnPC : ℕ)
    (hcode : EmbedsCode host guest offset returnPC) (c : Machine)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hgh : (decodeGuest c).halted = false)
    (hpos : c.pc = embeddedDestination offset returnPC (decodeGuest c))
    (ins : Instruction) (hc : guest.code[(decodeGuest c).pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 7 ∧ execute host c steps = d ∧
      decodeGuest d = step guest (decodeGuest c) ∧
      d.pc = embeddedDestination offset returnPC (decodeGuest d) ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  have hp : c.pc = offset + 8 * (decodeGuest c).pc := by simpa [embeddedDestination, hgh] using hpos
  obtain ⟨steps, d, hs, hd, hdec, hdpc, hw, hhalt, hm0, hm1⟩ :=
    embedded_macro host c (decodeGuest c).pc offset returnPC ins hh hone hgh hp
      (fun slot hslot => by rw [hp]; exact hcode _ _ hc slot hslot)
  refine ⟨steps, d, hs, hd, ?_, hdpc, hw, hhalt, hm0, hm1⟩
  rw [step_eq_effect guest (decodeGuest c) ins hgh hc]
  exact hdec
lemma execute_halted (p : Program) (c : Machine) (hh : c.halted = true) (t : ℕ) : execute p c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 = t + 1 by rfl, execute_add, ih]
    change step p c = c
    simp [step, hh]
lemma execute_succ_front (p : Program) (c : Machine) (t : ℕ) :
    execute p c (t + 1) = execute p (step p c) t := by
  rw [show t + 1 = 1 + t by omega, execute_add]
  rfl
lemma embedded_execution (host guest : Program) (offset returnPC : ℕ)
    (hcode : EmbedsCode host guest offset returnPC) (t : ℕ) (c : Machine)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hpos : c.pc = embeddedDestination offset returnPC (decodeGuest c))
    (hvalid : ∀ j < t, (execute guest (decodeGuest c) j).halted = false →
      ∃ ins, guest.code[(execute guest (decodeGuest c) j).pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 7 * t ∧ execute host c steps = d ∧
      decodeGuest d = execute guest (decodeGuest c) t ∧
      d.pc = embeddedDestination offset returnPC (decodeGuest d) ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  induction t generalizing c with
  | zero => exact ⟨0, c, le_rfl, rfl, rfl, hpos, rfl, hh, rfl, rfl⟩
  | succ t ih =>
    by_cases hgh : (decodeGuest c).halted = true
    · refine ⟨0, c, Nat.zero_le _, rfl, ?_, hpos, rfl, hh, rfl, rfl⟩
      exact (execute_halted guest (decodeGuest c) hgh (t + 1)).symm
    · have hghfalse : (decodeGuest c).halted = false := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins, hins⟩ := hvalid 0 (by omega) hghfalse
      obtain ⟨s, b, hs, hb, hbdec, hbpos, hbw, hbh, hb0, hb1⟩ :=
        embedded_single_step host guest offset returnPC hcode c hh hone hghfalse hpos ins hins
      have hbvalid : ∀ j < t, (execute guest (decodeGuest b) j).halted = false →
          ∃ ins, guest.code[(execute guest (decodeGuest b) j).pc]? = some ins := by
        intro j hj hhj
        rw [hbdec, ← execute_succ_front] at hhj ⊢
        exact hvalid (j + 1) (by omega) hhj
      obtain ⟨r, d, hr, hd, hddec, hdpos, hdw, hdh, hd0, hd1⟩ :=
        ih b hbh (hb1.trans hone) hbpos hbvalid
      refine ⟨s + r, d, ?_, ?_, ?_, hdpos, ?_, hdh, hd0.trans hb0, hd1.trans hb1⟩
      · omega
      · rw [execute_add, hb, hd]
      · rw [hddec, hbdec, ← execute_succ_front]
      · omega
end DecrAlmostLinearSSSP.Decremental
end s15
section s16
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma fault_step_persists (p : Program) (c : Machine) (hf : c.fault = true) : (step p c).fault = true := by
  classical
  unfold step
  split_ifs with hh
  · exact hf
  · cases hc : p.code[c.pc]? with
    | none => rfl
    | some ins =>
      cases ins <;> simp only
      all_goals try exact hf
      all_goals split_ifs <;> exact hf
lemma fault_execute_persists (p : Program) (c : Machine) (hf : c.fault = true) (t : ℕ) :
    (execute p c t).fault = true := by
  induction t with
  | zero => exact hf
  | succ t ih =>
    rw [execute_add]
    exact fault_step_persists p _ ih
lemma execution_prefix_no_fault (p : Program) (c : Machine) (t j : ℕ)
    (hj : j ≤ t) (hf : (execute p c t).fault = false) : (execute p c j).fault = false := by
  by_contra hh
  have ht : (execute p c j).fault = true := by
    cases hx : (execute p c j).fault <;> simp_all
  have hlast := fault_execute_persists p (execute p c j) ht (t - j)
  rw [← execute_add, Nat.add_sub_of_le hj, hf] at hlast
  contradiction
lemma execution_valid_code (p : Program) (c : Machine) (t : ℕ)
    (hf : (execute p c t).fault = false) :
    ∀ j < t, (execute p c j).halted = false → ∃ ins, p.code[(execute p c j).pc]? = some ins := by
  intro j hj hh
  cases hc : p.code[(execute p c j).pc]? with
  | some ins => exact ⟨ins, rfl⟩
  | none =>
    have hnof := execution_prefix_no_fault p c t (j + 1) (by omega) hf
    rw [execute_add] at hnof
    change (step p (execute p c j)).fault = false at hnof
    simp [step, hh, hc] at hnof
lemma step_work (p : Program) (c : Machine) (hh : c.halted = false) :
    (step p c).work = c.work + 1 := by
  classical
  unfold step
  rw [hh]
  simp only [Bool.false_eq_true, if_false]
  cases hc : p.code[c.pc]? with
  | none => rfl
  | some ins =>
    cases ins <;> simp only
    all_goals try rfl
    all_goals split_ifs <;> rfl
lemma step_of_halted (p : Program) (c : Machine) (hh : c.halted = true) : step p c = c := by
  unfold step
  rw [hh]
  rfl
lemma step_work_mono (p : Program) (c : Machine) : c.work ≤ (step p c).work := by
  by_cases hh : c.halted = true
  · rw [step_of_halted p c hh]
  · rw [step_work p c (Bool.eq_false_iff.mpr hh)]
    omega
lemma execute_work_mono (p : Program) (c : Machine) (t : ℕ) : c.work ≤ (execute p c t).work := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [execute_add]
    exact ih.trans (step_work_mono p _)
lemma terminating_prefix (p : Program) (c : Machine) (t : ℕ)
    (hh : (execute p c t).halted = true) :
    ∃ r ≤ t, execute p c r = execute p c t ∧ r = (execute p c t).work - c.work := by
  induction t generalizing c with
  | zero => exact ⟨0, le_rfl, rfl, by change 0 = c.work - c.work; omega⟩
  | succ t ih =>
    by_cases hch : c.halted = true
    · rw [execute_halted p c hch] at hh ⊢
      exact ⟨0, Nat.zero_le _, rfl, by simp⟩
    · have hchfalse : c.halted = false := Bool.eq_false_iff.mpr hch
      rw [execute_succ_front] at hh
      obtain ⟨r, hr, heq, hw⟩ := ih (step p c) hh
      refine ⟨r + 1, by omega, ?_, ?_⟩
      · rw [execute_succ_front, heq, ← execute_succ_front]
      · rw [execute_succ_front]
        have hstep := step_work p c hchfalse
        have hmono := execute_work_mono p (step p c) t
        omega
lemma embedded_ends (host guest : Program) (offset returnPC : ℕ)
    (hcode : EmbedsCode host guest offset returnPC) (c final : Machine)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hpos : c.pc = embeddedDestination offset returnPC (decodeGuest c))
    (he : Ends guest (decodeGuest c) final) :
    ∃ (steps : ℕ) (d : Machine), execute host c steps = d ∧ decodeGuest d = final ∧
      d.pc = returnPC ∧ d.work ≤ c.work + 7 * (final.work - (decodeGuest c).work) ∧
      d.halted = false ∧ d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  obtain ⟨t, ht, hhalt, hfault⟩ := he
  have hhalt' : (execute guest (decodeGuest c) t).halted = true := by rwa [ht]
  obtain ⟨r, _, hr, hw⟩ := terminating_prefix guest (decodeGuest c) t hhalt'
  have hrfinal : execute guest (decodeGuest c) r = final := hr.trans ht
  have hrfault : (execute guest (decodeGuest c) r).fault = false := by rwa [hrfinal]
  obtain ⟨s, d, hs, hd, hdec, hdpc, hdw, hdh, hd0, hd1⟩ :=
    embedded_execution host guest offset returnPC hcode r c hh hone hpos
      (execution_valid_code guest (decodeGuest c) r hrfault)
  refine ⟨s, d, hd, hdec.trans hrfinal, ?_, ?_, hdh, hd0, hd1⟩
  · rw [hdpc, hdec, hrfinal]
    simp [embeddedDestination, hhalt]
  · rw [ht] at hw
    omega
end DecrAlmostLinearSSSP.Decremental
end s16
section s17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def writesNat : Instruction → ℕ → Prop
  | .natural d _, k | .nadd d _ _, k | .nsub d _ _, k | .loadN d _, k => d = k
  | _, _ => False
def writesReal : Instruction → ℕ → Prop
  | .rational d _, k | .cast d _, k | .add d _ _, k | .sub d _ _, k
    | .mul d _ _, k | .div d _ _, k | .log d _, k | .load d _, k => d = k
  | _, _ => False
lemma step_nat_frame (p : Program) (c : Machine) (ins : Instruction) (k : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hwrite : ¬ writesNat ins k) :
    (step p c).natReg k = c.natReg k := by
  classical
  rw [step_eq_effect p c ins hh hc]
  cases ins <;> simp only [writesNat, instructionEffect] at hwrite ⊢
  all_goals try rfl
  all_goals try exact Function.update_of_ne (Ne.symm hwrite) _ _
  all_goals split_ifs <;> rfl
lemma step_real_frame (p : Program) (c : Machine) (ins : Instruction) (k : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hwrite : ¬ writesReal ins k) :
    (step p c).realReg k = c.realReg k := by
  classical
  rw [step_eq_effect p c ins hh hc]
  cases ins <;> simp only [writesReal, instructionEffect] at hwrite ⊢
  all_goals try rfl
  all_goals try exact Function.update_of_ne (Ne.symm hwrite) _ _
  all_goals split_ifs <;> rfl
lemma execute_nat_frame (p : Program) (c : Machine) (t k : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins → ¬ writesNat ins k) :
    (execute p c t).natReg k = c.natReg k := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).natReg k = _
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhfalse := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step, hhfalse, Bool.false_eq_true, if_false, hc] using hi
      | some ins => rw [step_nat_frame p _ ins k hhfalse hc (hcode t (by omega) ins hc), hi]
lemma execute_real_frame (p : Program) (c : Machine) (t k : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins → ¬ writesReal ins k) :
    (execute p c t).realReg k = c.realReg k := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).realReg k = _
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhfalse := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step, hhfalse, Bool.false_eq_true, if_false, hc] using hi
      | some ins => rw [step_real_frame p _ ins k hhfalse hc (hcode t (by omega) ins hc), hi]
end DecrAlmostLinearSSSP.Decremental
end s17
section s18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def instructionRegisters : Instruction → List ℕ
  | .rational d _ | .natural d _ => [d]
  | .cast d a | .log d a | .load d a | .loadN d a => [d,a]
  | .add d a b | .sub d a b | .mul d a b | .div d a b | .nadd d a b | .nsub d a b => [d,a,b]
  | .store a d | .storeN a d => [a,d]
  | .less a b _ | .lessN a b _ => [a,b]
  | .jump _ | .halt => []
def registerBound (code : List Instruction) : ℕ := 8+(code.flatMap instructionRegisters).sum
lemma registerBound_ge (code : List Instruction) : 8 ≤ registerBound code := by unfold registerBound;omega
lemma register_operand_bound (code : List Instruction) (ins : Instruction) (hi : ins ∈ code)
    (j : ℕ) (hj : j ∈ instructionRegisters ins) : j < registerBound code := by
  have hmem : j ∈ code.flatMap instructionRegisters := List.mem_flatMap.mpr ⟨ins,hi,hj⟩
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) j hmem
  unfold registerBound
  omega
lemma writesNat_operand (ins : Instruction) (j : ℕ) (h : writesNat ins j) : j ∈ instructionRegisters ins := by
  cases ins <;> simp only [writesNat] at h
  all_goals try contradiction
  all_goals subst j; simp [instructionRegisters]
lemma writesReal_operand (ins : Instruction) (j : ℕ) (h : writesReal ins j) : j ∈ instructionRegisters ins := by
  cases ins <;> simp only [writesReal] at h
  all_goals try contradiction
  all_goals subst j; simp [instructionRegisters]
lemma execute_nat_tail (p : Program) (c : Machine) (t j : ℕ) (hj : registerBound p.code ≤ j) :
    (execute p c t).natReg j = c.natReg j := by
  apply execute_nat_frame
  intro n hn ins hins hwrite
  have hmem := List.mem_of_getElem? hins
  have hbound := register_operand_bound p.code ins hmem j (writesNat_operand ins j hwrite)
  omega
lemma execute_real_tail (p : Program) (c : Machine) (t j : ℕ) (hj : registerBound p.code ≤ j) :
    (execute p c t).realReg j = c.realReg j := by
  apply execute_real_frame
  intro n hn ins hins hwrite
  have hmem := List.mem_of_getElem? hins
  have hbound := register_operand_bound p.code ins hmem j (writesReal_operand ins j hwrite)
  omega
def ZeroRegisterTail (bound : ℕ) (c : Machine) : Prop :=
  ∀ j, bound ≤ j → c.natReg j = 0 ∧ c.realReg j = 0
lemma ZeroRegisterTail.execute {p : Program} {c : Machine} (h : ZeroRegisterTail (registerBound p.code) c) (t : ℕ) :
    ZeroRegisterTail (registerBound p.code) (execute p c t) := by
  intro j hj
  rw [execute_nat_tail p c t j hj,execute_real_tail p c t j hj]
  exact h j hj
lemma ZeroRegisterTail.ends {p : Program} {c d : Machine} (h : ZeroRegisterTail (registerBound p.code) c)
    (he : Ends p c d) : ZeroRegisterTail (registerBound p.code) d := by
  obtain ⟨t,rfl,_,_⟩ := he
  exact h.execute t
lemma initialMachine_zero_tail (p : Program) (i : Input) : ZeroRegisterTail (registerBound p.code) (initialMachine p i) := by
  intro j hj
  have hb := registerBound_ge p.code
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  have h3 : j ≠ 3 := by omega
  have h4 : j ≠ 4 := by omega
  simp [initialMachine,h0,h1,h2,h3,h4]
lemma ZeroRegisterTail.deletion {p : Program} {c : Machine} (h : ZeroRegisterTail (registerBound p.code) c)
    (e : ℕ) : ZeroRegisterTail (registerBound p.code) (deletionMachine p c e) := by
  intro j hj
  have hb := registerBound_ge p.code
  have h5 : j ≠ 5 := by omega
  simpa only [deletionMachine,resume,Function.update_of_ne h5] using h j hj
lemma OnlineRun.zero_register_tail {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : ∀ c ∈ cs, ZeroRegisterTail (registerBound p.code) c := by
  induction h with
  | @init c he =>
    intro d hd
    have hd' : d = c := by simpa using hd
    subst d
    exact (initialMachine_zero_tail p i).ends he
  | @next ds cs c d hrun hlast e hend ih =>
    intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · exact ih z hz
    · have hz' : z = d := by simpa using hz
      subst z
      exact ((ih c (List.mem_of_getLast? hlast)).deletion e.val).ends hend
end DecrAlmostLinearSSSP.Decremental
end s18
section s19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
structure LowData (bound : ℕ) (host guest : Machine) : Prop where
  natural : ∀ j<bound, host.natReg j=guest.natReg j
  real : ∀ j<bound, host.realReg j=guest.realReg j
  natMem : host.natMem=guest.natMem
  realMem : host.realMem=guest.realMem
lemma LowData.refl (bound : ℕ) (c : Machine) : LowData bound c c := ⟨fun _ _ => rfl,fun _ _ => rfl,rfl,rfl⟩
lemma LowData.symm {bound : ℕ} {host guest : Machine} (h : LowData bound host guest) : LowData bound guest host :=
  ⟨fun j hj => (h.natural j hj).symm,fun j hj => (h.real j hj).symm,h.natMem.symm,h.realMem.symm⟩
lemma LowData.trans {bound : ℕ} {a b c : Machine} (h : LowData bound a b) (h' : LowData bound b c) : LowData bound a c :=
  ⟨fun j hj => (h.natural j hj).trans (h'.natural j hj),fun j hj => (h.real j hj).trans (h'.real j hj),h.natMem.trans h'.natMem,h.realMem.trans h'.realMem⟩
lemma LowData.natural_update {bound : ℕ} {host guest : Machine} (h : LowData bound host guest)
    (a value other : ℕ) (hv : value=other) :
    LowData bound {host with natReg := Function.update host.natReg a value} {guest with natReg := Function.update guest.natReg a other} := by
  subst other
  refine ⟨?_,h.real,h.natMem,h.realMem⟩
  intro j hj
  by_cases he : j=a
  · subst j;simp
  · simpa only [Function.update_of_ne he] using h.natural j hj
lemma LowData.real_update {bound : ℕ} {host guest : Machine} (h : LowData bound host guest)
    (a : ℕ) (value other : ℝ) (hv : value=other) :
    LowData bound {host with realReg := Function.update host.realReg a value} {guest with realReg := Function.update guest.realReg a other} := by
  subst other
  refine ⟨h.natural,?_,h.natMem,h.realMem⟩
  intro j hj
  by_cases he : j=a
  · subst j;simp
  · simpa only [Function.update_of_ne he] using h.real j hj
lemma LowData.natural_memory {bound : ℕ} {host guest : Machine} (h : LowData bound host guest)
    (a b value other : ℕ) (ha : a=b) (hv : value=other) :
    LowData bound {host with natMem := Function.update host.natMem a value} {guest with natMem := Function.update guest.natMem b other} := by
  subst b;subst other
  exact ⟨h.natural,h.real,by rw [h.natMem],h.realMem⟩
lemma LowData.real_memory {bound : ℕ} {host guest : Machine} (h : LowData bound host guest)
    (a b : ℕ) (value other : ℝ) (ha : a=b) (hv : value=other) :
    LowData bound {host with realMem := Function.update host.realMem a value} {guest with realMem := Function.update guest.realMem b other} := by
  subst b;subst other
  exact ⟨h.natural,h.real,h.natMem,by rw [h.realMem]⟩
lemma LowData.clock {bound : ℕ} {host guest : Machine} (h : LowData bound host guest)
    (hp gp hw gw : ℕ) :
    LowData bound {host with pc := hp,work := hw} {guest with pc := gp,work := gw} :=
  ⟨h.natural,h.real,h.natMem,h.realMem⟩
lemma LowData.effect {bound : ℕ} {host guest : Machine} (h : LowData bound host guest)
    (ins : Instruction) (hb : ∀ j∈instructionRegisters ins, j<bound) :
    LowData bound (instructionEffect ins host) (instructionEffect ins guest) := by
  classical
  cases ins with
  | rational a q => exact h.real_update a _ _ rfl
  | natural a v => exact h.natural_update a v v rfl
  | cast a b => exact h.real_update a _ _ (by rw [h.natural b (hb b (by simp [instructionRegisters]))])
  | add a b c => exact h.real_update a _ _ (by rw [h.real b (hb b (by simp [instructionRegisters])),h.real c (hb c (by simp [instructionRegisters]))])
  | sub a b c => exact h.real_update a _ _ (by rw [h.real b (hb b (by simp [instructionRegisters])),h.real c (hb c (by simp [instructionRegisters]))])
  | mul a b c => exact h.real_update a _ _ (by rw [h.real b (hb b (by simp [instructionRegisters])),h.real c (hb c (by simp [instructionRegisters]))])
  | div a b c => exact h.real_update a _ _ (by rw [h.real b (hb b (by simp [instructionRegisters])),h.real c (hb c (by simp [instructionRegisters]))])
  | log a b => exact h.real_update a _ _ (by rw [h.real b (hb b (by simp [instructionRegisters]))])
  | nadd a b c => exact h.natural_update a _ _ (by rw [h.natural b (hb b (by simp [instructionRegisters])),h.natural c (hb c (by simp [instructionRegisters]))])
  | nsub a b c => exact h.natural_update a _ _ (by rw [h.natural b (hb b (by simp [instructionRegisters])),h.natural c (hb c (by simp [instructionRegisters]))])
  | load a b => exact h.real_update a _ _ (by rw [h.realMem,h.natural b (hb b (by simp [instructionRegisters]))])
  | loadN a b => exact h.natural_update a _ _ (by rw [h.natMem,h.natural b (hb b (by simp [instructionRegisters]))])
  | store a b => exact h.real_memory _ _ _ _ (h.natural a (hb a (by simp [instructionRegisters]))) (h.real b (hb b (by simp [instructionRegisters])))
  | storeN a b => exact h.natural_memory _ _ _ _ (h.natural a (hb a (by simp [instructionRegisters]))) (h.natural b (hb b (by simp [instructionRegisters])))
  | jump pc => exact ⟨h.natural,h.real,h.natMem,h.realMem⟩
  | halt => exact ⟨h.natural,h.real,h.natMem,h.realMem⟩
  | less a b pc => simp only [instructionEffect];split_ifs <;> exact ⟨h.natural,h.real,h.natMem,h.realMem⟩
  | lessN a b pc => simp only [instructionEffect];split_ifs <;> exact ⟨h.natural,h.real,h.natMem,h.realMem⟩
end DecrAlmostLinearSSSP.Decremental.Relocation
end s19
section s20
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
def block (offset returnPC pc : ℕ) (ins : Instruction) : List Instruction :=
  let next := offset+2*(pc+1)
  match ins with
  | .jump dest => [.jump (offset+2*dest),.jump next]
  | .less a b dest => [.less a b (offset+2*dest),.jump next]
  | .lessN a b dest => [.lessN a b (offset+2*dest),.jump next]
  | .halt => [.jump returnPC,.jump returnPC]
  | ins => [ins,.jump next]
def codeAux (offset returnPC : ℕ) : ℕ → List Instruction → List Instruction
  | _,[] => []
  | pc,ins::rest => block offset returnPC pc ins++codeAux offset returnPC (pc+1) rest
def code (offset returnPC : ℕ) (source : List Instruction) : List Instruction := codeAux offset returnPC 0 source
lemma block_length (offset returnPC pc : ℕ) (ins : Instruction) : (block offset returnPC pc ins).length=2 := by cases ins <;> rfl
lemma codeAux_length (offset returnPC pc : ℕ) (source : List Instruction) : (codeAux offset returnPC pc source).length=2*source.length := by
  induction source generalizing pc with
  | nil => rfl
  | cons ins rest ih => simp only [codeAux,List.length_append,block_length,ih,List.length_cons];omega
lemma code_length (offset returnPC : ℕ) (source : List Instruction) : (code offset returnPC source).length=2*source.length := codeAux_length _ _ _ _
lemma codeAux_lookup (offset returnPC pc : ℕ) (source : List Instruction) (j : ℕ) (ins : Instruction)
    (h : source[j]?=some ins) (slot : ℕ) (hs : slot<2) :
    (codeAux offset returnPC pc source)[2*j+slot]?=(block offset returnPC (pc+j) ins)[slot]? := by
  induction source generalizing pc j with
  | nil => simp at h
  | cons first rest ih =>
    cases j with
    | zero =>
      have hi : first=ins := Option.some.inj h
      subst first
      simp only [codeAux,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
      exact List.getElem?_append_left (by rwa [block_length])
    | succ j =>
      have hj : (block offset returnPC pc first).length ≤ 2*(j+1)+slot := by rw [block_length];omega
      change (block offset returnPC pc first ++ codeAux offset returnPC (pc+1) rest)[2*(j+1)+slot]? = _
      rw [List.getElem?_append_right hj,block_length]
      have hidx : 2*(j+1)+slot-2=2*j+slot := by omega
      rw [hidx,ih (pc+1) j h]
      congr 2
      omega
lemma code_lookup (offset returnPC : ℕ) (source : List Instruction) (pc : ℕ) (ins : Instruction)
    (h : source[pc]?=some ins) (slot : ℕ) (hs : slot<2) :
    (code offset returnPC source)[2*pc+slot]?=(block offset returnPC pc ins)[slot]? := by
  simpa only [code,Nat.zero_add] using codeAux_lookup offset returnPC 0 source pc ins h slot hs
def Embeds (host guest : Program) (offset returnPC : ℕ) : Prop :=
  ∀ pc ins, guest.code[pc]?=some ins → ∀ slot<2,
    host.code[offset+2*pc+slot]?=(block offset returnPC pc ins)[slot]?
end DecrAlmostLinearSSSP.Decremental.Relocation
end s20
section s21
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def Straight : Instruction → Prop
  | .jump _ | .less _ _ _ | .lessN _ _ _ | .halt => False
  | _ => True
def ModifiesMemory : Instruction → Prop
  | .store _ _ | .storeN _ _ => True
  | _ => False
lemma step_straight (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hs : Straight ins) :
    (step p c).pc = c.pc + 1 ∧ (step p c).halted = false ∧ (step p c).work = c.work + 1 := by
  cases ins <;> simp only [Straight] at hs
  all_goals try contradiction
  all_goals simp only [step,hh,Bool.false_eq_true,if_false,hc,and_self]
lemma straight_prefix (p : Program) (c : Machine) (n : ℕ) (hh : c.halted = false)
    (hcode : ∀ j < n, ∃ ins, p.code[c.pc+j]? = some ins ∧ Straight ins) :
    ∀ j ≤ n, (execute p c j).pc = c.pc+j ∧ (execute p c j).halted = false ∧
      (execute p c j).work = c.work+j := by
  intro j hj
  induction j with
  | zero => exact ⟨rfl,hh,rfl⟩
  | succ j ih =>
    obtain ⟨hpc,hhalt,hwork⟩ := ih (by omega)
    obtain ⟨ins,hins,hstraight⟩ := hcode j (by omega)
    have hc : p.code[(execute p c j).pc]? = some ins := by rwa [hpc]
    have hs := step_straight p (execute p c j) ins hhalt hc hstraight
    rw [execute_add]
    change (step p (execute p c j)).pc = _ ∧ (step p (execute p c j)).halted = _ ∧ (step p (execute p c j)).work = _
    rw [hs.1,hs.2.1,hs.2.2,hpc,hwork]
    exact ⟨rfl,rfl,rfl⟩
lemma step_memory_frame (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hs : ¬ ModifiesMemory ins) :
    (step p c).realMem = c.realMem ∧ (step p c).natMem = c.natMem := by
  cases ins <;> simp only [ModifiesMemory] at hs
  all_goals try contradiction
  all_goals simp only [step,hh,Bool.false_eq_true,if_false,hc]
  all_goals try trivial
  all_goals split_ifs <;> simp
lemma execute_memory_frame (p : Program) (c : Machine) (t : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins → ¬ ModifiesMemory ins) :
    (execute p c t).realMem = c.realMem ∧ (execute p c t).natMem = c.natMem := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).realMem = c.realMem ∧ (step p (execute p c t)).natMem = c.natMem
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhfalse := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step,hhfalse,Bool.false_eq_true,if_false,hc] using hi
      | some ins =>
        have hs := step_memory_frame p _ ins hhfalse hc (hcode t (by omega) ins hc)
        exact ⟨hs.1.trans hi.1,hs.2.trans hi.2⟩
end DecrAlmostLinearSSSP.Decremental
end s21
section s22
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
noncomputable def destination (offset returnPC : ℕ) (g : Machine) : ℕ := if g.halted then returnPC else offset+2*g.pc
structure Rep (bound offset returnPC : ℕ) (host guest : Machine) : Prop where
  data : LowData bound host guest
  position : host.pc=destination offset returnPC guest
  running : host.halted=false
  fault : host.fault=false
lemma effect_fault (ins : Instruction) (c : Machine) : (instructionEffect ins c).fault=c.fault := by
  cases ins <;> simp only [instructionEffect]
  all_goals first | rfl | (split_ifs <;> rfl)
lemma effect_nat_frame (ins : Instruction) (c : Machine) (j : ℕ) (hw : ¬writesNat ins j) :
    (instructionEffect ins c).natReg j=c.natReg j := by
  cases ins <;> simp only [writesNat,instructionEffect] at hw ⊢
  all_goals first | rfl | exact Function.update_of_ne (Ne.symm hw) _ _ | (split_ifs <;> rfl)
lemma not_write_high (ins : Instruction) (bound j : ℕ) (hb : ∀ k∈instructionRegisters ins, k<bound) (hj : bound≤j) :
    ¬writesNat ins j := by
  intro hw
  have hh := hb j (writesNat_operand ins j hw)
  omega
lemma block_straight (offset returnPC pc : ℕ) (ins : Instruction) (hs : Straight ins) :
    block offset returnPC pc ins=[ins,.jump (offset+2*(pc+1))] := by
  cases ins <;> simp only [Straight] at hs
  all_goals first | contradiction | rfl
end DecrAlmostLinearSSSP.Decremental.Relocation
end s22
section s23
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
lemma straight_step (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (c g : Machine) (hr : Rep bound offset returnPC c g) (hg : g.halted=false)
    (ins : Instruction) (hc : guest.code[g.pc]?=some ins) (hb : ∀ j∈instructionRegisters ins, j<bound) (hs : Straight ins) :
    ∃ d, execute host c 2=d ∧ Rep bound offset returnPC d (step guest g) ∧
      d.work=c.work+2 ∧ d.natReg bound=c.natReg bound := by
  have hp : c.pc=offset+2*g.pc := by simpa only [destination,hg,Bool.false_eq_true,if_false] using hr.position
  have hblock := block_straight offset returnPC g.pc ins hs
  have h0 := hcode g.pc ins hc 0 (by omega)
  have h1 := hcode g.pc ins hc 1 (by omega)
  rw [hblock] at h0 h1
  have hc0 : host.code[c.pc]?=some ins := by simpa only [hp,Nat.add_zero,List.getElem?_cons_zero] using h0
  let b := step host c
  have hf := step_straight host c ins hr.running hc0 hs
  have hgf := step_straight guest g ins hg hc hs
  have hc1 : host.code[b.pc]?=some (.jump (offset+2*(g.pc+1))) := by
    rw [hf.1,hp]
    exact h1
  let d : Machine := {b with pc := offset+2*(g.pc+1),work := b.work+1}
  have hbd : step host b=d := by
    rw [step_eq_effect host b (.jump (offset+2*(g.pc+1))) hf.2.1 hc1]
    rfl
  have hdata1 : LowData bound b (step guest g) := by
    change LowData bound (step host c) (step guest g)
    rw [step_eq_effect host c ins hr.running hc0,step_eq_effect guest g ins hg hc]
    exact (hr.data.clock (c.pc+1) (g.pc+1) (c.work+1) (g.work+1)).effect ins hb
  have hbf : b.fault=false := by
    change (step host c).fault=false
    rw [step_eq_effect host c ins hr.running hc0,effect_fault]
    exact hr.fault
  have htag : b.natReg bound=c.natReg bound :=
    step_nat_frame host c ins bound hr.running hc0 (not_write_high ins bound bound hb le_rfl)
  refine ⟨d,?_,⟨?_,?_,hf.2.1,hbf⟩,?_,htag⟩
  · change step host (step host c)=d
    exact hbd
  · exact ⟨hdata1.natural,hdata1.real,hdata1.natMem,hdata1.realMem⟩
  · change offset+2*(g.pc+1)=destination offset returnPC (step guest g)
    simp only [destination,hgf.2.1,Bool.false_eq_true,if_false,hgf.1]
  · change b.work+1=c.work+2
    rw [hf.2.2]
end DecrAlmostLinearSSSP.Decremental.Relocation
end s23
section s24
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
lemma jump_step (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (c g : Machine) (hr : Rep bound offset returnPC c g) (hg : g.halted=false)
    (dest : ℕ) (hc : guest.code[g.pc]?=some (.jump dest)) :
    ∃ d, execute host c 1=d ∧ Rep bound offset returnPC d (step guest g) ∧
      d.work=c.work+1 ∧ d.natReg bound=c.natReg bound := by
  have hp : c.pc=offset+2*g.pc := by simpa only [destination,hg,Bool.false_eq_true,if_false] using hr.position
  have h0 := hcode g.pc (.jump dest) hc 0 (by omega)
  have hc0 : host.code[c.pc]?=some (.jump (offset+2*dest)) := by simpa only [hp,Nat.add_zero,block,List.getElem?_cons_zero] using h0
  let d : Machine := {c with pc := offset+2*dest,work := c.work+1}
  have hhost : step host c=d := by rw [step_eq_effect host c _ hr.running hc0];rfl
  have hguest : step guest g={g with pc := dest,work := g.work+1} := by rw [step_eq_effect guest g _ hg hc];rfl
  refine ⟨d,hhost,⟨?_,?_,hr.running,hr.fault⟩,rfl,rfl⟩
  · rw [hguest];exact ⟨hr.data.natural,hr.data.real,hr.data.natMem,hr.data.realMem⟩
  · rw [hguest]
    simp only [d,destination,hg,Bool.false_eq_true,if_false]
lemma halt_step (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (c g : Machine) (hr : Rep bound offset returnPC c g) (hg : g.halted=false)
    (hc : guest.code[g.pc]?=some .halt) :
    ∃ d, execute host c 1=d ∧ Rep bound offset returnPC d (step guest g) ∧
      d.work=c.work+1 ∧ d.natReg bound=c.natReg bound := by
  have hp : c.pc=offset+2*g.pc := by simpa only [destination,hg,Bool.false_eq_true,if_false] using hr.position
  have h0 := hcode g.pc .halt hc 0 (by omega)
  have hc0 : host.code[c.pc]?=some (.jump returnPC) := by simpa only [hp,Nat.add_zero,block,List.getElem?_cons_zero] using h0
  let d : Machine := {c with pc := returnPC,work := c.work+1}
  have hhost : step host c=d := by rw [step_eq_effect host c _ hr.running hc0];rfl
  have hguest : step guest g={g with pc := g.pc+1,work := g.work+1,halted := true} := by rw [step_eq_effect guest g _ hg hc];rfl
  refine ⟨d,hhost,⟨?_,?_,hr.running,hr.fault⟩,rfl,rfl⟩
  · rw [hguest];exact ⟨hr.data.natural,hr.data.real,hr.data.natMem,hr.data.realMem⟩
  · rw [hguest]
    simp [d,destination]
end DecrAlmostLinearSSSP.Decremental.Relocation
end s24
section s25
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
lemma less_step (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (c g : Machine) (hr : Rep bound offset returnPC c g) (hg : g.halted=false)
    (a b dest : ℕ) (hc : guest.code[g.pc]?=some (.less a b dest)) (ha : a<bound) (hb : b<bound) :
    ∃ steps d, steps≤2 ∧ execute host c steps=d ∧ Rep bound offset returnPC d (step guest g) ∧
      d.work=c.work+steps ∧ d.natReg bound=c.natReg bound := by
  classical
  have hp : c.pc=offset+2*g.pc := by simpa only [destination,hg,Bool.false_eq_true,if_false] using hr.position
  have h0 := hcode g.pc (.less a b dest) hc 0 (by omega)
  have h1 := hcode g.pc (.less a b dest) hc 1 (by omega)
  have hc0 : host.code[c.pc]?=some (.less a b (offset+2*dest)) := by
    simpa only [hp,Nat.add_zero,block,List.getElem?_cons_zero] using h0
  have hca : c.realReg a=g.realReg a := hr.data.real a ha
  have hcb : c.realReg b=g.realReg b := hr.data.real b hb
  by_cases ht : g.realReg a<g.realReg b
  · have htc : c.realReg a<c.realReg b := by rwa [hca,hcb]
    let d : Machine := {c with pc := offset+2*dest,work := c.work+1}
    have hhost : step host c=d := by rw [step_eq_effect host c _ hr.running hc0];simp only [instructionEffect,if_pos htc];rfl
    have hguest : step guest g={g with pc := dest,work := g.work+1} := by
      rw [step_eq_effect guest g _ hg hc];simp only [instructionEffect,if_pos ht]
    refine ⟨1,d,by omega,hhost,⟨?_,?_,hr.running,hr.fault⟩,rfl,rfl⟩
    · rw [hguest];exact ⟨hr.data.natural,hr.data.real,hr.data.natMem,hr.data.realMem⟩
    · rw [hguest];simp [d,destination,hg]
  · have htc : ¬c.realReg a<c.realReg b := by rwa [hca,hcb]
    let first : Machine := {c with pc := c.pc+1,work := c.work+1}
    let d : Machine := {c with pc := offset+2*(g.pc+1),work := c.work+2}
    have hfirst : step host c=first := by rw [step_eq_effect host c _ hr.running hc0];simp only [instructionEffect,if_neg htc];rfl
    have hc1 : host.code[first.pc]?=some (.jump (offset+2*(g.pc+1))) := by
      change host.code[c.pc+1]?=_
      rw [hp]
      exact h1
    have hsecond : step host first=d := by
      rw [step_eq_effect host first _ hr.running hc1]
      rfl
    have hguest : step guest g={g with pc := g.pc+1,work := g.work+1} := by
      rw [step_eq_effect guest g _ hg hc];simp only [instructionEffect,if_neg ht]
    refine ⟨2,d,by omega,?_,⟨?_,?_,hr.running,hr.fault⟩,rfl,rfl⟩
    · change step host (step host c)=d
      rw [hfirst,hsecond]
    · rw [hguest];exact ⟨hr.data.natural,hr.data.real,hr.data.natMem,hr.data.realMem⟩
    · rw [hguest];simp [d,destination,hg]
lemma lessN_step (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (c g : Machine) (hr : Rep bound offset returnPC c g) (hg : g.halted=false)
    (a b dest : ℕ) (hc : guest.code[g.pc]?=some (.lessN a b dest)) (ha : a<bound) (hb : b<bound) :
    ∃ steps d, steps≤2 ∧ execute host c steps=d ∧ Rep bound offset returnPC d (step guest g) ∧
      d.work=c.work+steps ∧ d.natReg bound=c.natReg bound := by
  classical
  have hp : c.pc=offset+2*g.pc := by simpa only [destination,hg,Bool.false_eq_true,if_false] using hr.position
  have h0 := hcode g.pc (.lessN a b dest) hc 0 (by omega)
  have h1 := hcode g.pc (.lessN a b dest) hc 1 (by omega)
  have hc0 : host.code[c.pc]?=some (.lessN a b (offset+2*dest)) := by
    simpa only [hp,Nat.add_zero,block,List.getElem?_cons_zero] using h0
  have hca : c.natReg a=g.natReg a := hr.data.natural a ha
  have hcb : c.natReg b=g.natReg b := hr.data.natural b hb
  by_cases ht : g.natReg a<g.natReg b
  · have htc : c.natReg a<c.natReg b := by rwa [hca,hcb]
    let d : Machine := {c with pc := offset+2*dest,work := c.work+1}
    have hhost : step host c=d := by rw [step_eq_effect host c _ hr.running hc0];simp only [instructionEffect,if_pos htc];rfl
    have hguest : step guest g={g with pc := dest,work := g.work+1} := by
      rw [step_eq_effect guest g _ hg hc];simp only [instructionEffect,if_pos ht]
    refine ⟨1,d,by omega,hhost,⟨?_,?_,hr.running,hr.fault⟩,rfl,rfl⟩
    · rw [hguest];exact ⟨hr.data.natural,hr.data.real,hr.data.natMem,hr.data.realMem⟩
    · rw [hguest];simp [d,destination,hg]
  · have htc : ¬c.natReg a<c.natReg b := by rwa [hca,hcb]
    let first : Machine := {c with pc := c.pc+1,work := c.work+1}
    let d : Machine := {c with pc := offset+2*(g.pc+1),work := c.work+2}
    have hfirst : step host c=first := by rw [step_eq_effect host c _ hr.running hc0];simp only [instructionEffect,if_neg htc];rfl
    have hc1 : host.code[first.pc]?=some (.jump (offset+2*(g.pc+1))) := by
      change host.code[c.pc+1]?=_
      rw [hp]
      exact h1
    have hsecond : step host first=d := by
      rw [step_eq_effect host first _ hr.running hc1]
      rfl
    have hguest : step guest g={g with pc := g.pc+1,work := g.work+1} := by
      rw [step_eq_effect guest g _ hg hc];simp only [instructionEffect,if_neg ht]
    refine ⟨2,d,by omega,?_,⟨?_,?_,hr.running,hr.fault⟩,rfl,rfl⟩
    · change step host (step host c)=d
      rw [hfirst,hsecond]
    · rw [hguest];exact ⟨hr.data.natural,hr.data.real,hr.data.natMem,hr.data.realMem⟩
    · rw [hguest];simp [d,destination,hg]
end DecrAlmostLinearSSSP.Decremental.Relocation
end s25
section s26
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
lemma single_step (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (c g : Machine) (hr : Rep bound offset returnPC c g) (hg : g.halted=false)
    (ins : Instruction) (hc : guest.code[g.pc]?=some ins) (hb : ∀ j∈instructionRegisters ins, j<bound) :
    ∃ steps d, steps≤2 ∧ execute host c steps=d ∧ Rep bound offset returnPC d (step guest g) ∧
      d.work=c.work+steps ∧ d.natReg bound=c.natReg bound := by
  by_cases hs : Straight ins
  · obtain ⟨d,he,hr,hw,htag⟩ := straight_step host guest bound offset returnPC hcode c g hr hg ins hc hb hs
    exact ⟨2,d,by omega,he,hr,hw,htag⟩
  · cases ins <;> simp only [Straight,not_true_eq_false] at hs
    case jump dest =>
      obtain ⟨d,he,hr,hw,htag⟩ := jump_step host guest bound offset returnPC hcode c g hr hg dest hc
      exact ⟨1,d,by omega,he,hr,hw,htag⟩
    case halt =>
      obtain ⟨d,he,hr,hw,htag⟩ := halt_step host guest bound offset returnPC hcode c g hr hg hc
      exact ⟨1,d,by omega,he,hr,hw,htag⟩
    case less a b dest =>
      exact less_step host guest bound offset returnPC hcode c g hr hg a b dest hc
        (hb a (by simp [instructionRegisters])) (hb b (by simp [instructionRegisters]))
    case lessN a b dest =>
      exact lessN_step host guest bound offset returnPC hcode c g hr hg a b dest hc
        (hb a (by simp [instructionRegisters])) (hb b (by simp [instructionRegisters]))
end DecrAlmostLinearSSSP.Decremental.Relocation
end s26
section s27
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
lemma execution (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (hb : ∀ ins∈guest.code, ∀ j∈instructionRegisters ins, j<bound)
    (fuel : ℕ) (c g : Machine) (hr : Rep bound offset returnPC c g)
    (hv : ∀ j<fuel, (execute guest g j).halted=false → ∃ ins, guest.code[(execute guest g j).pc]?=some ins) :
    ∃ steps d, steps≤2*fuel ∧ execute host c steps=d ∧ Rep bound offset returnPC d (execute guest g fuel) ∧
      d.work=c.work+steps ∧ d.natReg bound=c.natReg bound := by
  induction fuel generalizing c g with
  | zero => exact ⟨0,c,by omega,rfl,hr,rfl,rfl⟩
  | succ fuel ih =>
    by_cases hg : g.halted=true
    · refine ⟨0,c,by omega,rfl,?_,rfl,rfl⟩
      rw [execute_halted guest g hg];exact hr
    · have hgf : g.halted=false := Bool.eq_false_iff.mpr hg
      obtain ⟨ins,hins⟩ := hv 0 (by omega) hgf
      obtain ⟨cp,u,hcp,heu,hu,huw,hutag⟩ := single_step host guest bound offset returnPC hcode c g hr hgf ins hins
        (hb ins (List.mem_of_getElem? hins))
      have hunext : ∀ j<fuel, (execute guest (step guest g) j).halted=false →
          ∃ ins, guest.code[(execute guest (step guest g) j).pc]?=some ins := by
        intro j hj hh
        rw [←execute_succ_front] at hh ⊢
        exact hv (j+1) (by omega) hh
      obtain ⟨cq,d,hcq,hed,hd,hdw,hdtag⟩ := ih u (step guest g) hu hunext
      refine ⟨cp+cq,d,by omega,?_,?_,by omega,hdtag.trans hutag⟩
      · rw [execute_add,heu,hed]
      · rwa [execute_succ_front]
lemma ends_to_return (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (hb : ∀ ins∈guest.code, ∀ j∈instructionRegisters ins, j<bound)
    (c g final : Machine) (hr : Rep bound offset returnPC c g) (hend : Ends guest g final) :
    ∃ steps d, execute host c steps=d ∧ LowData bound d final ∧ d.pc=returnPC ∧
      d.work≤c.work+2*(final.work-g.work) ∧ d.halted=false ∧ d.fault=false ∧ d.natReg bound=c.natReg bound := by
  obtain ⟨fuel,hf,hh,hnof⟩ := hend
  have hhalt : (execute guest g fuel).halted=true := by rwa [hf]
  obtain ⟨r,hrFuel,hrEq,hrWork⟩ := terminating_prefix guest g fuel hhalt
  have hrFinal : execute guest g r=final := hrEq.trans hf
  have hrFault : (execute guest g r).fault=false := by rwa [hrFinal]
  obtain ⟨cost,d,hcost,he,hd,hdw,hdtag⟩ := execution host guest bound offset returnPC hcode hb r c g hr
    (execution_valid_code guest g r hrFault)
  have hdf : Rep bound offset returnPC d final := by rwa [hrFinal] at hd
  refine ⟨cost,d,he,hdf.data,?_,?_,hdf.running,hdf.fault,hdtag⟩
  · simpa only [destination,hh,Bool.true_eq,if_true] using hdf.position
  · rw [hf] at hrWork
    omega
end DecrAlmostLinearSSSP.Decremental.Relocation
end s27
section s28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Relocation
lemma ends (host guest : Program) (bound offset returnPC : ℕ) (hcode : Embeds host guest offset returnPC)
    (hb : ∀ ins∈guest.code, ∀ j∈instructionRegisters ins, j<bound)
    (hreturn : host.code[returnPC]?=some .halt)
    (c g final : Machine) (hr : Rep bound offset returnPC c g) (hend : Ends guest g final) :
    ∃ d, Ends host c d ∧ LowData bound d final ∧ d.work≤c.work+2*(final.work-g.work)+1 ∧
      d.natReg bound=c.natReg bound := by
  obtain ⟨cost,b,he,hdata,hpc,hw,hh,hf,htag⟩ := ends_to_return host guest bound offset returnPC hcode hb c g final hr hend
  let d : Machine := {b with pc := b.pc+1,work := b.work+1,halted := true}
  have hstep : step host b=d := by rw [step_eq_effect host b .halt hh (by rwa [hpc])];rfl
  refine ⟨d,⟨cost+1,?_,rfl,hf⟩,⟨hdata.natural,hdata.real,hdata.natMem,hdata.realMem⟩,by dsimp [d];omega,htag⟩
  rw [execute_add,he]
  exact hstep
lemma LowData.initial (bound : ℕ) (host guest : Program) (i : Input) :
    LowData bound (initialMachine host i) (initialMachine guest i) :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,rfl,rfl⟩
lemma LowData.deletion {bound : ℕ} {c g : Machine} (h : LowData bound c g) (host guest : Program) (e : ℕ) :
    LowData bound (deletionMachine host c e) (deletionMachine guest g e) := by
  have hh := h.natural_update 5 e e rfl
  exact ⟨hh.natural,hh.real,hh.natMem,hh.realMem⟩
lemma LowData.stored {bound : ℕ} {c g : Machine} (h : LowData bound c g) (v : ℕ) : stored c v=stored g v := by
  unfold DecrAlmostLinearSSSP.Decremental.stored
  rw [h.natMem,h.realMem]
lemma initial_ends_work_positive (p : Program) (i : Input) (c : Machine) (he : Ends p (initialMachine p i) c) : 1≤c.work := by
  obtain ⟨fuel,hEq,hh,hf⟩ := he
  cases fuel with
  | zero =>
    have hc : initialMachine p i=c := hEq
    rw [←hc] at hh
    contradiction
  | succ fuel =>
    rw [execute_succ_front] at hEq
    have hw := execute_work_mono p (step p (initialMachine p i)) fuel
    have hstep := step_work p (initialMachine p i) rfl
    rw [hEq] at hw
    simpa only [initialMachine,Nat.zero_add] using hstep.symm.trans_le hw
end DecrAlmostLinearSSSP.Decremental.Relocation
end s28
section s29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
structure Data where
  realReg : ℕ → ℝ
  natReg : ℕ → ℕ
  realMem : ℕ → ℝ
  natMem : ℕ → ℕ
def data (c : Machine) : Data := ⟨c.realReg,c.natReg,c.realMem,c.natMem⟩
def Data.machine (s : Data) : Machine := ⟨0,s.realReg,s.natReg,s.realMem,s.natMem,false,false,0⟩
structure Atom where
  instruction : Instruction
  straight : Straight instruction
noncomputable def Atom.effect (a : Atom) (s : Data) : Data := data (instructionEffect a.instruction s.machine)
inductive Test
  | realLess (a b : ℕ)
  | natLess (a b : ℕ)
noncomputable def Test.holds : Test → Data → Prop
  | .realLess a b,s => s.realReg a < s.realReg b
  | .natLess a b,s => s.natReg a < s.natReg b
def Test.emit : Test → ℕ → Instruction
  | .realLess a b,t => .less a b t
  | .natLess a b,t => .lessN a b t
inductive Cmd
  | skip
  | atom (a : Atom)
  | seq (a b : Cmd)
  | branch (test : Test) (yes no : Cmd)
  | loop (test : Test) (body : Cmd)
inductive Eval : Cmd → Data → ℕ → Data → Prop
  | skip (s : Data) : Eval .skip s 0 s
  | atom (a : Atom) (s : Data) : Eval (.atom a) s 1 (a.effect s)
  | seq {a b : Cmd} {s t u : Data} {ta tb : ℕ} :
      Eval a s ta t → Eval b t tb u → Eval (.seq a b) s (ta+tb) u
  | branchYes {test : Test} {yes no : Cmd} {s t : Data} {cost : ℕ} :
      test.holds s → Eval yes s cost t → Eval (.branch test yes no) s (cost+1) t
  | branchNo {test : Test} {yes no : Cmd} {s t : Data} {cost : ℕ} :
      ¬ test.holds s → Eval no s cost t → Eval (.branch test yes no) s (cost+2) t
  | loopNo {test : Test} {body : Cmd} (s : Data) :
      ¬ test.holds s → Eval (.loop test body) s 2 s
  | loopYes {test : Test} {body : Cmd} {s t u : Data} {first rest : ℕ} :
      test.holds s → Eval body s first t → Eval (.loop test body) t rest u →
      Eval (.loop test body) s (first+rest+2) u
def codeSize : Cmd → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => codeSize a+codeSize b
  | .branch _ yes no => codeSize no+codeSize yes+2
  | .loop _ body => codeSize body+3
def compile : Cmd → ℕ → List Instruction
  | .skip,_ => []
  | .atom a,_ => [a.instruction]
  | .seq a b,start => compile a start ++ compile b (start+codeSize a)
  | .branch test yes no,start =>
      [test.emit (start+codeSize no+2)] ++ (compile no (start+1) ++
      ([.jump (start+codeSize no+codeSize yes+2)] ++ compile yes (start+codeSize no+2)))
  | .loop test body,start =>
      [test.emit (start+2),.jump (start+codeSize body+3)] ++ (compile body (start+2) ++ [.jump start])
lemma compile_length (c : Cmd) (start : ℕ) : (compile c start).length = codeSize c := by
  induction c generalizing start with
  | skip => rfl
  | atom a => rfl
  | seq a b iha ihb => simp only [compile,List.length_append,iha,ihb,codeSize]
  | branch test yes no ihy ihn => simp [compile,ihy,ihn,codeSize] <;> omega
  | loop test body ih => simp [compile,ih,codeSize] <;> omega
lemma atom_step (p : Program) (c : Machine) (a : Atom)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some a.instruction) :
    data (step p c) = a.effect (data c) ∧ (step p c).pc = c.pc+1 ∧
      (step p c).halted = false ∧ (step p c).work = c.work+1 := by
  refine ⟨?_,step_straight p c a.instruction hh hc a.straight⟩
  rw [step_eq_effect p c a.instruction hh hc]
  have ha := a.straight
  cases a with
  | mk ins hstraight =>
    cases ins <;> simp only [Straight] at hstraight
    all_goals try contradiction
    all_goals rfl
lemma test_step (p : Program) (c : Machine) (test : Test) (target : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some (test.emit target)) :
    data (step p c) = data c ∧
      (step p c).pc = (if test.holds (data c) then target else c.pc+1) ∧
      (step p c).halted = false ∧ (step p c).work = c.work+1 := by
  classical
  cases test with
  | realLess a b =>
    by_cases h : c.realReg a < c.realReg b
    all_goals simp [step,hh,hc,Test.holds,Test.emit,data,h]
  | natLess a b =>
    by_cases h : c.natReg a < c.natReg b
    all_goals simp [step,hh,hc,Test.holds,Test.emit,data,h]
end DecrAlmostLinearSSSP.Decremental.Structured
end s29
section s30
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def CodeAt (p : Program) (start : ℕ) (code : List Instruction) : Prop :=
  ∀ j < code.length,p.code[start+j]? = code[j]?
lemma CodeAt.left {p : Program} {start : ℕ} {a b : List Instruction}
    (h : CodeAt p start (a++b)) : CodeAt p start a := by
  intro j hj
  rw [h j (by simp only [List.length_append];omega),List.getElem?_append_left hj]
lemma CodeAt.right {p : Program} {start : ℕ} {a b : List Instruction}
    (h : CodeAt p start (a++b)) : CodeAt p (start+a.length) b := by
  intro j hj
  have hh := h (a.length+j) (by simp only [List.length_append];omega)
  rw [List.getElem?_append_right (by omega)] at hh
  simpa only [Nat.add_sub_cancel_left,Nat.add_assoc] using hh
lemma CodeAt.head {p : Program} {start : ℕ} {ins : Instruction} {rest : List Instruction}
    (h : CodeAt p start (ins::rest)) : p.code[start]? = some ins := by
  simpa only [Nat.add_zero,List.getElem?_cons_zero] using h 0 (by simp)
lemma CodeAt.tail {p : Program} {start : ℕ} {ins : Instruction} {rest : List Instruction}
    (h : CodeAt p start (ins::rest)) : CodeAt p (start+1) rest := by
  intro j hj
  have hh := h (j+1) (by simp only [List.length_cons];omega)
  simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
lemma CodeAt.of_assembled (codePrefix code suffix : List Instruction) (p : Program)
    (hc : p.code = codePrefix++(code++suffix)) : CodeAt p codePrefix.length code := by
  intro j hj
  rw [hc,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj]
end DecrAlmostLinearSSSP.Decremental.Structured
end s30
section s31
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma compile_seq_parts (p : Program) (start : ℕ) (a b : Cmd)
    (h : CodeAt p start (compile (.seq a b) start)) :
    CodeAt p start (compile a start) ∧ CodeAt p (start+codeSize a) (compile b (start+codeSize a)) := by
  exact ⟨CodeAt.left h,by simpa only [compile_length] using CodeAt.right h⟩
lemma compile_branch_parts (p : Program) (start : ℕ) (test : Test) (yes no : Cmd)
    (h : CodeAt p start (compile (.branch test yes no) start)) :
    p.code[start]? = some (test.emit (start+codeSize no+2)) ∧
      CodeAt p (start+1) (compile no (start+1)) ∧
      p.code[start+1+codeSize no]? = some (.jump (start+codeSize no+codeSize yes+2)) ∧
      CodeAt p (start+codeSize no+2) (compile yes (start+codeSize no+2)) := by
  change CodeAt p start (test.emit (start+codeSize no+2) ::
    (compile no (start+1) ++ (.jump (start+codeSize no+codeSize yes+2) :: compile yes (start+codeSize no+2)))) at h
  have ht := CodeAt.tail h
  have hr := CodeAt.right ht
  refine ⟨CodeAt.head h,CodeAt.left ht,?_,?_⟩
  · simpa only [compile_length] using CodeAt.head hr
  · simpa only [compile_length, show start+1+codeSize no+1 = start+codeSize no+2 by omega] using CodeAt.tail hr
lemma compile_loop_parts (p : Program) (start : ℕ) (test : Test) (body : Cmd)
    (h : CodeAt p start (compile (.loop test body) start)) :
    p.code[start]? = some (test.emit (start+2)) ∧
      p.code[start+1]? = some (.jump (start+codeSize body+3)) ∧
      CodeAt p (start+2) (compile body (start+2)) ∧
      p.code[start+2+codeSize body]? = some (.jump start) := by
  change CodeAt p start (test.emit (start+2) :: .jump (start+codeSize body+3) ::
    (compile body (start+2) ++ [.jump start])) at h
  have ht := CodeAt.tail h
  have hb := CodeAt.tail ht
  refine ⟨CodeAt.head h,CodeAt.head ht,CodeAt.left hb,?_⟩
  simpa only [compile_length] using CodeAt.head (CodeAt.right hb)
lemma data_clock (c : Machine) (pc work : ℕ) : data {c with pc := pc,work := work} = data c := rfl
lemma jump_step (p : Program) (c : Machine) (target : ℕ) (hh : c.halted = false)
    (hc : p.code[c.pc]? = some (.jump target)) :
    data (execute p c 1) = data c ∧ (execute p c 1).pc = target ∧
      (execute p c 1).halted = false ∧ (execute p c 1).work = c.work+1 := by
  rw [host_jump p c target hh hc]
  exact ⟨rfl,rfl,hh,rfl⟩
end DecrAlmostLinearSSSP.Decremental.Structured
end s31
section s32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma eval_compiles {cmd : Cmd} {s t : Data} {cost : ℕ} (he : Eval cmd s cost t) :
    ∀ (p : Program) (start : ℕ) (c : Machine), CodeAt p start (compile cmd start) →
      c.pc = start → data c = s → c.halted = false →
      data (execute p c cost) = t ∧ (execute p c cost).pc = start+codeSize cmd ∧
        (execute p c cost).halted = false ∧ (execute p c cost).work = c.work+cost := by
  classical
  induction he with
  | skip s =>
    intro p start c hcode hpc hdata hhalt
    exact ⟨hdata,by change c.pc = start;exact hpc,hhalt,rfl⟩
  | atom a s =>
    intro p start c hcode hpc hdata hhalt
    have hfetch : p.code[c.pc]? = some a.instruction := by rw [hpc];exact CodeAt.head hcode
    obtain ⟨hd,hp,hh,hw⟩ := atom_step p c a hhalt hfetch
    rw [hdata] at hd
    rw [hpc] at hp
    exact ⟨hd,hp,hh,hw⟩
  | @seq a b s t u ta tb ha hb iha ihb =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hca,hcb⟩ := compile_seq_parts p start a b hcode
    obtain ⟨hda,hpa,hha,hwa⟩ := iha p start c hca hpc hdata hhalt
    obtain ⟨hdb,hpb,hhb,hwb⟩ := ihb p (start+codeSize a) (execute p c ta) hcb hpa hda hha
    rw [execute_add]
    refine ⟨hdb,?_,hhb,?_⟩
    · simpa only [codeSize,Nat.add_assoc] using hpb
    · rw [hwb,hwa,Nat.add_assoc]
  | @branchYes test yes no s t amount hcond he ih =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcno,hcjump,hcyes⟩ := compile_branch_parts p start test yes no hcode
    have hc : p.code[c.pc]? = some (test.emit (start+codeSize no+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : test.holds (data c) := by rwa [hdata]
    rw [if_pos htake] at hp1
    let c1 := step p c
    obtain ⟨hd2,hp2,hh2,hw2⟩ := ih p (start+codeSize no+2) c1 hcyes hp1 (hd1.trans hdata) hh1
    rw [show amount+1 = 1+amount by omega,execute_add]
    change data (execute p c1 amount) = _ ∧ (execute p c1 amount).pc = _ ∧
      (execute p c1 amount).halted = _ ∧ (execute p c1 amount).work = _
    refine ⟨hd2,?_,hh2,?_⟩
    · simp only [codeSize] at *
      omega
    · rw [hw2]
      change (step p c).work+amount = _
      rw [hw1]
      omega
  | @branchNo test yes no s t amount hcond he ih =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcno,hcjump,hcyes⟩ := compile_branch_parts p start test yes no hcode
    have hc : p.code[c.pc]? = some (test.emit (start+codeSize no+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : ¬test.holds (data c) := by rwa [hdata]
    rw [if_neg htake,hpc] at hp1
    let c1 := step p c
    obtain ⟨hd2,hp2,hh2,hw2⟩ := ih p (start+1) c1 hcno hp1 (hd1.trans hdata) hh1
    let c2 := execute p c1 amount
    have hc2 : p.code[c2.pc]? = some (.jump (start+codeSize no+codeSize yes+2)) := by rw [hp2];exact hcjump
    obtain ⟨hd3,hp3,hh3,hw3⟩ := jump_step p c2 _ hh2 hc2
    rw [show amount+2 = 1+(amount+1) by omega,execute_add,execute_add]
    change data (execute p c2 1) = _ ∧ (execute p c2 1).pc = _ ∧
      (execute p c2 1).halted = _ ∧ (execute p c2 1).work = _
    refine ⟨hd3.trans hd2,?_,hh3,?_⟩
    · simpa only [codeSize,Nat.add_assoc] using hp3
    · rw [hw3,hw2]
      change (step p c).work+amount+1 = _
      rw [hw1]
      omega
  | @loopNo test body s hcond =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcjump,hcbody,hcback⟩ := compile_loop_parts p start test body hcode
    have hc : p.code[c.pc]? = some (test.emit (start+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : ¬test.holds (data c) := by rwa [hdata]
    rw [if_neg htake,hpc] at hp1
    let c1 := step p c
    have hc1 : p.code[c1.pc]? = some (.jump (start+codeSize body+3)) := by rw [hp1];exact hcjump
    obtain ⟨hd2,hp2,hh2,hw2⟩ := jump_step p c1 _ hh1 hc1
    rw [show 2 = 1+1 by omega,execute_add]
    change data (execute p c1 1) = _ ∧ (execute p c1 1).pc = _ ∧
      (execute p c1 1).halted = _ ∧ (execute p c1 1).work = _
    refine ⟨hd2.trans (hd1.trans hdata),?_,hh2,?_⟩
    · simpa only [codeSize,Nat.add_assoc] using hp2
    · rw [hw2]
      change (step p c).work+1 = _
      rw [hw1]
  | @loopYes test body s t u first rest hcond he hloop ihbody ihloop =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcjump,hcbody,hcback⟩ := compile_loop_parts p start test body hcode
    have hc : p.code[c.pc]? = some (test.emit (start+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : test.holds (data c) := by rwa [hdata]
    rw [if_pos htake] at hp1
    let c1 := step p c
    obtain ⟨hd2,hp2,hh2,hw2⟩ := ihbody p (start+2) c1 hcbody hp1 (hd1.trans hdata) hh1
    let c2 := execute p c1 first
    have hc2 : p.code[c2.pc]? = some (.jump start) := by rw [hp2];exact hcback
    obtain ⟨hd3,hp3,hh3,hw3⟩ := jump_step p c2 start hh2 hc2
    let c3 := execute p c2 1
    obtain ⟨hd4,hp4,hh4,hw4⟩ := ihloop p start c3 hcode hp3 (hd3.trans hd2) hh3
    rw [show first+rest+2 = 1+(first+(1+rest)) by omega,execute_add,execute_add,execute_add]
    change data (execute p c3 rest) = _ ∧ (execute p c3 rest).pc = _ ∧
      (execute p c3 rest).halted = _ ∧ (execute p c3 rest).work = _
    refine ⟨hd4,hp4,hh4,?_⟩
    rw [hw4,hw3,hw2]
    change (step p c).work+first+1+rest = _
    rw [hw1]
    omega
end DecrAlmostLinearSSSP.Decremental.Structured
end s32
section s33
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
def FaultWellFormed (c : Machine) : Prop := c.fault = false ∨ c.halted = true
lemma fault_well_formed_step (p : Program) (c : Machine) (hc : FaultWellFormed c) :
    FaultWellFormed (step p c) := by
  classical
  by_cases hh : c.halted = true
  · rw [step_of_halted p c hh]
    exact Or.inr hh
  · have hhalt : c.halted = false := Bool.eq_false_iff.mpr hh
    have hfault : c.fault = false := hc.resolve_right hh
    unfold step
    rw [hhalt]
    simp only [Bool.false_eq_true,if_false]
    cases hcode : p.code[c.pc]? with
    | none => exact Or.inr rfl
    | some ins =>
      cases ins <;> simp only [FaultWellFormed]
      all_goals try exact Or.inl hfault
      all_goals split_ifs <;> exact Or.inl hfault
lemma fault_well_formed_execute (p : Program) (c : Machine) (t : ℕ) (hc : FaultWellFormed c) :
    FaultWellFormed (execute p c t) := by
  induction t with
  | zero => exact hc
  | succ t ih =>
    rw [execute_add]
    exact fault_well_formed_step p _ ih
lemma running_execution_no_fault (p : Program) (c : Machine) (t : ℕ)
    (hc : c.fault = false) (hh : (execute p c t).halted = false) :
    (execute p c t).fault = false := by
  have hi := fault_well_formed_execute p c t (Or.inl hc)
  exact hi.resolve_right (by rw [hh]; decide)
end DecrAlmostLinearSSSP.Decremental
end s33
section s34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
def program (init update : Cmd) : Program where
  code := compile init 0 ++ (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt]))
  initPC := 0
  update := codeSize init+1
  query := codeSize init+codeSize update+2
lemma program_init (init update : Cmd) : CodeAt (program init update) 0 (compile init 0) := by
  have h := CodeAt.of_assembled [] (compile init 0) (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt]))
    (program init update) rfl
  exact h
lemma program_init_halt (init update : Cmd) : (program init update).code[codeSize init]? = some .halt := by
  change (compile init 0 ++ (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt])))[codeSize init]? = _
  rw [List.getElem?_append_right (by rw [compile_length]),compile_length,Nat.sub_self]
  rfl
lemma program_update (init update : Cmd) :
    CodeAt (program init update) (codeSize init+1) (compile update (codeSize init+1)) := by
  have h := CodeAt.of_assembled (compile init 0 ++ [.halt]) (compile update (codeSize init+1))
    [.halt,.loadN 6 5,.load 1 5,.halt] (program init update) (by simp [program,List.append_assoc])
  simpa only [List.length_append,compile_length,List.length_singleton] using h
lemma program_update_halt (init update : Cmd) :
    (program init update).code[codeSize init+1+codeSize update]? = some .halt := by
  change (compile init 0 ++ (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt])))[_]? = _
  rw [List.getElem?_append_right (by rw [compile_length];omega),compile_length]
  have hi : codeSize init+1+codeSize update-codeSize init = codeSize update+1 := by omega
  rw [hi,List.getElem?_cons_succ,List.getElem?_append_right (by rw [compile_length]),compile_length,Nat.sub_self]
  rfl
lemma program_query_code (init update : Cmd) :
    CodeAt (program init update) (program init update).query [.loadN 6 5,.load 1 5,.halt] := by
  let codePrefix := compile init 0 ++ [.halt] ++ compile update (codeSize init+1) ++ [.halt]
  have h := CodeAt.of_assembled codePrefix [.loadN 6 5,.load 1 5,.halt] [] (program init update)
    (by simp [codePrefix,program,List.append_assoc])
  have hlen : codePrefix.length = (program init update).query := by
    change codePrefix.length = codeSize init+codeSize update+2
    simp only [codePrefix,List.length_append,List.length_singleton,compile_length]
    omega
  rwa [hlen] at h
lemma program_query_nine (init update : Cmd) (c : Machine) (v : ℕ) :
    ∃ d,Ends (program init update) {resume c (program init update).query with natReg := Function.update c.natReg 5 v} d ∧
      d.work+6 ≤ c.work+9 ∧ d.natReg 6 = c.natMem v ∧ d.realReg 1 = c.realMem v ∧
      d.realMem = c.realMem ∧ d.natMem = c.natMem := by
  have h := program_query_code init update
  exact ram_query_nine (program init update) (CodeAt.head h) (CodeAt.head (CodeAt.tail h))
    (CodeAt.head (CodeAt.tail (CodeAt.tail h))) c v
lemma command_ends {cmd : Cmd} {s t : Data} {cost : ℕ} (he : Eval cmd s cost t)
    (p : Program) (start : ℕ) (c : Machine)
    (hcode : CodeAt p start (compile cmd start)) (hpc : c.pc = start) (hdata : data c = s)
    (hhalt : c.halted = false) (hfault : c.fault = false)
    (hend : p.code[start+codeSize cmd]? = some .halt) :
    ∃ d,Ends p c d ∧ data d = t ∧ d.work = c.work+cost+1 := by
  obtain ⟨hd,hp,hh,hw⟩ := eval_compiles he p start c hcode hpc hdata hhalt
  let b := execute p c cost
  have hbf : b.fault = false := running_execution_no_fault p c cost hfault hh
  let d : Machine := {b with pc := b.pc+1,work := b.work+1,halted := true}
  have hc : p.code[b.pc]? = some .halt := by rw [hp];exact hend
  have hs : step p b = d := by simp [step,d,show b.halted = false from hh,hc]
  refine ⟨d,⟨cost+1,?_,rfl,hbf⟩,hd,?_⟩
  · rw [execute_add]
    exact hs
  · change b.work+1 = c.work+cost+1
    rw [hw]
end DecrAlmostLinearSSSP.Decremental.Structured
end s34
section s35
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
structure Branches where
  singleton : Program
  small : Program
  normal : Program
def fresh (b : Branches) : ℕ := 8+registerBound b.singleton.code+registerBound b.small.code+registerBound b.normal.code
def singletonOffset (_ : Branches) : ℕ := 19
def exactOffset (b : Branches) : ℕ := 19+2*b.singleton.code.length
def normalOffset (b : Branches) : ℕ := exactOffset b+2*b.small.code.length
def returnPC (b : Branches) : ℕ := normalOffset b+2*b.normal.code.length
def dispatchPrefix (b : Branches) : List Instruction := [
  .natural (fresh b+1) 2,
  .lessN 0 (fresh b+1) 10,
  .cast (fresh b) 2,
  .mul (fresh b) (fresh b) 0,
  .rational (fresh b+1) 1,
  .less (fresh b+1) (fresh b) 8,
  .natural (fresh b) 1,
  .jump (exactOffset b+2*b.small.initPC),
  .natural (fresh b) 2,
  .jump (normalOffset b+2*b.normal.initPC),
  .natural (fresh b) 0,
  .jump (singletonOffset b+2*b.singleton.initPC),
  .natural (fresh b+1) 1,
  .lessN (fresh b) (fresh b+1) 18,
  .natural (fresh b+1) 2,
  .lessN (fresh b) (fresh b+1) 17,
  .jump (normalOffset b+2*b.normal.update),
  .jump (exactOffset b+2*b.small.update),
  .jump (singletonOffset b+2*b.singleton.update)]
def singletonCode (b : Branches) : List Instruction := Relocation.code (singletonOffset b) (returnPC b) b.singleton.code
def exactCode (b : Branches) : List Instruction := Relocation.code (exactOffset b) (returnPC b) b.small.code
def normalCode (b : Branches) : List Instruction := Relocation.code (normalOffset b) (returnPC b) b.normal.code
def program (b : Branches) : Program where
  code := dispatchPrefix b++singletonCode b++exactCode b++normalCode b++[.halt,.loadN 6 5,.load 1 5,.halt]
  initPC := 0
  update := 12
  query := returnPC b+1
lemma prefix_length (b : Branches) : (dispatchPrefix b).length=19 := rfl
lemma fresh_ge (b : Branches) : 8≤fresh b := by unfold fresh;omega
lemma singleton_bound (b : Branches) : registerBound b.singleton.code≤fresh b := by unfold fresh;omega
lemma exact_bound (b : Branches) : registerBound b.small.code≤fresh b := by unfold fresh;omega
lemma normal_bound (b : Branches) : registerBound b.normal.code≤fresh b := by unfold fresh;omega
lemma singleton_operands (b : Branches) : ∀ ins∈b.singleton.code, ∀ j∈instructionRegisters ins, j<fresh b :=
  fun ins hi j hj => (register_operand_bound _ ins hi j hj).trans_le (singleton_bound b)
lemma exact_operands (b : Branches) : ∀ ins∈b.small.code, ∀ j∈instructionRegisters ins, j<fresh b :=
  fun ins hi j hj => (register_operand_bound _ ins hi j hj).trans_le (exact_bound b)
lemma normal_operands (b : Branches) : ∀ ins∈b.normal.code, ∀ j∈instructionRegisters ins, j<fresh b :=
  fun ins hi j hj => (register_operand_bound _ ins hi j hj).trans_le (normal_bound b)
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s35
section s36
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
open Structured
lemma embeds_of_codeAt (host guest : Program) (offset returnPC : ℕ)
    (hcode : CodeAt host offset (Relocation.code offset returnPC guest.code)) : Relocation.Embeds host guest offset returnPC := by
  intro pc ins hc slot hs
  have hpc : pc<guest.code.length := by
    by_contra hn
    have hnone : guest.code[pc]?=none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hnone] at hc;contradiction
  have hi : 2*pc+slot<(Relocation.code offset returnPC guest.code).length := by rw [Relocation.code_length];omega
  have hh := hcode (2*pc+slot) hi
  rw [Relocation.code_lookup offset returnPC guest.code pc ins hc slot hs] at hh
  simpa only [Nat.add_assoc] using hh
lemma singleton_codeAt (b : Branches) : CodeAt (program b) (singletonOffset b) (singletonCode b) := by
  have h := CodeAt.of_assembled (dispatchPrefix b) (singletonCode b)
    (exactCode b++normalCode b++[.halt,.loadN 6 5,.load 1 5,.halt]) (program b) (by simp [program,List.append_assoc])
  simpa only [prefix_length,singletonOffset] using h
lemma exact_codeAt (b : Branches) : CodeAt (program b) (exactOffset b) (exactCode b) := by
  have h := CodeAt.of_assembled (dispatchPrefix b++singletonCode b) (exactCode b)
    (normalCode b++[.halt,.loadN 6 5,.load 1 5,.halt]) (program b) (by simp [program,List.append_assoc])
  simpa only [List.length_append,prefix_length,singletonCode,Relocation.code_length,exactOffset] using h
lemma normal_codeAt (b : Branches) : CodeAt (program b) (normalOffset b) (normalCode b) := by
  have h := CodeAt.of_assembled (dispatchPrefix b++singletonCode b++exactCode b) (normalCode b)
    [.halt,.loadN 6 5,.load 1 5,.halt] (program b) (by simp [program,List.append_assoc])
  simpa only [List.length_append,prefix_length,singletonCode,exactCode,Relocation.code_length,normalOffset,exactOffset] using h
lemma singleton_embeds (b : Branches) : Relocation.Embeds (program b) b.singleton (singletonOffset b) (returnPC b) := embeds_of_codeAt _ _ _ _ (singleton_codeAt b)
lemma exact_embeds (b : Branches) : Relocation.Embeds (program b) b.small (exactOffset b) (returnPC b) := embeds_of_codeAt _ _ _ _ (exact_codeAt b)
lemma normal_embeds (b : Branches) : Relocation.Embeds (program b) b.normal (normalOffset b) (returnPC b) := embeds_of_codeAt _ _ _ _ (normal_codeAt b)
lemma suffix_codeAt (b : Branches) : CodeAt (program b) (returnPC b) [.halt,.loadN 6 5,.load 1 5,.halt] := by
  have h := CodeAt.of_assembled (dispatchPrefix b++singletonCode b++exactCode b++normalCode b)
    [.halt,.loadN 6 5,.load 1 5,.halt] [] (program b) (by simp [program,List.append_assoc])
  simpa only [List.length_append,prefix_length,singletonCode,exactCode,normalCode,Relocation.code_length,
    returnPC,normalOffset,exactOffset] using h
lemma return_halt (b : Branches) : (program b).code[returnPC b]?=some .halt := CodeAt.head (suffix_codeAt b)
lemma prefix_lookup (b : Branches) (j : ℕ) (hj : j<19) : (program b).code[j]?=(dispatchPrefix b)[j]? := by
  have h := CodeAt.of_assembled [] (dispatchPrefix b)
    (singletonCode b++exactCode b++normalCode b++[.halt,.loadN 6 5,.load 1 5,.halt]) (program b) (by simp [program,List.append_assoc])
  simpa only [List.length_nil,Nat.zero_add] using h j (by rwa [prefix_length])
lemma query_nine (b : Branches) (c : Machine) (v : ℕ) :
    ∃ d, Ends (program b) {resume c (program b).query with natReg := Function.update c.natReg 5 v} d ∧
      d.work+6≤c.work+9 ∧ d.natReg 6=c.natMem v ∧ d.realReg 1=c.realMem v ∧ d.realMem=c.realMem ∧ d.natMem=c.natMem := by
  have h := CodeAt.tail (suffix_codeAt b)
  exact ram_query_nine (program b) (CodeAt.head h) (CodeAt.head (CodeAt.tail h)) (CodeAt.head (CodeAt.tail (CodeAt.tail h))) c v
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s36
section s37
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
inductive Kind where
  | singleton
  | small
  | normal
  deriving DecidableEq
def Kind.tag : Kind → ℕ | .singleton => 0 | .small => 1 | .normal => 2
def source (b : Branches) : Kind → Program | .singleton => b.singleton | .small => b.small | .normal => b.normal
def offset (b : Branches) : Kind → ℕ | .singleton => singletonOffset b | .small => exactOffset b | .normal => normalOffset b
noncomputable def choose (i : Input) : Kind :=
  if i.n<2 then .singleton else if (1 : ℝ)<(i.size : ℝ)*i.accuracy then .normal else .small
lemma source_embeds (b : Branches) (k : Kind) : Relocation.Embeds (program b) (source b k) (offset b k) (returnPC b) := by
  cases k
  · exact singleton_embeds b
  · exact exact_embeds b
  · exact normal_embeds b
lemma source_operands (b : Branches) (k : Kind) : ∀ ins∈(source b k).code, ∀ j∈instructionRegisters ins, j<fresh b := by
  cases k
  · exact singleton_operands b
  · exact exact_operands b
  · exact normal_operands b
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s37
section s38
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma init_singleton (b : Branches) (i : Input) (hn : i.n<2) :
    ∃ c, execute (program b) (initialMachine (program b) i) 4=c ∧
      Relocation.Rep (fresh b) (singletonOffset b) (returnPC b) c (initialMachine b.singleton i) ∧
      c.work=4 ∧ c.natReg (fresh b)=0 := by
  classical
  let p := program b
  let c0 := initialMachine p i
  let c1 : Machine := {c0 with pc := 1,work := 1,natReg := Function.update c0.natReg (fresh b+1) 2}
  let c2 : Machine := {c1 with pc := 10,work := 2}
  let c3 : Machine := {c2 with pc := 11,work := 3,natReg := Function.update c2.natReg (fresh b) 0}
  let c4 : Machine := {c3 with pc := singletonOffset b+2*b.singleton.initPC,work := 4}
  have h0 : p.code[0]?=some (.natural (fresh b+1) 2) := by simpa [dispatchPrefix,p] using prefix_lookup b 0 (by omega)
  have h1 : p.code[1]?=some (.lessN 0 (fresh b+1) 10) := by simpa [dispatchPrefix,p] using prefix_lookup b 1 (by omega)
  have h10 : p.code[10]?=some (.natural (fresh b) 0) := by simpa [dispatchPrefix,p] using prefix_lookup b 10 (by omega)
  have h11 : p.code[11]?=some (.jump (singletonOffset b+2*b.singleton.initPC)) := by simpa [dispatchPrefix,p] using prefix_lookup b 11 (by omega)
  have hR := fresh_ge b
  have hs0 : step p c0=c1 := by
    rw [step_eq_effect p c0 (.natural (fresh b+1) 2) rfl h0]
    rfl
  have hs1 : step p c1=c2 := by
    have hr0 : (fresh b+1 : ℕ)≠0 := by omega
    simp [step,c0,c1,c2,initialMachine,h1,Function.update_of_ne (Ne.symm hr0),hn]
  have hs2 : step p c2=c3 := by simp [step,c0,c1,c2,c3,initialMachine,h10]
  have hs3 : step p c3=c4 := by simp [step,c0,c1,c2,c3,c4,initialMachine,h11]
  refine ⟨c4,?_,⟨?_,?_,rfl,rfl⟩,rfl,?_⟩
  · change step p (step p (step p (step p c0)))=c4
    rw [hs0,hs1,hs2,hs3]
  · refine ⟨?_,?_,rfl,rfl⟩
    · intro j hj
      have hj0 : j≠fresh b := by omega
      have hj1 : j≠fresh b+1 := by omega
      simp only [c4,c3,c2,c1,c0,initialMachine,Function.update_of_ne hj0,Function.update_of_ne hj1]
    · intro j hj;rfl
  · simp [c4,c3,Relocation.destination,initialMachine]
  · simp [c4,c3]
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s38
section s39
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma init_large_prefix (b : Branches) (i : Input) (hn : 2 ≤ i.n) :
    ∃ c, execute (program b) (initialMachine (program b) i) 6=c ∧
      Relocation.LowData (fresh b) c (initialMachine (program b) i) ∧
      c.pc=(if (1 : ℝ)<(i.size : ℝ)*i.accuracy then 8 else 6) ∧ c.work=6 ∧ c.halted=false ∧ c.fault=false := by
  classical
  let p := program b
  let c0 := initialMachine p i
  let c1 : Machine := {c0 with pc := 1,work := 1,natReg := Function.update c0.natReg (fresh b+1) 2}
  let c2 : Machine := {c1 with pc := 2,work := 2}
  let c3 : Machine := {c2 with pc := 3,work := 3,realReg := Function.update c2.realReg (fresh b) (i.size : ℝ)}
  let c4 : Machine := {c3 with pc := 4,work := 4,realReg := Function.update c3.realReg (fresh b) ((i.size : ℝ)*i.accuracy)}
  let c5 : Machine := {c4 with pc := 5,work := 5,realReg := Function.update c4.realReg (fresh b+1) 1}
  let c6 : Machine := {c5 with pc := (if (1 : ℝ)<(i.size : ℝ)*i.accuracy then 8 else 6),work := 6}
  have hR := fresh_ge b
  have hR0 : fresh b≠0 := by omega
  have hR1 : fresh b+1≠0 := by omega
  have hR2 : fresh b+1≠2 := by omega
  have hRne : fresh b≠fresh b+1 := by omega
  have hcode (j : ℕ) (hj : j<19) : p.code[j]?=(dispatchPrefix b)[j]? := prefix_lookup b j hj
  have hs0 : step p c0=c1 := by
    have hh : p.code[0]?=some (.natural (fresh b+1) 2) := by simpa [dispatchPrefix] using hcode 0 (by omega)
    rw [step_eq_effect p c0 (.natural (fresh b+1) 2) rfl hh]
    rfl
  have hs1 : step p c1=c2 := by
    have hh : p.code[1]?=some (.lessN 0 (fresh b+1) 10) := by simpa [dispatchPrefix] using hcode 1 (by omega)
    simp [step,c0,c1,c2,initialMachine,hh,Function.update_of_ne (Ne.symm hR1),show ¬i.n<2 by omega]
  have hs2 : step p c2=c3 := by
    have hh : p.code[2]?=some (.cast (fresh b) 2) := by simpa [dispatchPrefix] using hcode 2 (by omega)
    simp [step,c0,c1,c2,c3,initialMachine,hh,Function.update_of_ne (Ne.symm hR2)]
  have hs3 : step p c3=c4 := by
    have hh : p.code[3]?=some (.mul (fresh b) (fresh b) 0) := by simpa [dispatchPrefix] using hcode 3 (by omega)
    simp [step,c0,c1,c2,c3,c4,initialMachine,hh,Function.update_of_ne (Ne.symm hR0)]
  have hs4 : step p c4=c5 := by
    have hh : p.code[4]?=some (.rational (fresh b+1) 1) := by simpa [dispatchPrefix] using hcode 4 (by omega)
    simp [step,c0,c1,c2,c3,c4,c5,initialMachine,hh]
  have hs5 : step p c5=c6 := by
    have hh : p.code[5]?=some (.less (fresh b+1) (fresh b) 8) := by simpa [dispatchPrefix] using hcode 5 (by omega)
    simp only [step,c6,c5,c4,c3,c2,c1,c0,initialMachine,Bool.false_eq_true,if_false,hh,Function.update_self,
      Function.update_of_ne hRne]
    split_ifs <;> rfl
  refine ⟨c6,?_,⟨?_,?_,rfl,rfl⟩,rfl,rfl,rfl,rfl⟩
  · change step p (step p (step p (step p (step p (step p c0)))))=c6
    rw [hs0,hs1,hs2,hs3,hs4,hs5]
  · intro j hj
    simp only [c6,c5,c4,c3,c2,c1,c0,initialMachine,Function.update_of_ne (show j≠fresh b+1 by omega)]
  · intro j hj
    simp only [c6,c5,c4,c3,c2,c1,c0,initialMachine,Function.update_of_ne (show j≠fresh b+1 by omega),Function.update_of_ne (show j≠fresh b by omega)]
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s39
section s40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
def initTagPC : Kind → ℕ | .singleton => 10 | .small => 6 | .normal => 8
lemma init_tag_lookup (b : Branches) (k : Kind) : (program b).code[initTagPC k]?=some (.natural (fresh b) k.tag) := by
  cases k
  · simpa [dispatchPrefix,initTagPC,Kind.tag] using prefix_lookup b 10 (by omega)
  · simpa [dispatchPrefix,initTagPC,Kind.tag] using prefix_lookup b 6 (by omega)
  · simpa [dispatchPrefix,initTagPC,Kind.tag] using prefix_lookup b 8 (by omega)
lemma init_jump_lookup (b : Branches) (k : Kind) :
    (program b).code[initTagPC k+1]?=some (.jump (offset b k+2*(source b k).initPC)) := by
  cases k
  · simpa [dispatchPrefix,initTagPC,offset,source] using prefix_lookup b 11 (by omega)
  · simpa [dispatchPrefix,initTagPC,offset,source] using prefix_lookup b 7 (by omega)
  · simpa [dispatchPrefix,initTagPC,offset,source] using prefix_lookup b 9 (by omega)
lemma init_tail (b : Branches) (i : Input) (k : Kind) (c : Machine) (hpc : c.pc=initTagPC k)
    (hh : c.halted=false) (hf : c.fault=false)
    (hd : Relocation.LowData (fresh b) c (initialMachine (source b k) i)) :
    ∃ d, execute (program b) c 2=d ∧ Relocation.Rep (fresh b) (offset b k) (returnPC b) d (initialMachine (source b k) i) ∧
      d.work=c.work+2 ∧ d.natReg (fresh b)=k.tag := by
  let u : Machine := {c with pc := c.pc+1,work := c.work+1,natReg := Function.update c.natReg (fresh b) k.tag}
  let d : Machine := {u with pc := offset b k+2*(source b k).initPC,work := c.work+2}
  have hs0 : step (program b) c=u := by
    rw [step_eq_effect (program b) c (.natural (fresh b) k.tag) hh (by rw [hpc];exact init_tag_lookup b k)]
    rfl
  have hs1 : step (program b) u=d := by
    rw [step_eq_effect (program b) u (.jump (offset b k+2*(source b k).initPC)) hh (by
      change (program b).code[c.pc+1]?=_
      rw [hpc];exact init_jump_lookup b k)]
    rfl
  refine ⟨d,?_,⟨?_,?_,hh,hf⟩,rfl,by simp [d,u]⟩
  · change step (program b) (step (program b) c)=d
    rw [hs0,hs1]
  · refine ⟨?_,hd.real,hd.natMem,hd.realMem⟩
    intro j hj
    change Function.update c.natReg (fresh b) k.tag j=_
    rw [Function.update_of_ne (by omega)]
    exact hd.natural j hj
  · simp [d,Relocation.destination,initialMachine]
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s40
section s41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma initialize_dispatch (b : Branches) (i : Input) :
    ∃ steps c, steps≤8 ∧ execute (program b) (initialMachine (program b) i) steps=c ∧
      Relocation.Rep (fresh b) (offset b (choose i)) (returnPC b) c (initialMachine (source b (choose i)) i) ∧
      c.natReg (fresh b)=(choose i).tag ∧ c.work=steps := by
  classical
  by_cases hn : i.n<2
  · obtain ⟨c,he,hr,hw,htag⟩ := init_singleton b i hn
    refine ⟨4,c,by omega,he,?_,?_,hw⟩
    · simpa only [choose,if_pos hn,offset,source] using hr
    · simpa only [choose,if_pos hn,Kind.tag] using htag
  · obtain ⟨u,heu,hdu,hpc,hwork,hh,hf⟩ := init_large_prefix b i (by omega)
    have huPC : u.pc=initTagPC (choose i) := by
      rw [hpc]
      unfold choose
      rw [if_neg hn]
      split_ifs <;> rfl
    have hdu' : Relocation.LowData (fresh b) u (initialMachine (source b (choose i)) i) :=
      hdu.trans (Relocation.LowData.initial (fresh b) (program b) (source b (choose i)) i)
    obtain ⟨c,hec,hr,hw,htag⟩ := init_tail b i (choose i) u huPC hh hf hdu'
    refine ⟨8,c,by omega,?_,hr,htag,by omega⟩
    change execute (program b) (initialMachine (program b) i) (6+2)=c
    rw [execute_add,heu,hec]
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s41
section s42
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma update_singleton (b : Branches) (c : Machine) (hpc : c.pc=12) (hh : c.halted=false) (hf : c.fault=false)
    (htag : c.natReg (fresh b)=0) :
    ∃ d, execute (program b) c 3=d ∧ Relocation.LowData (fresh b) d c ∧
      d.pc=singletonOffset b+2*b.singleton.update ∧ d.work=c.work+3 ∧ d.halted=false ∧ d.fault=false ∧ d.natReg (fresh b)=0 := by
  let p := program b
  let u : Machine := {c with pc := 13,work := c.work+1,natReg := Function.update c.natReg (fresh b+1) 1}
  let v : Machine := {u with pc := 18,work := c.work+2}
  let d : Machine := {v with pc := singletonOffset b+2*b.singleton.update,work := c.work+3}
  have hRne : fresh b≠fresh b+1 := by omega
  have h12 : p.code[12]?=some (.natural (fresh b+1) 1) := by simpa [dispatchPrefix] using prefix_lookup b 12 (by omega)
  have h13 : p.code[13]?=some (.lessN (fresh b) (fresh b+1) 18) := by simpa [dispatchPrefix] using prefix_lookup b 13 (by omega)
  have h18 : p.code[18]?=some (.jump (singletonOffset b+2*b.singleton.update)) := by simpa [dispatchPrefix] using prefix_lookup b 18 (by omega)
  have hs0 : step p c=u := by rw [step_eq_effect p c _ hh (by rwa [hpc])];simp [instructionEffect,u,hpc]
  have hs1 : step p u=v := by simp [step,u,v,hh,h13,Function.update_of_ne hRne,htag]
  have hs2 : step p v=d := by simp [step,u,v,d,hh,h18]
  refine ⟨d,?_,⟨?_,fun _ _ => rfl,rfl,rfl⟩,rfl,rfl,hh,hf,?_⟩
  · change step p (step p (step p c))=d
    rw [hs0,hs1,hs2]
  · intro j hj
    change Function.update c.natReg (fresh b+1) 1 j=c.natReg j
    exact Function.update_of_ne (by omega) _ _
  · simpa only [d,v,u,Function.update_of_ne hRne] using htag
lemma update_large (b : Branches) (k : Kind) (hk : k=.small ∨ k=.normal) (c : Machine)
    (hpc : c.pc=12) (hh : c.halted=false) (hf : c.fault=false) (htag : c.natReg (fresh b)=k.tag) :
    ∃ d, execute (program b) c 5=d ∧ Relocation.LowData (fresh b) d c ∧
      d.pc=offset b k+2*(source b k).update ∧ d.work=c.work+5 ∧ d.halted=false ∧ d.fault=false ∧ d.natReg (fresh b)=k.tag := by
  classical
  let p := program b
  let u : Machine := {c with pc := 13,work := c.work+1,natReg := Function.update c.natReg (fresh b+1) 1}
  let v : Machine := {u with pc := 14,work := c.work+2}
  let w : Machine := {v with pc := 15,work := c.work+3,natReg := Function.update v.natReg (fresh b+1) 2}
  let z : Machine := {w with pc := (if k=.small then 17 else 16),work := c.work+4}
  let d : Machine := {z with pc := offset b k+2*(source b k).update,work := c.work+5}
  have hRne : fresh b≠fresh b+1 := by omega
  have hk1 : ¬k.tag<1 := by rcases hk with rfl | rfl <;> decide
  have hcode (j : ℕ) (hj : j<19) : p.code[j]?=(dispatchPrefix b)[j]? := prefix_lookup b j hj
  have hs0 : step p c=u := by
    have hc : p.code[12]?=some (.natural (fresh b+1) 1) := by simpa [dispatchPrefix] using hcode 12 (by omega)
    rw [step_eq_effect p c _ hh (by rwa [hpc])];simp [instructionEffect,u,hpc]
  have hs1 : step p u=v := by
    have hc : p.code[13]?=some (.lessN (fresh b) (fresh b+1) 18) := by simpa [dispatchPrefix] using hcode 13 (by omega)
    simp [step,u,v,hh,hc,Function.update_of_ne hRne,htag,hk1]
  have hs2 : step p v=w := by
    have hc : p.code[14]?=some (.natural (fresh b+1) 2) := by simpa [dispatchPrefix] using hcode 14 (by omega)
    simp [step,u,v,w,hh,hc]
  have hs3 : step p w=z := by
    have hc : p.code[15]?=some (.lessN (fresh b) (fresh b+1) 17) := by simpa [dispatchPrefix] using hcode 15 (by omega)
    rcases hk with rfl | rfl <;> simp [step,u,v,w,z,hh,hc,Function.update_of_ne hRne,htag,Kind.tag]
  have hs4 : step p z=d := by
    rcases hk with rfl | rfl
    · have hc : p.code[17]?=some (.jump (exactOffset b+2*b.small.update)) := by simpa [dispatchPrefix] using hcode 17 (by omega)
      simp [step,u,v,w,z,d,hh,hc,offset,source]
    · have hc : p.code[16]?=some (.jump (normalOffset b+2*b.normal.update)) := by simpa [dispatchPrefix] using hcode 16 (by omega)
      simp [step,u,v,w,z,d,hh,hc,offset,source]
  refine ⟨d,?_,⟨?_,fun _ _ => rfl,rfl,rfl⟩,rfl,rfl,hh,hf,?_⟩
  · change step p (step p (step p (step p (step p c))))=d
    rw [hs0,hs1,hs2,hs3,hs4]
  · intro j hj
    simp only [d,z,w,v,u,Function.update_of_ne (show j≠fresh b+1 by omega)]
  · simpa only [d,z,w,v,u,Function.update_of_ne hRne] using htag
lemma update_dispatch (b : Branches) (k : Kind) (c : Machine) (hpc : c.pc=12) (hh : c.halted=false) (hf : c.fault=false)
    (htag : c.natReg (fresh b)=k.tag) :
    ∃ steps d, steps≤5 ∧ execute (program b) c steps=d ∧ Relocation.LowData (fresh b) d c ∧
      d.pc=offset b k+2*(source b k).update ∧ d.work=c.work+steps ∧ d.halted=false ∧ d.fault=false ∧ d.natReg (fresh b)=k.tag := by
  cases k with
  | singleton =>
    obtain ⟨d,he,hd,hpc,hw,hh,hf,htag⟩ := update_singleton b c hpc hh hf htag
    exact ⟨3,d,by omega,he,hd,hpc,hw,hh,hf,htag⟩
  | small =>
    obtain ⟨d,he,hd,hpc,hw,hh,hf,htag⟩ := update_large b .small (Or.inl rfl) c hpc hh hf htag
    exact ⟨5,d,by omega,he,hd,hpc,hw,hh,hf,htag⟩
  | normal =>
    obtain ⟨d,he,hd,hpc,hw,hh,hf,htag⟩ := update_large b .normal (Or.inr rfl) c hpc hh hf htag
    exact ⟨5,d,by omega,he,hd,hpc,hw,hh,hf,htag⟩
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s42
section s43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma prepend_execute (p : Program) (c u d : Machine) (steps : ℕ) (h : execute p c steps=u) (he : Ends p u d) : Ends p c d := by
  obtain ⟨n,hn,hh,hf⟩ := he
  exact ⟨steps+n,by rw [execute_add,h,hn],hh,hf⟩
lemma initial_call (b : Branches) (i : Input) (g : Machine)
    (hg : Ends (source b (choose i)) (initialMachine (source b (choose i)) i) g) :
    ∃ c, Ends (program b) (initialMachine (program b) i) c ∧
      Relocation.LowData (fresh b) c g ∧ c.natReg (fresh b)=(choose i).tag ∧ c.work≤2*g.work+9 := by
  obtain ⟨steps,u,hsteps,heu,hu,htag,huw⟩ := initialize_dispatch b i
  obtain ⟨c,he,hd,hw,ht⟩ := Relocation.ends (program b) (source b (choose i)) (fresh b) (offset b (choose i)) (returnPC b)
    (source_embeds b (choose i)) (source_operands b (choose i)) (return_halt b) u (initialMachine (source b (choose i)) i) g hu hg
  refine ⟨c,prepend_execute _ _ _ _ _ heu he,hd,ht.trans htag,?_⟩
  simp only [initialMachine,Nat.sub_zero] at hw
  omega
lemma update_call (b : Branches) (k : Kind) (c g g' : Machine) (e : ℕ)
    (hcg : Relocation.LowData (fresh b) c g) (htag : c.natReg (fresh b)=k.tag)
    (hg : Ends (source b k) (deletionMachine (source b k) g e) g') :
    ∃ d, Ends (program b) (deletionMachine (program b) c e) d ∧
      Relocation.LowData (fresh b) d g' ∧ d.natReg (fresh b)=k.tag ∧ d.work≤c.work+2*(g'.work-g.work)+6 := by
  let start := deletionMachine (program b) c e
  let guest := deletionMachine (source b k) g e
  have hstartTag : start.natReg (fresh b)=k.tag := by
    have hne : fresh b≠5 := by have := fresh_ge b;omega
    simpa only [start,deletionMachine,resume,Function.update_of_ne hne] using htag
  obtain ⟨steps,u,hsteps,heu,hu,hpc,huw,hh,hf,ht⟩ := update_dispatch b k start rfl rfl rfl hstartTag
  have hdata : Relocation.LowData (fresh b) u guest := hu.trans (hcg.deletion (program b) (source b k) e)
  have hrep : Relocation.Rep (fresh b) (offset b k) (returnPC b) u guest :=
    ⟨hdata,by simpa only [Relocation.destination,guest,deletionMachine,resume,Bool.false_eq_true,if_false] using hpc,hh,hf⟩
  obtain ⟨d,he,hd,hw,htag⟩ := Relocation.ends (program b) (source b k) (fresh b) (offset b k) (returnPC b)
    (source_embeds b k) (source_operands b k) (return_halt b) u guest g' hrep hg
  refine ⟨d,prepend_execute _ _ _ _ _ heu he,hd,htag.trans ht,?_⟩
  change u.work=c.work+steps at huw
  change d.work≤u.work+2*(g'.work-g.work)+1 at hw
  omega
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s43
section s44
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma ends_running_work_positive (p : Program) (c d : Machine)
    (hh : c.halted = false) (he : Ends p c d) : c.work+1 ≤ d.work := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute p c t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix p c t hhalt'
  have hr : 0 < r := by
    by_contra hn
    have hr0 : r = 0 := by omega
    have hh' : (execute p c r).halted = true := by rw [hrun,ht];exact hhalt
    simp only [hr0,execute,Function.iterate_zero,id_eq,hh,Bool.false_eq_true] at hh'
  rw [ht] at hrwork
  omega
lemma call_overhead_absorbed (D overhead before after cost : ℕ)
    (hstep : before+1 ≤ after) (hcost : cost ≤ D*(after-before)+overhead) :
    cost ≤ (D+overhead)*(after-before) := by
  have hpos : 1 ≤ after-before := by omega
  have hh := Nat.mul_le_mul_left overhead hpos
  rw [Nat.mul_one] at hh
  rw [Nat.add_mul]
  omega
lemma live_take_subset {k : ℕ} (ds : List (Fin k)) (j : ℕ) : live ds ⊆ live (ds.take j) := by
  classical
  intro e he
  simp only [live,Finset.mem_sdiff,Finset.mem_univ,true_and,List.mem_toFinset] at he ⊢
  intro hh
  exact he (List.mem_of_mem_take hh)
end DecrAlmostLinearSSSP.Decremental
end s44
section s45
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma OnlineRun.initial_execution {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : ∃ c, cs[0]? = some c ∧ Ends p (initialMachine p i) c := by
  induction h with
  | init he => exact ⟨_,rfl,he⟩
  | @next ds cs c d h hlast e hd ih =>
    obtain ⟨a,ha,he⟩ := ih
    cases cs with
    | nil => simp at ha
    | cons b rest =>
      have hab : b = a := by simpa using ha
      subst b
      exact ⟨a,rfl,he⟩
lemma Maintains.initialization {p : Program} {C : ℝ} {a : ℕ → ℝ} {queryBound : ℕ}
    {logWeights : Bool} {i : Input} (h : Maintains p C a queryBound logWeights i) :
    ∃ c, Ends p (initialMachine p i) c ∧ stored c i.source.val = 0 ∧
      (∀ v : Fin i.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
      (∀ v : Fin i.n, i.dist [] v ≤ stored c v.val ∧
        stored c v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
        (stored c v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) ∧
      (c.work : ℝ) ≤ C*i.size*a i.size/i.accuracy*
        (if logWeights then max 1 (logarithm2 i.W) else 1) := by
  obtain ⟨cs,hrun,hlen,hgood,hcost,_⟩ := h [] (by simp [Legal])
  obtain ⟨c,hfirst,hend⟩ := hrun.initial_execution
  have hg := hgood 0 c hfirst
  have hcs : cs = [c] := by
    cases cs with
    | nil => simp at hfirst
    | cons d rest =>
      have hd : d = c := by simpa using hfirst
      subst d
      have hr : rest = [] := by simpa using hlen
      subst rest
      rfl
  have hc := hcost c (by simp [hcs])
  refine ⟨c,hend,hg.1,hg.2.1,?_,?_⟩
  · simpa using hg.2.2
  · simpa using hc
end DecrAlmostLinearSSSP.Decremental
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma Ends.deterministic {p : Program} {c d e : Machine} (hd : Ends p c d) (he : Ends p c e) : d = e := by
  obtain ⟨t,rfl,hhalt,_⟩ := hd
  obtain ⟨u,rfl,hhalt',_⟩ := he
  rcases le_total t u with htu | hut
  · have heq : u = t+(u-t) := by omega
    conv_rhs => rw [heq,execute_add,execute_halted p _ hhalt]
  · have heq : t = u+(t-u) := by omega
    conv_lhs => rw [heq,execute_add,execute_halted p _ hhalt']
end DecrAlmostLinearSSSP.Decremental
end s46
section s47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma OnlineRun.length {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : cs.length = ds.length+1 := by
  induction h with
  | init => rfl
  | next _ _ _ _ ih => simp only [List.length_append,List.length_singleton];omega
lemma OnlineRun.transition_at {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) (k : ℕ) (hk : k < ds.length) :
    ∃ c d, cs[k]? = some c ∧ cs[k+1]? = some d ∧ Ends p (deletionMachine p c (ds[k]).val) d := by
  induction h generalizing k with
  | init => simp at hk
  | @next ds cs c d h hlast e hd ih =>
    have hlen := h.length
    by_cases hlt : k < ds.length
    · obtain ⟨c',d',hc',hd',he'⟩ := ih k hlt
      refine ⟨c',d',?_,?_,?_⟩
      · simpa only [List.getElem?_append_left (show k < cs.length by omega)] using hc'
      · simpa only [List.getElem?_append_left (show k+1 < cs.length by omega)] using hd'
      · simpa only [List.getElem_append_left hlt] using he'
    · have heq : k = ds.length := by simp only [List.length_append,List.length_singleton] at hk;omega
      subst k
      have hc : cs[ds.length]? = some c := by
        rw [List.getLast?_eq_getElem?] at hlast
        simpa only [hlen,Nat.add_sub_cancel] using hlast
      refine ⟨c,d,?_,?_,?_⟩
      · simpa only [List.getElem?_append_left (show ds.length < cs.length by omega)] using hc
      · rw [show ds.length+1 = cs.length from hlen.symm,List.getElem?_append_right le_rfl,Nat.sub_self]
        rfl
      · have he : (ds++[e])[ds.length] = e := by simp
        simpa only [he] using hd
lemma Ends.work_mono {p : Program} {c d : Machine} (h : Ends p c d) : c.work ≤ d.work := by
  obtain ⟨t,ht,_,_⟩ := h
  rw [← ht]
  exact execute_work_mono p c t
lemma OnlineRun.work_le_last {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) (last : Machine) (hlast : cs.getLast? = some last) :
    ∀ c ∈ cs, c.work ≤ last.work := by
  induction h generalizing last with
  | @init c he =>
    have heq : c = last := by simpa using hlast
    subst last
    intro d hd
    have hd' : d = c := by simpa using hd
    subst d
    exact le_rfl
  | @next ds cs c d h hlastc e hd ih =>
    have heq : d = last := by simpa using hlast
    subst last
    intro z hz
    simp only [List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | hz
    · exact (ih c hlastc z hz).trans hd.work_mono
    · subst z;exact le_rfl
end DecrAlmostLinearSSSP.Decremental
end s47
section s48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
structure Pair (b : Branches) (k : Kind) (j : ℕ) (host guest : Machine) : Prop where
  data : Relocation.LowData (fresh b) host guest
  tag : host.natReg (fresh b)=k.tag
  work : host.work≤2*guest.work+6*j+9
structure Aligned (b : Branches) (k : Kind) (host guest : List Machine) : Prop where
  length : host.length=guest.length
  matching : ∀ j c g, host[j]?=some c → guest[j]?=some g → Pair b k j c g
lemma Aligned.last {b : Branches} {k : Kind} {host guest : List Machine} (h : Aligned b k host guest)
    (c g : Machine) (hc : host.getLast?=some c) (hg : guest.getLast?=some g) :
    Pair b k (guest.length-1) c g := by
  rw [List.getLast?_eq_getElem?] at hc hg
  rw [h.length] at hc
  exact h.matching _ c g hc hg
lemma Aligned.append {b : Branches} {k : Kind} {host guest : List Machine} (h : Aligned b k host guest)
    (c g : Machine) (hp : Pair b k guest.length c g) : Aligned b k (host++[c]) (guest++[g]) := by
  refine ⟨by simp only [List.length_append,List.length_singleton,h.length],?_⟩
  intro j d f hd hf
  by_cases hj : j<host.length
  · rw [List.getElem?_append_left hj] at hd
    rw [List.getElem?_append_left (by rwa [←h.length])] at hf
    exact h.matching j d f hd hf
  · have hjeq : j=host.length := by
      have hjlt : j<(host++[c]).length := by
        by_contra hn
        have hnone : (host++[c])[j]?=none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [hnone] at hd;contradiction
      simp only [List.length_append,List.length_singleton] at hjlt
      omega
    subst j
    rw [List.getElem?_append_right le_rfl,Nat.sub_self] at hd
    rw [h.length,List.getElem?_append_right le_rfl,Nat.sub_self] at hf
    have hcd : c=d := Option.some.inj hd
    have hgf : g=f := Option.some.inj hf
    subst d;subst f
    rwa [h.length]
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s48
section s49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma lift_online (b : Branches) (i : Input) (ds : List (Fin i.k)) (guest : List Machine)
    (hr : OnlineRun (source b (choose i)) i ds guest) :
    ∃ (host : List Machine) (last : Machine), OnlineRun (program b) i ds host ∧ host.getLast?=some last ∧
      Aligned b (choose i) host guest := by
  induction hr with
  | @init g he =>
    obtain ⟨c,hc,hdata,htag,hwork⟩ := initial_call b i g he
    refine ⟨[c],c,OnlineRun.init hc,rfl,⟨rfl,?_⟩⟩
    intro j d f hd hf
    cases j with
    | zero =>
      have hcd : c=d := Option.some.inj hd
      have hgf : g=f := Option.some.inj hf
      subst d;subst f
      exact ⟨hdata,htag,by simpa using hwork⟩
    | succ j => simp at hd
  | @next ds guest c d hrun hlast e hend ih =>
    obtain ⟨host,last,hhost,hlastHost,halign⟩ := ih
    have hpair := halign.last last c hlastHost hlast
    obtain ⟨next,hnext,hdata,htag,hwork⟩ := update_call b (choose i) last c d e.val hpair.data hpair.tag hend
    have hmono : c.work≤d.work := hend.work_mono
    have hlen : guest.length=ds.length+1 := hrun.length
    have hp : Pair b (choose i) guest.length next d := by
      refine ⟨hdata,htag,?_⟩
      have hpwork := hpair.work
      omega
    exact ⟨host++[next],next,OnlineRun.next hhost hlastHost e hnext,by simp,halign.append next d hp⟩
lemma Aligned.source_at {b : Branches} {k : Kind} {host guest : List Machine} (h : Aligned b k host guest)
    (j : ℕ) (c : Machine) (hc : host[j]?=some c) :
    ∃ g, guest[j]?=some g ∧ Pair b k j c g := by
  have hj : j<guest.length := by
    rw [←h.length]
    by_contra hn
    have hnone : host[j]?=none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hnone] at hc;contradiction
  refine ⟨guest[j],List.getElem?_eq_getElem hj,?_⟩
  exact h.matching j c guest[j] hc (List.getElem?_eq_getElem hj)
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s49
section s50
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Dispatcher
lemma online_work_positive {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : ∀ c∈cs, 1≤c.work := by
  induction h with
  | @init c he =>
    intro d hd
    have hdc : d=c := by simpa using hd
    subst d;exact Relocation.initial_ends_work_positive p i c he
  | @next ds cs c d hr hlast e he ih =>
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ih z hz
    · have hzd : z=d := by simpa using hz
      subst z
      exact (ih c (List.mem_of_getLast? hlast)).trans he.work_mono
lemma maintains_transfer (b : Branches) (i : Input) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (h : Maintains (source b (choose i)) C a queryBound true i) :
    Maintains (program b) (11*C) a 9 true i := by
  classical
  intro ds hd
  obtain ⟨guest,hguest,hguestLen,hgood,hwork,hquery⟩ := h ds hd
  obtain ⟨host,last,hhost,hlast,halign⟩ := lift_online b i ds guest hguest
  refine ⟨host,hhost,hhost.length,?_,?_,?_⟩
  · intro j c hc
    obtain ⟨g,hg,hpair⟩ := halign.source_at j c hc
    obtain ⟨hs,hn,hv⟩ := hgood j g hg
    refine ⟨(hpair.data.stored i.source.val).trans hs,?_,?_⟩
    · intro v
      simpa only [hpair.data.natMem,hpair.data.realMem] using hn v
    · intro v
      rw [hpair.data.stored v.val]
      exact hv v
  · intro c hc
    have hcIndex : host[host.length-1]?=some c := by rwa [←List.getLast?_eq_getElem?]
    obtain ⟨g,hgIndex,hpair⟩ := halign.source_at (host.length-1) c hcIndex
    have hgLast : guest.getLast?=some g := by rw [List.getLast?_eq_getElem?,←halign.length];exact hgIndex
    have hgBound := hwork g hgLast
    have hgPositive := online_work_positive hguest g (List.mem_of_getLast? hgLast)
    have hHostLen := hhost.length
    have hpWork := hpair.work
    have hNat : c.work+6*ds.length ≤ 2*(g.work+6*ds.length)+9 := by omega
    have hReal : (((c.work+6*ds.length : ℕ) : ℝ)) ≤ 2*(((g.work+6*ds.length : ℕ) : ℝ))+9 := by exact_mod_cast hNat
    have hgOne : (1 : ℝ) ≤ (((g.work+6*ds.length : ℕ) : ℝ)) := by exact_mod_cast (show 1≤g.work+6*ds.length by omega)
    change (((c.work+6*ds.length : ℕ) : ℝ)) ≤ (11*C)*i.size*a i.size/i.accuracy*max 1 (logarithm2 i.W)
    change (((g.work+6*ds.length : ℕ) : ℝ)) ≤ C*i.size*a i.size/i.accuracy*max 1 (logarithm2 i.W) at hgBound
    have hb : (((c.work+6*ds.length : ℕ) : ℝ)) ≤ 11*(C*i.size*a i.size/i.accuracy*max 1 (logarithm2 i.W)) := by nlinarith
    convert hb using 1 <;> ring
  · intro c hc v
    exact query_nine b c v.val
end DecrAlmostLinearSSSP.Decremental.Dispatcher
end s50
section s51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma Maintains.mono {p : Program} {i : Input} {C D : ℝ} {a b : ℕ → ℝ} {queryBound queryBound' : ℕ} {logWeights logWeights' : Bool}
    (h : Maintains p C a queryBound logWeights i)
    (hc : C*i.size*a i.size/i.accuracy*(if logWeights then max 1 (logarithm2 i.W) else 1) ≤
      D*i.size*b i.size/i.accuracy*(if logWeights' then max 1 (logarithm2 i.W) else 1))
    (hq : queryBound≤queryBound') : Maintains p D b queryBound' logWeights' i := by
  intro ds hd
  obtain ⟨cs,hr,hlen,hgood,hwork,hquery⟩ := h ds hd
  refine ⟨cs,hr,hlen,hgood,fun c hh => (hwork c hh).trans hc,?_⟩
  intro c hmem v
  obtain ⟨d,he,hw,hflag,hvalue,hrm,hnm⟩ := hquery c hmem v
  exact ⟨d,he,hw.trans (Nat.add_le_add_left hq c.work),hflag,hvalue,hrm,hnm⟩
end DecrAlmostLinearSSSP.Decremental
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma maintenance_cost_mono (i : Input) (hi : i.Valid) (C D A B : ℝ)
    (hC : 0≤C) (hCD : C≤D) (hA : 0≤A) (hAB : A≤B) :
    C*i.size*A/i.accuracy*max 1 (logarithm2 i.W) ≤ D*i.size*B/i.accuracy*max 1 (logarithm2 i.W) := by
  have hm : (0 : ℝ) ≤ i.size := Nat.cast_nonneg _
  have he := hi.2.2.2.1.le
  have hD : 0≤D := hC.trans hCD
  have hw : (0 : ℝ) ≤ max 1 (logarithm2 i.W) := le_trans (by norm_num) (le_max_left _ _)
  have hprod : C*A≤D*B := mul_le_mul hCD hAB hA hD
  have hscaled := mul_le_mul_of_nonneg_left hprod hm
  have hdiv := div_le_div_of_nonneg_right hscaled he
  have hfull := mul_le_mul_of_nonneg_right hdiv hw
  calc
    C*i.size*A/i.accuracy*max 1 (logarithm2 i.W) = ((i.size : ℝ)*(C*A))/i.accuracy*max 1 (logarithm2 i.W) := by ring
    _ ≤ ((i.size : ℝ)*(D*B))/i.accuracy*max 1 (logarithm2 i.W) := hfull
    _ = D*i.size*B/i.accuracy*max 1 (logarithm2 i.W) := by ring
lemma Maintains.saturated_log {p : Program} {i : Input} (hi : i.Valid) {C : ℝ} {a : ℕ → ℝ} {B : ℕ}
    (h : Maintains p C a B false i) (hC : 0≤C) (ha : 0≤a i.size) : Maintains p C a B true i := by
  apply h.mono ?_ le_rfl
  change C*i.size*a i.size/i.accuracy*1 ≤ C*i.size*a i.size/i.accuracy*max 1 (logarithm2 i.W)
  apply mul_le_mul_of_nonneg_left (le_max_left _ _)
  exact div_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) ha) hi.2.2.2.1.le
end DecrAlmostLinearSSSP.Decremental
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma general_domain_from_branches
    (normal : Program) (D : ℝ) (b : ℕ → ℝ) (hD : 0 < D) (hb : Subpolynomial b)
    (hnormal : ∀ i : Input, i.Valid → 2 ≤ i.n → 1/(i.size : ℝ) < i.accuracy →
      Maintains normal D b 9 true i)
    (small : Program) (E : ℝ) (e : ℕ → ℝ) (hE : 0 < E) (he : Subpolynomial e)
    (hsmall : ∀ i : Input, i.Valid → i.accuracy ≤ 1/(i.size : ℝ) →
      Maintains small E e 9 true i) :
    ∃ (p' : Program) (C' : ℝ) (a' : ℕ → ℝ) (queryBound' : ℕ),
      0<C' ∧ 0<queryBound' ∧ Subpolynomial a' ∧ ∀ i : Input, i.Valid → Maintains p' C' a' queryBound' true i := by
  let branches : Dispatcher.Branches := ⟨singletonProgram,small,normal⟩
  let K : ℝ := 8+E+D
  let combined : ℕ → ℝ := fun m => 1+e m+b m
  have hcombined : Subpolynomial combined := subpolynomial_add _ _
    (subpolynomial_add _ _ (subpolynomial_constant 1 (by norm_num)) he) hb
  have hK : 0<K := by dsimp [K];linarith
  refine ⟨Dispatcher.program branches,11*K,combined,9,by positivity,by omega,hcombined,?_⟩
  intro i hi
  have hnPositive := (lt_of_le_of_lt (Nat.zero_le _) i.source.isLt : 0 < i.n)
  have hmNat : 1 ≤ i.size := by have hn := hi.1;omega
  have hm : (0 : ℝ) < i.size := by exact_mod_cast (show 0 < i.size by omega)
  have hexactA : 0<e i.size := he.1 i.size
  have hbA : 0<b i.size := hb.1 i.size
  have hOne : (1 : ℝ)≤combined i.size := by dsimp [combined];linarith
  have hExact : e i.size≤combined i.size := by dsimp [combined];linarith
  have hNormal : b i.size≤combined i.size := by dsimp [combined];linarith
  have hchosen : Maintains (Dispatcher.source branches (Dispatcher.choose i)) K combined 9 true i := by
    by_cases hn : i.n<2
    · have hn1 : i.n=1 := by omega
      have hs := (singleton_maintains i hi hn1).saturated_log hi (by norm_num) (by norm_num)
      have hcost := maintenance_cost_mono i hi 8 K 1 (combined i.size) (by norm_num)
        (by dsimp [K];linarith) (by norm_num) hOne
      have hs' := hs.mono (D := K) (b := combined) (queryBound' := 9) (logWeights' := true) (by simpa using hcost) le_rfl
      simpa only [Dispatcher.choose,if_pos hn,Dispatcher.source,branches] using hs'
    · have hn2 : 2 ≤ i.n := by omega
      by_cases heps : (1 : ℝ)<(i.size : ℝ)*i.accuracy
      · have heps' : 1/(i.size : ℝ) < i.accuracy := (div_lt_iff₀ hm).mpr (by nlinarith only [heps])
        have hs := hnormal i hi hn2 heps'
        have hcost := maintenance_cost_mono i hi D K (b i.size) (combined i.size) hD.le
          (by dsimp [K];linarith) hbA.le hNormal
        have hs' := hs.mono (D := K) (b := combined) (queryBound' := 9) (logWeights' := true) (by simpa using hcost) le_rfl
        simpa only [Dispatcher.choose,if_neg hn,if_pos heps,Dispatcher.source,branches] using hs'
      · have heps' : i.accuracy≤1/(i.size : ℝ) := (le_div_iff₀ hm).mpr (by nlinarith only [heps])
        have hs := hsmall i hi heps'
        have hcost := maintenance_cost_mono i hi E K (e i.size) (combined i.size) hE.le
          (by dsimp [K];linarith) hexactA.le hExact
        have hs' := hs.mono (D := K) (b := combined) (queryBound' := 9) (logWeights' := true) (by simpa using hcost) le_rfl
        simpa only [Dispatcher.choose,if_neg hn,if_neg heps,Dispatcher.source,branches] using hs'
  exact Dispatcher.maintains_transfer branches i K combined 9 hchosen
end DecrAlmostLinearSSSP.Decremental
end s53
section s54
set_option autoImplicit false
open DecrAlmostLinearSSSP.Decremental
theorem solution
    (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (hC : 0 < C) (hquery : 0 < queryBound) (ha : Subpolynomial a)
    (hpoly : ∀ i : Input, i.Valid → 2 ≤ i.n → i.W ≤ i.size ^ 2 →
      1 / (i.size : ℝ) < i.accuracy → i.accuracy < 1 →
      Maintains p C a queryBound false i) :
    ∃ (p' : Program) (C' : ℝ) (a' : ℕ → ℝ) (queryBound' : ℕ),
      0 < C' ∧ 0 < queryBound' ∧ Subpolynomial a' ∧
      ∀ i : Input, i.Valid → Maintains p' C' a' queryBound' true i := by
  obtain ⟨normal,D,b,hD,hb,hnormal⟩ := normal_domain_sssp_adapter p C a queryBound hC ha hpoly
  obtain ⟨small,E,e,hE,he,hsmall⟩ := exact_small_accuracy_sssp
  exact general_domain_from_branches normal D b hD hb hnormal small E e hE he hsmall
end s54

