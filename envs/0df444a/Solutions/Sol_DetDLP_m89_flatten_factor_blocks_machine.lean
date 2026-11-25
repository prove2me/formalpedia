-- Prove2me | solution 1 for DetDLP.m89_flatten_factor_blocks_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T17:13:53.427401+00:00
-- url     : https://prove2.me/submissions/cb9e2d8f-65e6-4cc2-94c4-d2718160f135

import Definitions.Def_DetDLP_M89_CompileSpace
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false
namespace DetDLP.M89Flatten
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def program : BitProgram.Program 3 2 13 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 0 2 7
    | 2 => .pop 0 0 1 3
    | 3 => .pop 0 2 1 4
    | 4 => .pop 0 0 1 5
    | 5 => .branch 0 6 0
    | 6 => .push 1 2 3
    | 7 => .push 1 0 8
    | 8 => .pop 1 0 1 9
    | 9 => .branch 1 10 12
    | 10 => .push 0 0 8
    | _ => .halt

private abbrev cfg (pc : Option (Fin 13)) (r : Fin 3 → Bool) (src tmp : List Bool) : BitProgram.Cfg 3 2 13 :=
  ⟨pc,r,![src,tmp]⟩
private lemma set0 (a b c : List Bool) : Function.update ![a,b] 0 c = ![c,b] := by
  funext i; fin_cases i <;> simp
private lemma set1 (a b c : List Bool) : Function.update ![a,b] 1 c = ![a,c] := by
  funext i; fin_cases i <;> simp
private def run (n : ℕ) (q q' : Option (Fin 13)) (src tmp src' tmp' : List Bool) : Prop :=
  ∀ r, ∃ r', BitProgram.Trace program n (cfg q r src tmp) (cfg q' r' src' tmp')
private theorem chain {n m q q' q'' s t s' t' s'' t''} (h : run n q q' s t s' t')
    (g : run m q' q'' s' t' s'' t'') : run (n+m) q q'' s t s'' t'' := by
  intro r; obtain ⟨r',h'⟩ := h r; obtain ⟨r'',g'⟩ := g r'; exact ⟨_,h'.trans g'⟩
private lemma enter (w t : List Bool) : run 3 (some 0) (some 3) (true::true::w) t w t := by
  intro r; apply Exists.intro; apply Computation.Trace.of_iterate;
   simp [Function.iterate_succ_apply,BitProgram.step,BitProgram.execInstr,program,cfg,set0,set1,
    BitProgram.readRegs, Function.update_apply] <;> try rfl
private lemma bit (b : Bool) (w t : List Bool) : run 4 (some 3) (some 3) (b::true::w) t w (b::t) := by
  intro r; apply Exists.intro; apply Computation.Trace.of_iterate;
   simp [Function.iterate_succ_apply,BitProgram.step,BitProgram.execInstr,program,cfg,set0,set1,
    BitProgram.readRegs, Function.update_apply] <;> try rfl
private lemma close (w t : List Bool) : run 3 (some 3) (some 0) (false::false::w) t w t := by
  intro r; apply Exists.intro; apply Computation.Trace.of_iterate;
   simp [Function.iterate_succ_apply,BitProgram.step,BitProgram.execInstr,program,cfg,set0,set1,
    BitProgram.readRegs, Function.update_apply] <;> try rfl
private lemma finish (t : List Bool) : run 3 (some 0) (some 8) [false] t [] (false::t) := by
  intro r; apply Exists.intro; apply Computation.Trace.of_iterate;
   simp [Function.iterate_succ_apply,BitProgram.step,BitProgram.execInstr,program,cfg,set0,set1,
    BitProgram.readRegs, Function.update_apply] <;> try rfl
private lemma back (b : Bool) (s t : List Bool) : run 3 (some 8) (some 8) s (b::t) (b::s) t := by
  intro r; apply Exists.intro; apply Computation.Trace.of_iterate;
   simp [Function.iterate_succ_apply,BitProgram.step,BitProgram.execInstr,program,cfg,set0,set1,
    BitProgram.readRegs, Function.update_apply] <;> try rfl
private lemma stop (s : List Bool) : run 3 (some 8) none s [] s [] := by
  intro r; apply Exists.intro; apply Computation.Trace.of_iterate;
   simp [Function.iterate_succ_apply,BitProgram.step,BitProgram.execInstr,program,cfg,set0,set1,
    BitProgram.readRegs, Function.update_apply] <;> try rfl

private def payload (w : List Bool) : List Bool := w.flatMap (fun b => [b,true])
private lemma body (bs rest tmp : List Bool) : run (4*bs.length+3) (some 3) (some 0)
    (payload bs ++ false::false::rest) tmp rest (bs.reverse ++ tmp) := by
  induction bs generalizing tmp with
  | nil => exact close rest tmp
  | cons b bs ih =>
    simpa [payload,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,List.append_assoc] using
      chain (bit b (payload bs ++ false::false::rest) tmp) (ih (b::tmp))
private lemma bodyframe (bs : List Bool) : Encoding.frame (bs ++ [false]) = true :: (payload bs ++ [false,false]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change true :: b :: Encoding.frame (bs ++ [false]) = _
    rw [ih]; rfl
private lemma block (bs rest tmp : List Bool) : run (4*bs.length+6) (some 0) (some 0)
    (true :: (Encoding.frame (bs++[false]) ++ rest)) tmp rest (bs.reverse ++ tmp) := by
  rw [bodyframe, show 4*bs.length+6 = 3+(4*bs.length+3) by omega]; simpa [List.append_assoc] using
    chain (enter (payload bs ++ false::false::rest) tmp) (body bs rest tmp)
private lemma reverseRun (xs ys : List Bool) : run (3*xs.length+3) (some 8) none ys xs (xs.reverse ++ ys) [] := by
  induction xs generalizing ys with
  | nil => exact stop ys
  | cons b xs ih =>
    simpa [Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,List.append_assoc] using
      chain (back b ys xs) (ih (b::ys))

private def chunks (blocks : List (List Bool)) := Encoding.encodeList (fun bs => bs ++ [false]) blocks
private def cost (blocks : List (List Bool)) := (blocks.map (fun bs => 4*bs.length+6)).sum
private lemma parse (blocks : List (List Bool)) (tmp : List Bool) : run (cost blocks+3) (some 0) (some 8)
    (chunks blocks) tmp [] (false::(blocks.flatten.reverse ++ tmp)) := by
  induction blocks generalizing tmp with
  | nil => exact finish tmp
  | cons bs blocks ih =>
    simpa [chunks,Encoding.encodeList,cost,List.append_assoc,Nat.add_assoc] using
      chain (block bs (chunks blocks) tmp) (ih (bs.reverse ++ tmp))
private lemma estimate (blocks : List (List Bool)) :
    cost blocks + 3*blocks.flatten.length ≤ 7*(chunks blocks).length := by
  have fr (bs : List Bool) : (Encoding.frame bs).length=2*bs.length+1 := by
    induction bs with
    | nil => rfl
    | cons b bs ih => change (Encoding.frame bs).length+1+1 = 2*(bs.length+1)+1; omega
  induction blocks with
  | nil => decide
  | cons bs blocks ih =>
    change 4*bs.length+6 + cost blocks + 3*(bs++blocks.flatten).length ≤ 7*((Encoding.frame (bs++[false]) ++ chunks blocks).length+1)
    simp only [List.length_append,fr,List.length_singleton]; omega
private def atoms {α : Type*} (enc : α → List Bool) (xs : List α) := xs.flatMap (fun x => true::Encoding.frame (enc x))
private lemma listEq {α : Type*} (f : α → List Bool) (xs : List α) : Encoding.encodeList f xs = atoms f xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [Encoding.encodeList,ih,atoms,List.flatMap_cons,List.cons_append,List.append_assoc]

/-- A fixed machine removes the outer block framing and retains the order of all inner items. -/
theorem flatten_runs (p : ℕ) [NeZero p] {m : ℕ} (F : Fin m → List (ZMod p)ˣ) :
    let input := encodeFpFactorBlocks F
    let output := encodeNatListBin ((List.ofFn F).flatten.map (fun a : (ZMod p)ˣ => (a : ZMod p).val))
    RunsWithin (GuardedCompiler.primitive program) program.outputStack input output
      ((49*input.length+63 : ℕ) : ℝ) ((18*input.length+48 : ℕ) : ℝ) := by
  let enc := fun a : (ZMod p)ˣ => countWord (a : ZMod p).val
  let blocks := (List.ofFn F).map (atoms enc)
  have ch : chunks blocks = encodeFpFactorBlocks F := by
    unfold encodeFpFactorBlocks chunks blocks
    induction List.ofFn F with
    | nil => rfl
    | cons xs l ih => simp only [List.map_cons,Encoding.encodeList]; rw [← ih,listEq enc xs]
  have he : blocks.flatten ++ [false] = encodeNatListBin ((List.ofFn F).flatten.map (fun a : (ZMod p)ˣ => (a : ZMod p).val)) := by
    rw [encodeNatListBin,listEq]; congr 1
    unfold blocks
    induction List.ofFn F with
    | nil => rfl
    | cons xs xss ih =>
      simp only [List.map_cons,List.flatten_cons,List.map_append,atoms,List.flatMap_append] at *
      rw [ih]; congr 1
      induction xs with
      | nil => rfl
      | cons a xs ih' => simp [enc,ih']
  have hi : BitProgram.initial program (chunks blocks) = cfg (some 0) (fun _ => false) (chunks blocks) [] := by
    unfold BitProgram.initial cfg; congr 1; funext i; fin_cases i <;> rfl
  have pr := chain (parse blocks []) (reverseRun (false :: (blocks.flatten.reverse ++ [])) [])
  obtain ⟨r,tr⟩ := pr (fun _ => false)
  rw [← hi] at tr
  simp only [List.append_nil,List.reverse_cons,List.reverse_reverse,he] at tr
  have hr := CompileSpace.compile_runsWithin_from_time program tr rfl (show (cfg none r _ []).stacks program.outputStack = _ from rfl)
  have hn := estimate blocks
  rw [← ch]
  obtain ⟨k,c,ht,hh,hw,htime,hspace⟩ := hr
  refine ⟨k,c,ht,hh,hw,htime.trans ?_,fun i d h tr' => (hspace i d h tr').trans ?_⟩ <;>
    exact_mod_cast (by simp only [List.length_cons,List.length_reverse] at *; omega : _)

end DetDLP.M89Flatten
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount), ∀ (p : ℕ) [NeZero p] {m : ℕ} (F : Fin m → List (ZMod p)ˣ),
     let input := encodeFpFactorBlocks F
    let output := encodeNatListBin ((List.ofFn F).flatten.map (fun a : (ZMod p)ˣ => (a : ZMod p).val))
    RunsWithin M out input output
      ((49*input.length+63 : ℕ) : ℝ) ((18*input.length+48 : ℕ) : ℝ) := by
  exact ⟨GuardedCompiler.primitive M89Flatten.program, M89Flatten.program.outputStack, fun p _ _ F => M89Flatten.flatten_runs p F⟩
#print axioms solution
