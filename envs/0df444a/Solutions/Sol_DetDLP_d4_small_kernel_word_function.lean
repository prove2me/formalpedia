-- Prove2me | solution 1 for DetDLP.d4_small_kernel_word_function
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:19:12.283903+00:00
-- url     : https://prove2.me/submissions/8f8215c1-237f-4682-83a9-14aba8005b8a

import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_DetDLP_f6a_small_kernel_bit_machine
import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
set_option maxHeartbeats 350000
open Groundwork OAI.Algorithms.SubexponentialSAT BitProgram
namespace D4BI
abbrev W := List Bool
abbrev Bank := List W
abbrev S := ℕ × Bank
variable {r s l : ℕ}
abbrev Q (r l : ℕ) := Option (Fin l) × (Fin r → Bool)
noncomputable def code (q : Q r l) := (Fintype.equivFin (Q r l) q).val
private theorem inj : Function.Injective (code (r:=r) (l:=l)) := Fin.val_injective.comp (Fintype.equivFin _).injective
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.getD PolyT.tail PolyT.headD P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_cons__3a60f43a3b86
private def modify (n : ℕ) (f : W → W) (xs : Bank) : Bank := xs.modify n f
private theorem mod_poly {α : Type} [Enc α] (n : ℕ) {xs : α → Bank} (h : PolyT xs) (f : W → W) (hf : PolyT f) : PolyT (fun a => modify n f (xs a)) := by
  induction n generalizing xs with
  | zero =>
    have t : PolyT (fun a => if (xs a).isEmpty then [] else f ((xs a).headD []) :: (xs a).tail) := by fun_prop
    exact t.congr fun a => by cases xs a <;> rfl
  | succ n ih =>
    have t : PolyT (fun a => if (xs a).isEmpty then [] else (xs a).headD [] :: modify n f (xs a).tail) := by apply P2M_Groundwork_PolyT_ite__226169acf219 <;> first | fun_prop | exact ih (PolyT.tail h)
    exact t.congr fun a => by cases xs a <;> rfl
private theorem mod_len (n : ℕ) (f : W → W) (hf : ∀ t, len (f t) ≤ len t + 3) (xs : Bank) : len (modify n f xs) ≤ len xs + 3 := by
  induction n generalizing xs with
  | zero => cases xs with
    | nil => simp [modify]
    | cons a xs => have := hf a; change len (f a :: xs) ≤ _; simp only [len_cons]; omega
  | succ n ih => cases xs with
    | nil => simp [modify]
    | cons a xs => have := ih xs; change len (a :: modify n f xs) ≤ _; simp only [len_cons] at *; omega
private theorem modify_ofFn {α : Type} (xs : Fin s → α) (i : Fin s) (f : α → α) :
    (List.ofFn xs).modify i.val f = List.ofFn (Function.update xs i (f (xs i))) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk; simp only [List.getElem_modify, List.getElem_ofFn]; split_ifs with h
    · subst j; simp
    · rw [Function.update_of_ne]; intro eq; exact h (congrArg Fin.val eq).symm
noncomputable def pc (q : Option (Fin l)) (reg : Fin r → Bool) := code (q,reg)
noncomputable def row (reg : Fin r → Bool) (i : Instr r s l) (a : S) : S :=
  let plain (q : Option (Fin l)) (v : Fin r → Bool) := (pc q v,a.2)
  let read (k : Fin s) (v h : Fin r) (q : Fin l) (bs : Bank) :=
    let kWord := a.2.getD k.val []
    (if kWord.isEmpty then pc (some q) (readRegs reg v h none) else if kWord.headD false then pc (some q) (readRegs reg v h (some true)) else pc (some q) (readRegs reg v h (some false)), bs)
  match i with
  | .halt => plain none reg
  | .goto q => plain (some q) reg
  | .set v b q => plain (some q) (Function.update reg v b)
  | .copy v t q => plain (some q) (Function.update reg v (reg t))
  | .bnot v t q => plain (some q) (Function.update reg v (!(reg t)))
  | .band v b c q => plain (some q) (Function.update reg v (reg b && reg c))
  | .bor v b c q => plain (some q) (Function.update reg v (reg b || reg c))
  | .bxor v b c q => plain (some q) (Function.update reg v (reg b ^^ reg c))
  | .branch t yes no => plain (some (if reg t then yes else no)) reg
  | .push k v q => (pc (some q) reg,modify k.val (fun w => reg v :: w) a.2)
  | .peek k v h q => read k v h q a.2
  | .pop k v h q => read k v h q (modify k.val List.tail a.2)
private theorem rp (reg : Fin r → Bool) (i : Instr r s l) : PolyT (row reg i) := by
  cases i <;> unfold row <;> dsimp only <;> first | fun_prop | apply PolyT.prodMk <;> first | fun_prop | apply mod_poly <;> fun_prop
private theorem rl (reg : Fin r → Bool) (i : Instr r s l) (a : S) : len (row reg i a).2 ≤ len a.2+3 := by
  cases i <;> simp only [row] <;> first | omega | apply mod_len; intro t; simp [len_bools]; omega
private theorem rc (reg : Fin r → Bool) (i : Instr r s l) (a : S) : (row reg i a).1 < Fintype.card (Q r l) := by
  cases i <;> simp only [row] <;> (repeat' split) <;> exact Fin.isLt _
private def lookup {ι : Type} (idx : ι → ℕ) (f : ι → S → S) : List ι → S → S
  | [],a => a
  | j::js,a => if a.1 = idx j then f j a else lookup idx f js a
private theorem lp {ι : Type} (idx : ι → ℕ) (f : ι → S → S) (hf : ∀ j, PolyT (f j)) (js : List ι) : PolyT (lookup idx f js) := by
  induction js with
  | nil => exact PolyT.id'
  | cons j js ih => change PolyT (fun a : S => if a.1 = idx j then f j a else lookup idx f js a); fun_prop
private theorem lok {ι : Type} (idx : ι → ℕ) (hi : Function.Injective idx) (f : ι → S → S) (a : S) (j : ι) (js : List ι) (h : j ∈ js) (ha : a.1 = idx j) : lookup idx f js a = f j a := by
  induction js with
  | nil => simp at h
  | cons k js ih =>
    by_cases e : j=k
    · subst k; simp [lookup,ha]
    · rw [lookup,if_neg (show a.1 ≠ idx k from fun he => e (hi (ha.symm.trans he)))]; exact ih ((List.mem_cons.mp h).resolve_left e)
noncomputable def each (p : Program r s l) (q : Q r l) (a : S) := match q.1 with
  | none => a
  | some j => row q.2 (p.code j) a
noncomputable def step (p : Program r s l) := lookup code (each p) (Finset.univ : Finset (Q r l)).toList
private theorem sp (p : Program r s l) : PolyT (step p) := by
  apply lp; intro ⟨u,g⟩; cases u with
  | none => exact PolyT.id'
  | some j => exact rp g _
private theorem sl (p : Program r s l) (a : S) : len (step p a) ≤ len a + (3*Fintype.card (Q r l)+8) := by
  unfold step
  induction (Finset.univ : Finset (Q r l)).toList with
  | nil => simp [lookup]
  | cons q js ih => rw [lookup]; split
                    · rcases q with ⟨_|j,g⟩
                      · change len a ≤ _; omega
                      · have h := rl g (p.code j) a
                        have h' := (Nat.size_le).mpr ((rc g (p.code j) a).trans (Nat.lt_two_pow_self (n:=Fintype.card (Q r l))))
                        change len (row g (p.code j) a) ≤ _
                        change len ((row g (p.code j) a).1,(row g (p.code j) a).2) ≤ len (a.1,a.2) + _
                        simp only [len_pair,len_nat]; omega
                    · exact ih
noncomputable def enc (c : Cfg r s l) : S := (pc c.pc c.regs,List.ofFn c.stacks)
private theorem se (p : Program r s l) (c : Cfg r s l) : step p (enc c) = ((BitProgram.step p c).map enc).getD (enc c) := by
  rw [step,lok _ inj _ _ (c.pc,c.regs) _ (by simp) rfl]
  rcases c with ⟨_|j,g,b⟩
  · rfl
  · change row g (p.code j) (pc (some j) g,List.ofFn b) = enc (execInstr (p.code j) ⟨some j,g,b⟩)
    generalize p.code j = i
    cases i <;> first | rfl | simp [row,execInstr,enc,modify,modify_ofFn,List.getD_eq_getElem?_getD]
    all_goals rename_i k v h q; cases b k with | nil => rfl | cons b bs => cases b <;> rfl
private theorem iter (p : Program r s l) {c d : Cfg r s l} {n : ℕ} (tr : BitProgram.Trace p n c d) (hd : d.pc=none) (fuel : W) (hn : n ≤ fuel.length) : fuel.foldl (fun a _ => step p a) (enc c) = enc d := by
  induction tr generalizing fuel with
  | refl c => induction fuel with
              | nil => rfl
              | cons b bs ih => simpa [List.foldl,se,BitProgram.step,hd] using ih (by omega)
  | cons st tr ih => cases fuel with
                     | nil => simp at hn
                     | cons b bs => rw [List.foldl,se,st]; apply ih hd <;> simpa using hn
end D4BI
open D4BI

private theorem interpret {r s l : ℕ} (p : BitProgram.Program r s l) (o : Fin s) :
    ∃ f : List (List Bool) × List Bool → List Bool, PolyT f ∧
    ∀ (bank : Fin s → List Bool) (fuel : List Bool) (n : ℕ) (rf : Fin r → Bool) (endBank : Fin s → List Bool),
      n ≤ fuel.length → BitProgram.Trace p n ⟨some p.entry,fun _ => false,bank⟩ ⟨none,rf,endBank⟩ →
      f (List.ofFn bank,fuel) = endBank o := by
  let run (a : Bank × W) := a.2.foldl (fun u _ => step p u) (pc (some p.entry) (fun _ : Fin r => false),a.1)
  have h : PolyT run := by
    exact PolyT.foldl_add (g:=fun (_ : Bank × W) u (_ : Bool) => step p u) (PolyT.snd PolyT.id') (PolyT.prodMk (PolyT.const _) (PolyT.fst PolyT.id')) ((sp p).comp (PolyT.fst (PolyT.snd PolyT.id'))) ⟨_,PB.const _,fun x c e he => sl p c⟩
  refine ⟨fun a => (run a).2.getD o.val [],PolyT.getD (PolyT.snd h) (PolyT.const _) (PolyT.const _),?_⟩
  intro bank fuel n rf bs hn tr
  have hv := iter p tr rfl fuel hn
  change (fuel.foldl _ (enc ⟨some p.entry,fun _ => false,bank⟩)).2.getD o.val [] = bs o
  rw [hv]; simp [enc,List.getD_eq_getElem?_getD]

open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT.Computation

theorem solution (C c L : ℕ) (E : PrimitiveMachine) (oe : Fin E.tapeCount) :
    ∃ (s K : ℕ) (sim : List (List Bool) × List Bool → List Bool), PolyT sim ∧
    ∀ x : Input C c, Nat.clog 2 x.S < L → entry x E oe →
      let r := x.G.nV+3
      let pairs := (List.finRange x.G.nE).map fun e => ((x.G.endpoints e).1.val,(x.G.endpoints e).2.val)
      let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
      let w := x.G.nE+x.G.nV*(x.p+Nat.clog 2 x.l)+1+x.p
      let B := 2^w
      let bank := List.replicate 8 ([] : List Bool) ++ [(2^x.G.nE : ℕ).bits,x.G.nV.bits,[],[],(1:ℕ).bits,[],[],[],(1:ℕ).bits,(1:ℕ).bits,(2^x.G.nE:ℕ).bits] ++
        [x.desc,r.bits,code.bits,(code/r).bits,(B-1).bits,B.bits,(B-1-2).bits] ++ List.replicate s []
      ∀ fuel : List Bool, K*(size x+1)^K ≤ fuel.length → ∃ z : ℕ, sim (bank,fuel) = z.bits ∧
        encodeNatListBin (List.ofFn fun i : Fin x.l => z/B^i.val%B%(2^x.p)) = answer x := by
  obtain ⟨s,lab,K,P,run⟩ := f6a_small_kernel_bit_machine E oe C c L
  obtain ⟨sim,sp,correct⟩ := interpret P ((13 : Fin 19).castAdd (7+s))
  refine ⟨s,K,sim,sp,?_⟩
  intro x hl he r pairs code w B bank fuel hf
  obtain ⟨z,n,rf,bs,hn,tr,_,hz,out⟩ := run x.G x.m x.k x.S _ x.p x.l x.desc x.A x.spec hl x.nV x.lm x.hp x.pS x.hl x.bounded he (fun _ => false)
  refine ⟨z,?_,out⟩
  have ans := correct _ fuel n rf bs (hn.trans hf) tr
  rw [← hz,← ans]; congr 2
  have append {m n : ℕ} (a : Fin m → List Bool) (b : Fin n → List Bool) : List.ofFn (fun i => Fin.addCases a b i) = List.ofFn a ++ List.ofFn b := by
    rw [List.ofFn_add]; congr 1
    · apply congrArg List.ofFn; funext i; exact Fin.addCases_left ..
    · apply congrArg List.ofFn; funext i; exact Fin.addCases_right ..
  simp only [append,List.ofFn_const,bank]; rw [List.append_assoc, List.append_assoc]; rfl
