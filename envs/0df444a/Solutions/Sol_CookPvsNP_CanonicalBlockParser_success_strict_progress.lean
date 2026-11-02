-- Prove2me | solution 1 for CookPvsNP.CanonicalBlockParser.success_strict_progress
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:24:37.347195+00:00
-- url     : https://prove2.me/submissions/c74213b5-f77c-4824-b753-bd95f62ca774

import Definitions.Def_CookPvsNP_CanonicalBlockParser
import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Theorems.Thm_CookPvsNP_stack_copy

open CookPvsNP

namespace StackProgPortLift

/-- Project a larger stack store to the ports selected by an embedding. -/
def project {K L A : Type} (r : K ↪ L) (s : L → List A) : K → List A :=
  fun k ↦ s (r k)

/-- Replace exactly the embedded ports, leaving all other stack contents intact. -/
noncomputable def write {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) : L → List A := by
  classical
  exact fun l ↦ if h : ∃ k, r k = l then t (Classical.choose h) else s l

/-- Lift one action, projecting read heads and keeping every unselected port. -/
noncomputable def liftAct {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) : (L → Option A) → L → StackAct A := by
  classical
  exact fun h l ↦ if hex : ∃ k, r k = l then f (fun k ↦ h (r k)) (Classical.choose hex) else .keep

/-- Lift a structured stack program along an injective port map. -/
noncomputable def liftProg {K L A : Type} (r : K ↪ L) : StackProg K A → StackProg L A
  | .act f => .act (liftAct r f)
  | .seq p q => .seq (liftProg r p) (liftProg r q)
  | .branch test p q => .branch (fun h ↦ test (fun k ↦ h (r k))) (liftProg r p) (liftProg r q)
  | .loop test p => .loop (fun h ↦ test (fun k ↦ h (r k))) (liftProg r p)

private theorem write_at {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) (k : K) : write r t s (r k) = t k := by
  classical
  unfold write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

private theorem write_outside {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) {l : L} (h : ∀ k, r k ≠ l) : write r t s l = s l := by
  classical
  unfold write
  split
  · rename_i hex
    obtain ⟨k, hk⟩ := hex
    exact (h k hk).elim
  · rfl

private theorem liftAct_at {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) (h : L → Option A) (k : K) :
    liftAct r f h (r k) = f (fun j ↦ h (r j)) k := by
  classical
  unfold liftAct
  split
  · rename_i hex
    have hk : Classical.choose hex = k := r.injective (Classical.choose_spec hex)
    rw [hk]
  · rename_i hex
    exact (hex ⟨k, rfl⟩).elim

/-- A lifted atomic action simulates the source action and preserves every
    port outside the embedded source interface. -/
theorem lift_applyAct {K L A : Type} (r : K ↪ L)
    (f : (K → Option A) → K → StackAct A) (s : L → List A) :
    StackProg.applyAct (liftAct r f) s =
      write r (StackProg.applyAct f (project r s)) s := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    simp [StackProg.applyAct, project, liftAct_at, write_at]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    simp [StackProg.applyAct, liftAct, hex, write_outside r _ _ hout, StackAct.apply]



private theorem project_write {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) : project r (write r t s) = t := by
  funext k
  exact write_at r t s k

private theorem write_project {K L A : Type} (r : K ↪ L) (s : L → List A) :
    write r (project r s) s = s := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    rw [write_at]
    rfl
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    exact write_outside r _ _ hout

private theorem write_overwrite {K L A : Type} (r : K ↪ L) (u t : K → List A)
    (s : L → List A) : write r u (write r t s) = write r u s := by
  classical
  funext l
  by_cases hex : ∃ k, r k = l
  · obtain ⟨k, rfl⟩ := hex
    simp only [write_at]
  · have hout : ∀ k, r k ≠ l := by
      intro k hk
      exact hex ⟨k, hk⟩
    rw [write_outside r u _ hout, write_outside r t s hout, write_outside r u s hout]

private theorem projected_heads {K L A : Type} (r : K ↪ L) (base : L → List A)
    (s : K → List A) (hs : project r base = s) :
    (fun k ↦ (base (r k)).head?) = fun k ↦ (s k).head? := by
  funext k
  exact congrArg List.head? (congrFun hs k)

/-- Injectively reindexing a structured stack program simulates every source
    execution with exactly the same step count. Nonselected ports keep their
    original contents. -/
theorem lift_exec {K L A : Type} (r : K ↪ L) {p : StackProg K A}
    {s t : K → List A} {n : ℕ} (h : p.Exec s t n) :
    ∀ base : L → List A, project r base = s →
      (liftProg r p).Exec base (write r t base) n := by
  induction h with
  | act f s =>
    intro base hb
    have heq := lift_applyAct r f base
    rw [hb] at heq
    change (StackProg.act (liftAct r f)).Exec base (write r (StackProg.applyAct f s) base) 1
    rw [← heq]
    exact StackProg.Exec.act _ _
  | @seq p q s t u n m hp hq ihp ihq =>
    intro base hb
    have h1 := ihp base hb
    have h2 := ihq (write r t base) (project_write r t base)
    have hs := StackProg.Exec.seq h1 h2
    rw [write_overwrite] at hs
    simpa only [liftProg] using hs
  | @branchTrue test p q s t n htest hp ih =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = true := by
      change test (fun k ↦ (base (r k)).head?) = true
      rw [hheads]
      exact htest
    have hs := StackProg.Exec.branchTrue (test := fun h : L → Option A ↦ test (fun k ↦ h (r k)))
      (p := liftProg r p) (q := liftProg r q) hcond (ih base hb)
    simpa only [liftProg] using hs
  | @branchFalse test p q s t n htest hq ih =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = false := by
      change test (fun k ↦ (base (r k)).head?) = false
      rw [hheads]
      exact htest
    have hs := StackProg.Exec.branchFalse (test := fun h : L → Option A ↦ test (fun k ↦ h (r k)))
      (p := liftProg r p) (q := liftProg r q) hcond (ih base hb)
    simpa only [liftProg] using hs
  | @loopFalse test p s htest =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = false := by
      change test (fun k ↦ (base (r k)).head?) = false
      rw [hheads]
      exact htest
    have heq : write r s base = base := by
      rw [← hb]
      exact write_project r base
    have hs := StackProg.Exec.loopFalse (test := fun h : L → Option A ↦ test (fun k ↦ h (r k)))
      (p := liftProg r p) (s := base) hcond
    simpa only [liftProg, heq] using hs
  | @loopTrue test p s t u n m htest hp hloop ihp ihloop =>
    intro base hb
    have hheads := projected_heads r base s hb
    have hcond : (fun h ↦ test (fun k ↦ h (r k))) (fun l ↦ (base l).head?) = true := by
      change test (fun k ↦ (base (r k)).head?) = true
      rw [hheads]
      exact htest
    have h1 := ihp base hb
    have h2 : (StackProg.loop (fun h : L → Option A ↦ test (fun k ↦ h (r k)))
        (liftProg r p)).Exec (write r t base) (write r u (write r t base)) m := by
      simpa only [liftProg] using ihloop (write r t base) (project_write r t base)
    have hs := StackProg.Exec.loopTrue
      (test := fun h : L → Option A ↦ test (fun k ↦ h (r k))) (p := liftProg r p) hcond h1 h2
    rw [write_overwrite] at hs
    simpa only [liftProg] using hs

/-- Port lifting leaves every stack outside the embedding unchanged. -/
theorem lift_exec_preserves_other_ports {K L A : Type} (r : K ↪ L) {p : StackProg K A}
    {s t : K → List A} {n : ℕ} (h : p.Exec s t n) (base : L → List A)
    (hb : project r base = s) {l : L} (hout : ∀ k, r k ≠ l) :
    (liftProg r p).Exec base (write r t base) n ∧ write r t base l = base l :=
  ⟨lift_exec r h base hb, write_outside r t base hout⟩



/-- Compose source programs with different local port types on one shared
    global store. The compatibility hypothesis states the exact second
    program input after the first program writes its embedded ports. -/
theorem lift_seq_exec {K J L A : Type} (r : K ↪ L) (q : J ↪ L)
    {p : StackProg K A} {pIn pOut : K → List A} {np : ℕ} (hp : p.Exec pIn pOut np)
    {z : StackProg J A} {zIn zOut : J → List A} {nz : ℕ} (hz : z.Exec zIn zOut nz)
    (base : L → List A) (hbase : project r base = pIn)
    (hcompat : project q (write r pOut base) = zIn) :
    (StackProg.seq (liftProg r p) (liftProg q z)).Exec base
      (write q zOut (write r pOut base)) (np + 1 + nz) :=
  StackProg.Exec.seq (lift_exec r hp base hbase)
    (lift_exec q hz (write r pOut base) hcompat)

end StackProgPortLift
namespace StackProgPortLift

/-- Computable action lift when an explicit port decoder is supplied. -/
def liftActC {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (f : (K → Option A) → K → StackAct A) : (L → Option A) → L → StackAct A :=
  fun h l ↦ match decode l with
    | none => .keep
    | some k => f (fun j ↦ h (r j)) k

/-- Computable program lift when an explicit port decoder is supplied. -/
def liftProgC {K L A : Type} (r : K ↪ L) (decode : L → Option K) :
    StackProg K A → StackProg L A
  | .act f => .act (liftActC r decode f)
  | .seq p q => .seq (liftProgC r decode p) (liftProgC r decode q)
  | .branch test p q => .branch (fun h ↦ test (fun k ↦ h (r k))) (liftProgC r decode p) (liftProgC r decode q)
  | .loop test p => .loop (fun h ↦ test (fun k ↦ h (r k))) (liftProgC r decode p)

theorem liftActC_eq_liftAct {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (hdecode : ∀ l k, decode l = some k ↔ r k = l)
    (f : (K → Option A) → K → StackAct A) : liftActC r decode f = liftAct r f := by
  classical
  funext h l
  cases hd : decode l with
  | none =>
    have hn : ¬ ∃ k, r k = l := by
      rintro ⟨k, hk⟩
      have hs := (hdecode l k).2 hk
      rw [hd] at hs
      contradiction
    simp [liftActC, liftAct, hd, hn]
  | some k =>
    have hk : r k = l := (hdecode l k).1 hd
    subst l
    simp only [liftActC, hd, liftAct_at]

/-- A verified explicit decoder gives exactly the general mathematical lift. -/
theorem liftProgC_eq_liftProg {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (hdecode : ∀ l k, decode l = some k ↔ r k = l) (p : StackProg K A) :
    liftProgC r decode p = liftProg r p := by
  induction p with
  | act f => simp only [liftProgC, liftProg, liftActC_eq_liftAct r decode hdecode]
  | seq p q hp hq => simp only [liftProgC, liftProg, hp, hq]
  | branch test p q hp hq => simp only [liftProgC, liftProg, hp, hq]
  | loop test p hp => simp only [liftProgC, liftProg, hp]

end StackProgPortLift



open CookPvsNP ProjSchedTW.Complexity

namespace TensorBoundedUnaryAdd

/-- The four ports are source, destination, remaining capacity, and status. -/
private def store4 (src dst cap status : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then src else if k = 1 then dst else if k = 2 then cap else status

private def canTransfer (h : Fin 4 → Option BSym) : Bool :=
  (h 0).isSome && (h 2).isSome

private def transferAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .push .one else if k = 2 then .pop else .keep

/-- Transfer unary tokens until either the source or the fuel is exhausted. -/
def boundedTransferProg : StackProg (Fin 4) BSym := .loop canTransfer (.act transferAct)

private theorem transfer_step (n m d : ℕ) (status : List BSym) :
    StackProg.applyAct transferAct
      (store4 (List.replicate (n+1) .one) (List.replicate d .one)
        (List.replicate (m+1) .one) status) =
    store4 (List.replicate n .one) (List.replicate (d+1) .one)
      (List.replicate m .one) status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, transferAct, store4, StackAct.apply, List.replicate_succ]

/-- For any number k of available matching source and fuel tokens, the loop
    transfers exactly k provided one residual stack is empty. -/
theorem boundedTransfer_exec (k a b d : ℕ) (status : List BSym) (hstop : a = 0 ∨ b = 0) :
    boundedTransferProg.Exec
      (store4 (List.replicate (k+a) .one) (List.replicate d .one)
        (List.replicate (k+b) .one) status)
      (store4 (List.replicate a .one) (List.replicate (k+d) .one)
        (List.replicate b .one) status) (3*k+1) := by
  induction k generalizing d with
  | zero =>
    have ht : canTransfer (fun j ↦
        (store4 (List.replicate a .one) (List.replicate d .one)
          (List.replicate b .one) status j).head?) = false := by
      rcases hstop with rfl | rfl <;> simp [canTransfer, store4]
    simpa [boundedTransferProg] using
      (StackProg.Exec.loopFalse (test := canTransfer) (p := .act transferAct) ht)
  | succ k ih =>
    have ht : canTransfer (fun j ↦
        (store4 (List.replicate (k+a+1) .one) (List.replicate d .one)
          (List.replicate (k+b+1) .one) status j).head?) = true := by
      simp [canTransfer, store4, List.replicate_succ]
    have ha : (StackProg.act transferAct).Exec
        (store4 (List.replicate (k+a+1) .one) (List.replicate d .one)
          (List.replicate (k+b+1) .one) status)
        (store4 (List.replicate (k+a) .one) (List.replicate (d+1) .one)
          (List.replicate (k+b) .one) status) 1 := by
      simpa only [transfer_step] using
        (StackProg.Exec.act transferAct
          (store4 (List.replicate (k+a+1) .one) (List.replicate d .one)
            (List.replicate (k+b+1) .one) status))
    have h := StackProg.Exec.loopTrue ht ha (ih (d+1))
    have hsrc : (k+1)+a = k+a+1 := by omega
    have hcap : (k+1)+b = k+b+1 := by omega
    have hdst : k+(d+1) = (k+1)+d := by omega
    have htime : 1+1+1+(3*k+1) = 3*(k+1)+1 := by omega
    change (StackProg.loop canTransfer (.act transferAct)).Exec
      (store4 (List.replicate ((k+1)+a) .one) (List.replicate d .one)
        (List.replicate ((k+1)+b) .one) status)
      (store4 (List.replicate a .one) (List.replicate ((k+1)+d) .one)
        (List.replicate b .one) status) (3*(k+1)+1)
    rw [hsrc, hcap, ← hdst, ← htime]
    exact h

/-- With sufficient capacity, all source tokens are added to the destination. -/
theorem boundedTransfer_success (n spare d : ℕ) (status : List BSym) :
    boundedTransferProg.Exec
      (store4 (List.replicate n .one) (List.replicate d .one)
        (List.replicate (n+spare) .one) status)
      (store4 [] (List.replicate (n+d) .one) (List.replicate spare .one) status)
      (3*n+1) := by
  simpa using boundedTransfer_exec n 0 spare d status (Or.inl rfl)

/-- When capacity runs out first, the loop stops with a nonempty source.
    This residual source is an explicit over-cap signal for the next branch. -/
theorem boundedTransfer_exhausted (fuel extra d : ℕ) (status : List BSym) :
    boundedTransferProg.Exec
      (store4 (List.replicate (fuel+(extra+1)) .one) (List.replicate d .one)
        (List.replicate fuel .one) status)
      (store4 (List.replicate (extra+1) .one) (List.replicate (fuel+d) .one) [] status)
      (3*fuel+1) := by
  simpa using boundedTransfer_exec fuel (extra+1) 0 d status (Or.inr rfl)

end TensorBoundedUnaryAdd

namespace TensorBoundedDouble

open StackProgPortLift TensorBoundedUnaryAdd

/-- Source number, temporary copy, remaining fuel, scratch, status. -/
def store5 (src copy fuel scratch status : List BSym) : Fin 5 → List BSym :=
  fun k ↦ if k = 0 then src else if k = 1 then copy else if k = 2 then fuel
    else if k = 3 then scratch else status

def addPorts : Fin 4 ↪ Fin 5 := ⟨![1, 0, 2, 4], by decide⟩
def addDecode : Fin 5 → Option (Fin 4) := ![some 1, some 0, some 2, none, some 3]

private theorem addDecode_correct (l : Fin 5) (k : Fin 4) :
    addDecode l = some k ↔ addPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

/-- Copy the number, then spend one unit of fuel per added unary token. -/
def boundedDoubleProg : StackProg (Fin 5) BSym :=
  .seq (copyProg 0 1 3) (liftProgC addPorts addDecode boundedTransferProg)

/-- When the fuel contains n+spare tokens, double n within that cap. -/
theorem boundedDouble_success (n spare : ℕ) (status : List BSym) :
    boundedDoubleProg.Exec
      (store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (write addPorts
        (TensorBoundedUnaryAdd.store4 [] (List.replicate (n+n) .one)
          (List.replicate spare .one) status)
        (store5 (List.replicate n .one) (List.replicate n .one)
          (List.replicate (n+spare) .one) [] status)) (9*n+5) := by
  classical
  let s := store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status
  let m := store5 (List.replicate n .one) (List.replicate n .one)
    (List.replicate (n+spare) .one) [] status
  have he : s 3 = [] := by simp [s, store5]
  have hmid : Function.update s 1 (s 0 ++ s 1) = m := by
    funext k
    fin_cases k <;> simp [s, m, store5, Function.update]
  have hc : (copyProg (0 : Fin 5) 1 3).Exec s m (6*n+3) := by
    have h := stack_copy (0 : Fin 5) 1 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store5] using h
  have hproject : project addPorts m =
      TensorBoundedUnaryAdd.store4 (List.replicate n .one) (List.replicate n .one)
        (List.replicate (n+spare) .one) status := by
    funext k
    fin_cases k <;> simp [project, addPorts, m, store5, TensorBoundedUnaryAdd.store4]
  have ha := lift_exec addPorts (boundedTransfer_success n spare n status) m hproject
  have h := StackProg.Exec.seq hc ha
  have htime : (6*n+3)+1+(3*n+1) = 9*n+5 := by omega
  rw [← htime]
  simpa only [boundedDoubleProg, liftProgC_eq_liftProg addPorts addDecode addDecode_correct,
    s, m] using h

/-- With fewer than n fuel tokens, doubling stops as soon as the budget is
    empty and leaves a nonempty copy as an explicit over-cap signal. -/
theorem boundedDouble_exhausted (fuel extra : ℕ) (status : List BSym) :
    boundedDoubleProg.Exec
      (store5 (List.replicate (fuel+(extra+1)) .one) [] (List.replicate fuel .one) [] status)
      (write addPorts
        (TensorBoundedUnaryAdd.store4 (List.replicate (extra+1) .one)
          (List.replicate (fuel+(fuel+(extra+1))) .one) [] status)
        (store5 (List.replicate (fuel+(extra+1)) .one)
          (List.replicate (fuel+(extra+1)) .one) (List.replicate fuel .one) [] status))
      ((6*(fuel+(extra+1))+3)+1+(3*fuel+1)) := by
  classical
  let n := fuel+(extra+1)
  let s := store5 (List.replicate n .one) [] (List.replicate fuel .one) [] status
  let m := store5 (List.replicate n .one) (List.replicate n .one)
    (List.replicate fuel .one) [] status
  have he : s 3 = [] := by simp [s, store5]
  have hmid : Function.update s 1 (s 0 ++ s 1) = m := by
    funext k
    fin_cases k <;> simp [s, m, store5, Function.update]
  have hc : (copyProg (0 : Fin 5) 1 3).Exec s m (6*n+3) := by
    have h := stack_copy (0 : Fin 5) 1 3 (by decide) (by decide) (by decide) s he
    rw [hmid] at h
    simpa [s, store5] using h
  have hproject : project addPorts m =
      TensorBoundedUnaryAdd.store4 (List.replicate (fuel+(extra+1)) .one) (List.replicate n .one)
        (List.replicate fuel .one) status := by
    funext k
    fin_cases k <;> simp [project, addPorts, m, n, store5, TensorBoundedUnaryAdd.store4]
  have ha := lift_exec addPorts (boundedTransfer_exhausted fuel extra n status) m hproject
  have h := StackProg.Exec.seq hc ha
  simpa only [boundedDoubleProg, liftProgC_eq_liftProg addPorts addDecode addDecode_correct,
    s, m, n] using h

end TensorBoundedDouble


open CookPvsNP ProjSchedTW.Complexity

namespace TensorBoundedBit

/-- Remaining binary digits, unary value, remaining unary fuel, status. -/
private def store4 (bits value fuel status : List BSym) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then bits else if k = 1 then value else if k = 2 then fuel else status

private def isZero (h : Fin 4 → Option BSym) : Bool := h 0 == some BSym.zero
private def isOne (h : Fin 4 → Option BSym) : Bool := h 0 == some BSym.one
private def hasFuel (h : Fin 4 → Option BSym) : Bool := h 2 == some BSym.one

private def zeroAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else .keep
private def oneAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then .push .one else if k = 2 then .pop else .keep
private def rejectAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push .zero else .keep

/-- Read one bit, spending one fuel token if the bit is one; mark exhaustion
    and all non-bit heads as failures. -/
def boundedBitProg : StackProg (Fin 4) BSym :=
  .branch isZero (.act zeroAct)
    (.branch isOne (.branch hasFuel (.act oneAct) (.act rejectAct)) (.act rejectAct))

private theorem zero_step (tail value fuel status : List BSym) :
    StackProg.applyAct zeroAct (store4 (.zero :: tail) value fuel status) =
      store4 tail value fuel status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, zeroAct, store4, StackAct.apply]

private theorem one_step (tail value fuel status : List BSym) :
    StackProg.applyAct oneAct (store4 (.one :: tail) value (.one :: fuel) status) =
      store4 tail (.one :: value) fuel status := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, oneAct, store4, StackAct.apply]

private theorem reject_step (bits value fuel status : List BSym) :
    StackProg.applyAct rejectAct (store4 bits value fuel status) =
      store4 bits value fuel (.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store4, StackAct.apply]

/-- A zero bit consumes no fuel and leaves the unary value unchanged. -/
theorem boundedBit_zero (tail value fuel status : List BSym) :
    boundedBitProg.Exec (store4 (.zero :: tail) value fuel status)
      (store4 tail value fuel status) 2 := by
  have ha : (StackProg.act zeroAct).Exec (store4 (.zero :: tail) value fuel status)
      (store4 tail value fuel status) 1 := by
    simpa only [zero_step] using (StackProg.Exec.act zeroAct (store4 (.zero :: tail) value fuel status))
  exact StackProg.Exec.branchTrue (by rfl) ha

/-- A one bit increments the value and spends exactly one fuel token. -/
theorem boundedBit_one (tail value fuel status : List BSym) :
    boundedBitProg.Exec (store4 (.one :: tail) value (.one :: fuel) status)
      (store4 tail (.one :: value) fuel status) 4 := by
  have ha : (StackProg.act oneAct).Exec (store4 (.one :: tail) value (.one :: fuel) status)
      (store4 tail (.one :: value) fuel status) 1 := by
    simpa only [one_step] using (StackProg.Exec.act oneAct (store4 (.one :: tail) value (.one :: fuel) status))
  have hf := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : hasFuel (fun k ↦ (store4 (.one :: tail) value (.one :: fuel) status k).head?) = true) ha
  have ho := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : isOne (fun k ↦ (store4 (.one :: tail) value (.one :: fuel) status k).head?) = true) hf
  exact StackProg.Exec.branchFalse (by rfl) ho

/-- A one bit with no fuel produces the failure marker without incrementing. -/
theorem boundedBit_exhausted (tail value status : List BSym) :
    boundedBitProg.Exec (store4 (.one :: tail) value [] status)
      (store4 (.one :: tail) value [] (.zero :: status)) 4 := by
  have ha : (StackProg.act rejectAct).Exec (store4 (.one :: tail) value [] status)
      (store4 (.one :: tail) value [] (.zero :: status)) 1 := by
    simpa only [reject_step] using (StackProg.Exec.act rejectAct (store4 (.one :: tail) value [] status))
  have hf := StackProg.Exec.branchFalse (p := .act oneAct)
    (by rfl : hasFuel (fun k ↦ (store4 (.one :: tail) value [] status k).head?) = false) ha
  have ho := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : isOne (fun k ↦ (store4 (.one :: tail) value [] status k).head?) = true) hf
  exact StackProg.Exec.branchFalse (by rfl) ho

end TensorBoundedBit

namespace TensorCappedDecode

open StackProgPortLift TensorBoundedDouble TensorBoundedBit

/-- Bits, unary value, doubling copy, remaining fuel, scratch and status. -/
def store6 (bits value copy fuel scratch status : List BSym) : Fin 6 → List BSym :=
  fun k ↦ if k = 0 then bits else if k = 1 then value else if k = 2 then copy
    else if k = 3 then fuel else if k = 4 then scratch else status

def doublePorts : Fin 5 ↪ Fin 6 := ⟨![1,2,3,4,5], by decide⟩
def doubleDecode : Fin 6 → Option (Fin 5) := ![none,some 0,some 1,some 2,some 3,some 4]
def bitPorts : Fin 4 ↪ Fin 6 := ⟨![0,1,3,5], by decide⟩
def bitDecode : Fin 6 → Option (Fin 4) := ![some 0,some 1,none,some 2,none,some 3]

private theorem doubleDecode_correct (l : Fin 6) (k : Fin 5) :
    doubleDecode l = some k ↔ doublePorts k = l := by
  fin_cases l <;> fin_cases k <;> decide
private theorem bitDecode_correct (l : Fin 6) (k : Fin 4) :
    bitDecode l = some k ↔ bitPorts k = l := by
  fin_cases l <;> fin_cases k <;> decide

private def copyEmpty (h : Fin 6 → Option BSym) : Bool := (h 2).isNone
private def rejectAct (_h : Fin 6 → Option BSym) (k : Fin 6) : StackAct BSym :=
  if k = 5 then .push .zero else .keep
private def shouldLoop (h : Fin 6 → Option BSym) : Bool :=
  (h 0).isSome && (h 5 == some BSym.one)

/-- Double under the fuel cap; only process the bit if doubling succeeded. -/
def cappedDigitProg : StackProg (Fin 6) BSym :=
  .seq (liftProgC doublePorts doubleDecode boundedDoubleProg)
    (.branch copyEmpty (liftProgC bitPorts bitDecode boundedBitProg) (.act rejectAct))

/-- Process digits until the input is exhausted or a failure marker is set. -/
def cappedDecodeProg : StackProg (Fin 6) BSym := .loop shouldLoop cappedDigitProg

private theorem write_add (a b c d x y z t u : List BSym) :
    write TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
      (TensorBoundedDouble.store5 x y z t u) = TensorBoundedDouble.store5 b a c t d := by
  funext k
  fin_cases k
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (1 : Fin 4))
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (0 : Fin 4))
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (2 : Fin 4))
  · have ho : ∀ j : Fin 4, TensorBoundedDouble.addPorts j ≠ (3 : Fin 5) := by
      intro j; fin_cases j <;> decide
    simpa [TensorBoundedDouble.store5] using
      (StackProgPortLift.write_outside TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) ho)
  · simpa [TensorBoundedDouble.addPorts, TensorBoundedUnaryAdd.store4, TensorBoundedDouble.store5] using
      (StackProgPortLift.write_at TensorBoundedDouble.addPorts (TensorBoundedUnaryAdd.store4 a b c d)
        (TensorBoundedDouble.store5 x y z t u) (3 : Fin 4))

private theorem write_double (a b c d e i v q f t s : List BSym) :
    write doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) =
      store6 i a b c d e := by
  funext k
  fin_cases k
  · have ho : ∀ j : Fin 5, doublePorts j ≠ (0 : Fin 6) := by
      intro j; fin_cases j <;> decide
    simpa [store6] using
      (StackProgPortLift.write_outside doublePorts (TensorBoundedDouble.store5 a b c d e)
        (store6 i v q f t s) ho)
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (0 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (1 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (2 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (3 : Fin 5))
  · simpa [doublePorts, TensorBoundedDouble.store5, store6] using
      (StackProgPortLift.write_at doublePorts (TensorBoundedDouble.store5 a b c d e) (store6 i v q f t s) (4 : Fin 5))

private theorem write_bit (a b c d i v q f t s : List BSym) :
    write bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) =
      store6 a b q c t d := by
  funext k
  fin_cases k
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (0 : Fin 4))
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (1 : Fin 4))
  · have ho : ∀ j : Fin 4, bitPorts j ≠ (2 : Fin 6) := by
      intro j; fin_cases j <;> decide
    simpa [store6] using (StackProgPortLift.write_outside bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) ho)
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (2 : Fin 4))
  · have ho : ∀ j : Fin 4, bitPorts j ≠ (4 : Fin 6) := by
      intro j; fin_cases j <;> decide
    simpa [store6] using (StackProgPortLift.write_outside bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) ho)
  · simpa [bitPorts, TensorBoundedBit.store4, store6] using
      (StackProgPortLift.write_at bitPorts (TensorBoundedBit.store4 a b c d) (store6 i v q f t s) (3 : Fin 4))

private theorem reject_step (bits value copy fuel scratch status : List BSym) :
    StackProg.applyAct rejectAct (store6 bits value copy fuel scratch status) =
      store6 bits value copy fuel scratch (.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store6, StackAct.apply]

private theorem double_exec6 (bits a b c d e a' b' c' d' e' : List BSym) (steps : ℕ)
    (h : boundedDoubleProg.Exec (TensorBoundedDouble.store5 a b c d e)
      (TensorBoundedDouble.store5 a' b' c' d' e') steps) :
    (liftProgC doublePorts doubleDecode boundedDoubleProg).Exec
      (store6 bits a b c d e) (store6 bits a' b' c' d' e') steps := by
  have hp : project doublePorts (store6 bits a b c d e) = TensorBoundedDouble.store5 a b c d e := by
    funext k
    fin_cases k <;> simp [project, doublePorts, store6, TensorBoundedDouble.store5]
  have hr := lift_exec doublePorts h (store6 bits a b c d e) hp
  rw [write_double] at hr
  simpa only [liftProgC_eq_liftProg doublePorts doubleDecode doubleDecode_correct] using hr

private theorem bit_exec6 (bits value copy fuel scratch status bits' value' fuel' status' : List BSym)
    (steps : ℕ) (h : boundedBitProg.Exec (TensorBoundedBit.store4 bits value fuel status)
      (TensorBoundedBit.store4 bits' value' fuel' status') steps) :
    (liftProgC bitPorts bitDecode boundedBitProg).Exec
      (store6 bits value copy fuel scratch status) (store6 bits' value' copy fuel' scratch status') steps := by
  have hp : project bitPorts (store6 bits value copy fuel scratch status) =
      TensorBoundedBit.store4 bits value fuel status := by
    funext k
    fin_cases k <;> simp [project, bitPorts, store6, TensorBoundedBit.store4]
  have hr := lift_exec bitPorts h (store6 bits value copy fuel scratch status) hp
  rw [write_bit] at hr
  simpa only [liftProgC_eq_liftProg bitPorts bitDecode bitDecode_correct] using hr

/-- With spare fuel, processing a zero digit doubles the unary value. -/
theorem cappedDigit_zero (tail : List BSym) (n spare : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 (.zero :: tail) (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (store6 tail (List.replicate (n+n) .one) [] (List.replicate spare .one) [] status)
      (9*n+9) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] (List.replicate spare .one) [] status)
      (9*n+5) := by simpa only [write_add] using boundedDouble_success n spare status
  have hd := double_exec6 (.zero :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hb := bit_exec6 (.zero :: tail) (List.replicate (n+n) .one) []
    (List.replicate spare .one) [] status tail (List.replicate (n+n) .one)
    (List.replicate spare .one) status 2 (boundedBit_zero tail _ _ status)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (.zero :: tail) (List.replicate (n+n) .one) []
      (List.replicate spare .one) [] status k).head?) = true) hb
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+2) = 9*n+9 := by omega
  rw [← ht]
  exact he

/-- With one extra fuel token, a one digit doubles and increments. -/
theorem cappedDigit_one (tail : List BSym) (n spare : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 (.one :: tail) (List.replicate n .one) [] (List.replicate (n+(spare+1)) .one) [] status)
      (store6 tail (List.replicate (n+n+1) .one) [] (List.replicate spare .one) [] status)
      (9*n+11) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+(spare+1)) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] (List.replicate (spare+1) .one) [] status)
      (9*n+5) := by simpa only [write_add] using boundedDouble_success n (spare+1) status
  have hd := double_exec6 (.one :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hb := bit_exec6 (.one :: tail) (List.replicate (n+n) .one) []
    (BSym.one :: List.replicate spare .one) [] status tail
    (BSym.one :: List.replicate (n+n) .one) (List.replicate spare .one) status 4
    (boundedBit_one tail _ _ status)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (.one :: tail) (List.replicate (n+n) .one) []
      (List.replicate (spare+1) .one) [] status k).head?) = true) (by
        simpa only [List.replicate_succ] using hb)
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+4) = 9*n+11 := by omega
  rw [← ht]
  simpa only [cappedDigitProg, List.replicate_succ] using he

/-- If doubling fits but the one digit cannot be added, mark exhaustion. -/
theorem cappedDigit_one_exhausted (tail : List BSym) (n : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 (.one :: tail) (List.replicate n .one) [] (List.replicate n .one) [] status)
      (store6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] (.zero :: status))
      (9*n+11) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+0) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] [] [] status) (9*n+5) := by
    simpa only [write_add, List.replicate_zero] using boundedDouble_success n 0 status
  have hd := double_exec6 (.one :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hb := bit_exec6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] status
    (.one :: tail) (List.replicate (n+n) .one) [] (.zero :: status) 4
    (boundedBit_exhausted tail _ status)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] status k).head?) = true) hb
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+4) = 9*n+11 := by omega
  rw [← ht]
  simpa only [cappedDigitProg, Nat.add_zero] using he

/-- If doubling exhausts fuel, set failure before attempting the bit. -/
theorem cappedDigit_double_exhausted (bits : List BSym) (fuel extra : ℕ) (status : List BSym) :
    cappedDigitProg.Exec
      (store6 bits (List.replicate (fuel+(extra+1)) .one) [] (List.replicate fuel .one) [] status)
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one)
        (List.replicate (extra+1) .one) [] [] (.zero :: status))
      (((6*(fuel+(extra+1))+3)+1+(3*fuel+1))+1+2) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate (fuel+(extra+1)) .one) [] (List.replicate fuel .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (fuel+(fuel+(extra+1))) .one)
        (List.replicate (extra+1) .one) [] [] status)
      ((6*(fuel+(extra+1))+3)+1+(3*fuel+1)) := by
    simpa only [write_add] using boundedDouble_exhausted fuel extra status
  have hd := double_exec6 bits _ _ _ _ _ _ _ _ _ _ _ hd0
  have ha : (StackProg.act rejectAct).Exec
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one) (List.replicate (extra+1) .one) [] [] status)
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one) (List.replicate (extra+1) .one) [] [] (.zero :: status)) 1 := by
    simpa only [reject_step] using StackProg.Exec.act rejectAct
      (store6 bits (List.replicate (fuel+(fuel+(extra+1))) .one) (List.replicate (extra+1) .one) [] [] status)
  have hc := StackProg.Exec.branchFalse (test := copyEmpty) (p := liftProgC bitPorts bitDecode boundedBitProg)
    (by simp [copyEmpty, store6, List.replicate_succ]) ha
  exact StackProg.Exec.seq hd hc

private theorem boundedBit_bad (a : BSym) (tail value fuel status : List BSym)
    (hz : TensorBoundedBit.isZero (fun k ↦ (TensorBoundedBit.store4 (a :: tail) value fuel status k).head?) = false)
    (ho : TensorBoundedBit.isOne (fun k ↦ (TensorBoundedBit.store4 (a :: tail) value fuel status k).head?) = false) :
    boundedBitProg.Exec (TensorBoundedBit.store4 (a :: tail) value fuel status)
      (TensorBoundedBit.store4 (a :: tail) value fuel (.zero :: status)) 3 := by
  have ha : (StackProg.act TensorBoundedBit.rejectAct).Exec
      (TensorBoundedBit.store4 (a :: tail) value fuel status)
      (TensorBoundedBit.store4 (a :: tail) value fuel (.zero :: status)) 1 := by
    simpa only [TensorBoundedBit.reject_step] using
      StackProg.Exec.act TensorBoundedBit.rejectAct (TensorBoundedBit.store4 (a :: tail) value fuel status)
  have hb := StackProg.Exec.branchFalse (p := .branch TensorBoundedBit.hasFuel
    (.act TensorBoundedBit.oneAct) (.act TensorBoundedBit.rejectAct)) ho ha
  exact StackProg.Exec.branchFalse hz hb

/-- A non-binary digit marks failure after the bounded doubling stage. -/
theorem cappedDigit_bad (a : BSym) (tail : List BSym) (n spare : ℕ) (status : List BSym)
    (hz : a ≠ .zero) (ho : a ≠ .one) :
    cappedDigitProg.Exec
      (store6 (a :: tail) (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (store6 (a :: tail) (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.zero :: status))
      (9*n+10) := by
  have hd0 : boundedDoubleProg.Exec
      (TensorBoundedDouble.store5 (List.replicate n .one) [] (List.replicate (n+spare) .one) [] status)
      (TensorBoundedDouble.store5 (List.replicate (n+n) .one) [] (List.replicate spare .one) [] status)
      (9*n+5) := by simpa only [write_add] using boundedDouble_success n spare status
  have hd := double_exec6 (a :: tail) _ _ _ _ _ _ _ _ _ _ _ hd0
  have hzero : TensorBoundedBit.isZero (fun k ↦
      (TensorBoundedBit.store4 (a :: tail) (List.replicate (n+n) .one) (List.replicate spare .one) status k).head?) = false := by
    simp [TensorBoundedBit.isZero, TensorBoundedBit.store4, hz]
  have hone : TensorBoundedBit.isOne (fun k ↦
      (TensorBoundedBit.store4 (a :: tail) (List.replicate (n+n) .one) (List.replicate spare .one) status k).head?) = false := by
    simp [TensorBoundedBit.isOne, TensorBoundedBit.store4, ho]
  have hb := bit_exec6 (a :: tail) (List.replicate (n+n) .one) []
    (List.replicate spare .one) [] status (a :: tail) (List.replicate (n+n) .one)
    (List.replicate spare .one) (.zero :: status) 3 (boundedBit_bad a tail _ _ status hzero hone)
  have hc := StackProg.Exec.branchTrue (q := .act rejectAct)
    (by rfl : copyEmpty (fun k ↦ (store6 (a :: tail) (List.replicate (n+n) .one) []
      (List.replicate spare .one) [] status k).head?) = true) hb
  have he := StackProg.Exec.seq hd hc
  have ht : (9*n+5)+1+(1+3) = 9*n+10 := by omega
  rw [← ht]
  exact he

/-- Interpret a digit as the usual big-endian doubling-and-increment step. -/
def digitValue (n : ℕ) (a : BSym) : ℕ := n+n + if a = .one then 1 else 0

/-- Every single capped digit either consumes one bit while preserving the
    value-plus-fuel invariant, or records failure without exceeding the cap. -/
theorem cappedDigit_progress (a : BSym) (tail : List BSym) (n fuel : ℕ) (status : List BSym) :
    ∃ out steps,
      cappedDigitProg.Exec
        (store6 (a :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status)) out steps ∧
      steps ≤ 9*(n+fuel)+11 ∧
      ((∃ n' fuel', out = store6 tail (List.replicate n' .one) [] (List.replicate fuel' .one) [] (.one :: status) ∧
          n'+fuel'=n+fuel ∧ n' = digitValue n a) ∨
       (∃ bits' value' copy' fuel' scratch',
          out = store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status))) := by
  by_cases hle : n ≤ fuel
  · let spare := fuel-n
    have hf : fuel = n+spare := by dsimp [spare]; omega
    by_cases hz : a = .zero
    · subst a
      refine ⟨store6 tail (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.one :: status),
        9*n+9, ?_, by omega, Or.inl ⟨n+n, spare, rfl, ?_, ?_⟩⟩
      · simpa only [hf] using cappedDigit_zero tail n spare (.one :: status)
      · omega
      · simp [digitValue]
    · by_cases ho : a = .one
      · subst a
        cases hs : spare with
        | zero =>
          have hf0 : fuel = n := by rw [hs] at hf; omega
          refine ⟨store6 (.one :: tail) (List.replicate (n+n) .one) [] [] [] (.zero :: .one :: status),
            9*n+11, ?_, by omega, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
          simpa only [hf0] using cappedDigit_one_exhausted tail n (.one :: status)
        | succ spare =>
          have hf1 : fuel = n+(spare+1) := by rw [hs] at hf; omega
          refine ⟨store6 tail (List.replicate (n+n+1) .one) [] (List.replicate spare .one) [] (.one :: status),
            9*n+11, ?_, by omega, Or.inl ⟨n+n+1, spare, rfl, ?_, ?_⟩⟩
          · simpa only [hf1] using cappedDigit_one tail n spare (.one :: status)
          · omega
          · simp [digitValue]
      · refine ⟨store6 (a :: tail) (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.zero :: .one :: status),
          9*n+10, ?_, by omega, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
        simpa only [hf] using cappedDigit_bad a tail n spare (.one :: status) hz ho
  · let extra := n-fuel-1
    have hn : n = fuel+(extra+1) := by dsimp [extra]; omega
    refine ⟨store6 (a :: tail) (List.replicate (fuel+(fuel+(extra+1))) .one)
        (List.replicate (extra+1) .one) [] [] (.zero :: .one :: status),
      ((6*(fuel+(extra+1))+3)+1+(3*fuel+1))+1+2, ?_, ?_, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
    · simpa only [hn] using cappedDigit_double_exhausted (a :: tail) fuel extra (.one :: status)
    · omega

/-- The whole capped digit loop terminates on every symbol list. It either
    consumes all digits while preserving the cap invariant, or stops with a
    failure marker; its cost is bounded by the product of digit count and cap. -/
theorem cappedDecode_total (bits : List BSym) (n fuel : ℕ) (status : List BSym) :
    ∃ out steps,
      cappedDecodeProg.Exec
        (store6 bits (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status)) out steps ∧
      steps ≤ (9*(n+fuel)+15)*bits.length+1 ∧
      ((∃ n' fuel', out = store6 [] (List.replicate n' .one) [] (List.replicate fuel' .one) [] (.one :: status) ∧
          n'+fuel'=n+fuel ∧ n' = bits.foldl digitValue n) ∨
       (∃ bits' value' copy' fuel' scratch',
          out = store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status))) := by
  induction bits generalizing n fuel with
  | nil =>
    refine ⟨store6 [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status),
      1, ?_, by simp, Or.inl ⟨n, fuel, rfl, rfl, rfl⟩⟩
    exact StackProg.Exec.loopFalse (by rfl)
  | cons a tail ih =>
    have ht : shouldLoop (fun k ↦
        (store6 (a :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status) k).head?) = true := by rfl
    obtain ⟨mid, cost, hdigit, hcost, hresult⟩ := cappedDigit_progress a tail n fuel status
    rcases hresult with ⟨n', fuel', rfl, hsum, hvalueStep⟩ | ⟨bits', value', copy', fuel', scratch', rfl⟩
    · obtain ⟨out, steps, hloop, hsteps, hout⟩ := ih n' fuel'
      have he := StackProg.Exec.loopTrue ht hdigit hloop
      refine ⟨out, 1+cost+1+steps, he, ?_, ?_⟩
      · rw [hsum] at hsteps
        simp only [List.length_cons, Nat.mul_succ]
        omega
      · rcases hout with ⟨n'', fuel'', rfl, hsum', hvalue⟩ | hfail
        · left
          refine ⟨n'', fuel'', rfl, ?_, ?_⟩
          · omega
          · simp only [List.foldl_cons]
            rw [← hvalueStep]
            exact hvalue
        · exact Or.inr hfail
    · have htstop : shouldLoop (fun k ↦
          (store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status) k).head?) = false := by
        simp [shouldLoop, store6]
      have hstop : cappedDecodeProg.Exec
          (store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status))
          (store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status)) 1 := by
        exact StackProg.Exec.loopFalse htstop
      have he := StackProg.Exec.loopTrue ht hdigit hstop
      refine ⟨store6 bits' value' copy' fuel' scratch' (.zero :: .one :: status),
        1+cost+1+1, he, ?_, Or.inr ⟨_, _, _, _, _, rfl⟩⟩
      simp only [List.length_cons, Nat.mul_succ]
      have hnonneg : 0 ≤ (9*(n+fuel)+15)*tail.length := Nat.zero_le _
      omega

private theorem digitValue_ge (n : ℕ) (a : BSym) : n ≤ digitValue n a := by
  simp only [digitValue]
  split <;> omega

private theorem digitFold_ge (bits : List BSym) (n : ℕ) : n ≤ bits.foldl digitValue n := by
  induction bits generalizing n with
  | nil => rfl
  | cons a tail ih =>
    exact le_trans (digitValue_ge n a) (ih (digitValue n a))

/-- A valid binary stream whose completed value fits the initial unary cap is
    never spuriously rejected. The final unary value and unused fuel are exact. -/
theorem cappedDecode_valid (bits : List BSym) (n fuel : ℕ) (status : List BSym)
    (hbits : ∀ a ∈ bits, a = .zero ∨ a = .one)
    (hcap : bits.foldl digitValue n ≤ n+fuel) :
    ∃ steps,
      cappedDecodeProg.Exec
        (store6 bits (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status))
        (store6 [] (List.replicate (bits.foldl digitValue n) .one) []
          (List.replicate (n+fuel-bits.foldl digitValue n) .one) [] (.one :: status)) steps ∧
      steps ≤ (9*(n+fuel)+15)*bits.length+1 := by
  induction bits generalizing n fuel with
  | nil =>
    refine ⟨1, ?_, by simp⟩
    simpa [cappedDecodeProg] using
      (StackProg.Exec.loopFalse (test := shouldLoop) (p := cappedDigitProg)
      (s := store6 [] (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status)) (by rfl))
  | cons a tail ih =>
    have htailbits : ∀ b ∈ tail, b = .zero ∨ b = .one := by
      intro b hb
      exact hbits b (by simp [hb])
    have ha := hbits a (by simp)
    have hnext : digitValue n a ≤ (a :: tail).foldl digitValue n := by
      exact digitFold_ge tail (digitValue n a)
    have ht : shouldLoop (fun k ↦
        (store6 (a :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status) k).head?) = true := by rfl
    rcases ha with rfl | rfl
    · let spare := fuel-n
      have hf : fuel = n+spare := by
        dsimp [spare]
        simp only [digitValue, reduceCtorEq, ↓reduceIte, Nat.add_zero] at hnext
        omega
      have hsum : n+n+spare = n+fuel := by omega
      have htailcap : tail.foldl digitValue (n+n) ≤ n+n+spare := by
        simp only [List.foldl_cons, digitValue, reduceCtorEq, ↓reduceIte, Nat.add_zero] at hcap
        omega
      obtain ⟨steps, hr, hsteps⟩ := ih (n+n) spare htailbits htailcap
      have hd : cappedDigitProg.Exec
          (store6 (.zero :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status))
          (store6 tail (List.replicate (n+n) .one) [] (List.replicate spare .one) [] (.one :: status)) (9*n+9) := by
        simpa only [hf] using cappedDigit_zero tail n spare (.one :: status)
      have he := StackProg.Exec.loopTrue ht hd hr
      refine ⟨1+(9*n+9)+1+steps, ?_, ?_⟩
      · simpa only [cappedDecodeProg, List.foldl_cons, digitValue, reduceCtorEq, ↓reduceIte, Nat.add_zero, hsum] using he
      · rw [hsum] at hsteps
        simp only [List.length_cons, Nat.mul_succ]
        omega
    · let spare := fuel-n-1
      have hf : fuel = n+(spare+1) := by
        dsimp [spare]
        simp only [digitValue, ↓reduceIte] at hnext
        omega
      have hsum : n+n+1+spare = n+fuel := by omega
      have htailcap : tail.foldl digitValue (n+n+1) ≤ n+n+1+spare := by
        simp only [List.foldl_cons, digitValue, ↓reduceIte] at hcap
        omega
      obtain ⟨steps, hr, hsteps⟩ := ih (n+n+1) spare htailbits htailcap
      have hd : cappedDigitProg.Exec
          (store6 (.one :: tail) (List.replicate n .one) [] (List.replicate fuel .one) [] (.one :: status))
          (store6 tail (List.replicate (n+n+1) .one) [] (List.replicate spare .one) [] (.one :: status)) (9*n+11) := by
        simpa only [hf] using cappedDigit_one tail n spare (.one :: status)
      have he := StackProg.Exec.loopTrue ht hd hr
      refine ⟨1+(9*n+11)+1+steps, ?_, ?_⟩
      · simpa only [cappedDecodeProg, List.foldl_cons, digitValue, ↓reduceIte, hsum] using he
      · rw [hsum] at hsteps
        simp only [List.length_cons, Nat.mul_succ]
        omega

end TensorCappedDecode


namespace TensorCanonicalDigits

/-- Interpret little-endian Boolean digits as a natural number. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bitsValue bs)

/-- Every bit list ending in one is the canonical bit representation of its
    computed value. Thus checking the most significant bit suffices for
    canonicality once a nonempty binary block has been scanned. -/
theorem bitsValue_bits_append_true (pre : List Bool) :
    (bitsValue (pre ++ [true])).bits = pre ++ [true] := by
  induction pre with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    have hne : bitsValue (bs ++ [true]) ≠ 0 := by
      intro hz
      rw [hz, Nat.zero_bits] at ih
      have hcons : bs ++ [true] ≠ [] := by simp
      exact hcons ih.symm
    have hcanonical : bitsValue (bs ++ [true]) = 0 → b = true := by
      intro hz
      exact (hne hz).elim
    simpa [bitsValue, ih] using Nat.bits_append_bit (bitsValue (bs ++ [true])) b hcanonical

/-- Zero is represented by the empty block, and all other canonical bit lists
    end in one. -/
theorem nat_bits_canonical (n : ℕ) : n.bits = [] ∨ ∃ pre, n.bits = pre ++ [true] := by
  induction n using Nat.binaryRecFromOne with
  | zero => exact Or.inl (by simp)
  | one => exact Or.inr ⟨[], by simp⟩
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b (fun hz ↦ (hn hz).elim)]
    rcases ih with hempty | ⟨pre, hprefix⟩
    · have hn0 : n = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp [Nat.testBit_eq_inth, hempty]
      exact (hn hn0).elim
    · exact Or.inr ⟨b :: pre, by simp [hprefix]⟩

/-- The parser's mathematical canonicality condition is exact: an empty
    block or one ending in one is precisely a canonical `Nat.bits` block. -/
theorem canonical_digits_iff (digits : List Bool) :
    (digits = [] ∨ ∃ pre, digits = pre ++ [true]) ↔ ∃ n : ℕ, n.bits = digits := by
  constructor
  · intro h
    rcases h with rfl | ⟨pre, rfl⟩
    · exact ⟨0, by simp⟩
    · exact ⟨bitsValue (pre ++ [true]), bitsValue_bits_append_true pre⟩
  · rintro ⟨n, rfl⟩
    exact nat_bits_canonical n


/-- Reading the scanner's reversed Boolean digit stack from the top computes
    the little-endian number by the familiar accumulator update `2a+b`. -/
theorem bitsValue_reverse_fold (digits : List Bool) :
    digits.reverse.foldl (fun a bit ↦ 2 * a + bit.toNat) 0 = bitsValue digits := by
  induction digits with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, List.foldl_append, bitsValue, ih, Nat.bit_val]

/-- The mathematical bit decoder is a left inverse of the platform's
    canonical binary representation. -/
theorem bitsValue_nat_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hcanonical ih =>
    rw [Nat.bits_append_bit n b hcanonical]
    simp [bitsValue, ih]

open ProjSchedTW.Complexity

private def digitSym (b : Bool) : BSym := if b then .one else .zero
private def symValue (s : BSym) : ℕ := if s = .one then 1 else 0

/-- The exact symbol stack produced by the first-block scanner decodes to the
    original natural number by successive double-and-add operations. -/
theorem scanner_digits_reverse_fold (n : ℕ) :
    ((n.bits.map digitSym).reverse).foldl (fun a sym ↦ 2 * a + symValue sym) 0 = n := by
  rw [← List.map_reverse, List.foldl_map]
  have hstep : (fun (a : ℕ) (bit : Bool) ↦ 2 * a + symValue (digitSym bit)) =
      (fun (a : ℕ) (bit : Bool) ↦ 2 * a + bit.toNat) := by
    funext a bit
    cases bit <;> rfl
  rw [hstep, bitsValue_reverse_fold, bitsValue_nat_bits]

/-- Every double-and-add step is nondecreasing, so processing further bits
    cannot decrease the running value. -/
private theorem bit_fold_nondecreasing (digits : List Bool) (a : ℕ) :
    a ≤ digits.foldl (fun x bit ↦ 2 * x + bit.toNat) a := by
  induction digits generalizing a with
  | nil => simp
  | cons bit digits ih =>
    have hstep : a ≤ 2 * a + bit.toNat := by omega
    exact le_trans hstep (ih (2 * a + bit.toNat))

/-- Every intermediate value while reading the scanner's most-significant-bit
    first digit stack is at most the completed value n. Hence the early cap by
    the input length cannot reject a valid graph code, whose vertex count is
    already bounded by that length. -/
theorem reversed_bits_prefix_value_le (n k : ℕ) :
    ((n.bits.reverse.take k).foldl (fun x bit ↦ 2 * x + bit.toNat) 0) ≤ n := by
  let ds := n.bits.reverse
  have h := bit_fold_nondecreasing (ds.drop k) ((ds.take k).foldl (fun x bit ↦ 2 * x + bit.toNat) 0)
  rw [← List.foldl_append, List.take_append_drop] at h
  change ((n.bits.reverse.take k).foldl (fun x bit ↦ 2 * x + bit.toNat) 0) ≤
    n.bits.reverse.foldl (fun x bit ↦ 2 * x + bit.toNat) 0 at h
  rw [bitsValue_reverse_fold, bitsValue_nat_bits] at h
  exact h

end TensorCanonicalDigits

namespace TensorCappedDecode

open TensorCanonicalDigits

/-- The actual digit stack produced by the prefix parser for encNat n. -/
def scannerDigits (n : ℕ) : List BSym := (n.bits.map TensorCanonicalDigits.digitSym).reverse

private theorem scannerDigits_binary (n : ℕ) :
    ∀ a ∈ scannerDigits n, a = .zero ∨ a = .one := by
  intro a ha
  simp only [scannerDigits, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  cases b <;> simp [TensorCanonicalDigits.digitSym]

private theorem scannerDigits_fold (n : ℕ) : (scannerDigits n).foldl digitValue 0 = n := by
  have heq : digitValue = (fun a s ↦ 2*a + TensorCanonicalDigits.symValue s) := by
    funext a s
    simp [digitValue, TensorCanonicalDigits.symValue]
    omega
  rw [heq]
  exact TensorCanonicalDigits.scanner_digits_reverse_fold n

/-- If n fits the input-length cap, the executable loop converts the exact
    parser-produced canonical digit stack to unary n without false rejection. -/
theorem cappedDecode_scannerDigits (n cap : ℕ) (status : List BSym) (hcap : n ≤ cap) :
    ∃ steps,
      cappedDecodeProg.Exec
        (store6 (scannerDigits n) [] [] (List.replicate cap .one) [] (.one :: status))
        (store6 [] (List.replicate n .one) [] (List.replicate (cap-n) .one) [] (.one :: status)) steps ∧
      steps ≤ (9*cap+15)*n.bits.length+1 := by
  have hc : (scannerDigits n).foldl digitValue 0 ≤ 0+cap := by
    simpa [scannerDigits_fold] using hcap
  obtain ⟨steps, hr, hb⟩ := cappedDecode_valid (scannerDigits n) 0 cap status (scannerDigits_binary n) hc
  refine ⟨steps, ?_, ?_⟩
  · simpa only [List.replicate_zero, Nat.zero_add, scannerDigits_fold] using hr
  · simpa [scannerDigits] using hb

end TensorCappedDecode


open CookPvsNP ProjSchedTW.Complexity

namespace TensorGraphPrefix3

/-- Three stacks hold unconsumed input, reversed digits, and status markers. -/
private def store (input acc status : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then acc else status

private def digitSym (b : Bool) : BSym := if b then .one else .zero

private def isDigit (o : Option BSym) : Bool :=
  match o with
  | some .zero | some .one => true
  | _ => false

private def digitTest (h : Fin 3 → Option BSym) : Bool := isDigit (h 0)
private def separatorTest (h : Fin 3 → Option BSym) : Bool := h 0 == some BSym.sep

private def readAct (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then
    match h 0 with
    | some .zero => .push .zero
    | some .one => .push .one
    | _ => .keep
  else .keep

private def acceptAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 2 then .push .one else .keep

private def rejectAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- A finite program that reads the first 0/1 block, consumes its separator
    on success, and pushes one status marker: one for a separator, zero for a
    missing separator or illegal next symbol. -/
def parseBlockProg : StackProg (Fin 3) BSym :=
  .seq (.loop digitTest (.act readAct))
    (.branch separatorTest (.act acceptAct) (.act rejectAct))

private theorem readAct_step (b : Bool) (rest acc status : List BSym) :
    StackProg.applyAct readAct (store (digitSym b :: rest) acc status) =
      store rest (digitSym b :: acc) status := by
  funext k
  fin_cases k <;> cases b <;>
    simp [StackProg.applyAct, readAct, store, digitSym, StackAct.apply]

private theorem acceptAct_step (tail acc status : List BSym) :
    StackProg.applyAct acceptAct (store (BSym.sep :: tail) acc status) =
      store tail acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, acceptAct, store, StackAct.apply]

private theorem rejectAct_step (rest acc status : List BSym) :
    StackProg.applyAct rejectAct (store rest acc status) =
      store rest acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store, StackAct.apply]

private theorem scan_exec (digits : List Bool) (stop acc status : List BSym)
    (hstop : isDigit stop.head? = false) :
    (StackProg.loop digitTest (.act readAct)).Exec
      (store (digits.map digitSym ++ stop) acc status)
      (store stop ((digits.map digitSym).reverse ++ acc) status)
      (3 * digits.length + 1) := by
  induction digits generalizing acc with
  | nil =>
    apply StackProg.Exec.loopFalse
    simpa [digitTest, store] using hstop
  | cons b digits ih =>
    have htest : digitTest (fun k ↦ (store (digitSym b ::
        (digits.map digitSym ++ stop)) acc status k).head?) = true := by
      cases b <;> rfl
    have hact : (StackProg.act readAct).Exec
        (store (digitSym b :: (digits.map digitSym ++ stop)) acc status)
        (store (digits.map digitSym ++ stop) (digitSym b :: acc) status) 1 := by
      rw [← readAct_step]
      exact StackProg.Exec.act _ _
    have hloop := StackProg.Exec.loopTrue htest hact (ih (digitSym b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop

/-- A terminated block is consumed and accepted, with exact cost 3d+4. -/
theorem parseBlockProg_success (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) acc status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.sep :: tail) acc status (by rfl)
  have hact : (StackProg.act acceptAct).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 1 := by
    rw [← acceptAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = true := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- A minus sign in place of the separator is rejected and left unconsumed. -/
theorem parseBlockProg_reject_minus (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) acc status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.minus :: tail) acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- End of input in place of the separator is rejected. -/
theorem parseBlockProg_reject_eof (digits : List Bool) (acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym) acc status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits [] acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store [] ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega


/-- A terminated block is canonical when it is empty or has most significant
    digit one; status zero from the first stage is always rejected. -/
private def canonicalTest (h : Fin 3 → Option BSym) : Bool :=
  (h 2 == some BSym.one) &&
    match h 1 with
    | none | some .one => true
    | _ => false

private def markTrueAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .one else .keep

private def markFalseAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- The delimiter parser followed by a finite-control canonicality check.
    The top status marker is one exactly on a terminated block that is empty
    or ends in one; the previous delimiter status is kept just below it. -/
def parseCanonicalBlockProg : StackProg (Fin 3) BSym :=
  .seq parseBlockProg (.branch canonicalTest (.act markTrueAct) (.act markFalseAct))

private theorem markTrue_step (input acc status : List BSym) :
    StackProg.applyAct markTrueAct (store input acc status) =
      store input acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markTrueAct, store, StackAct.apply]

private theorem markFalse_step (input acc status : List BSym) :
    StackProg.applyAct markFalseAct (store input acc status) =
      store input acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markFalseAct, store, StackAct.apply]

/-- Empty blocks and nonempty blocks ending in one are accepted and leave
    their reversed digits available for decoding. -/
theorem parseCanonicalBlockProg_accept (digits : List Bool) (tail status : List BSym)
    (hcanon : digits = [] ∨ ∃ pre, digits = pre ++ [true]) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = true := by
    rcases hcanon with rfl | ⟨pre, rfl⟩
    · rfl
    · simp [canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markTrueAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 1 := by
    simpa only [markTrue_step] using
      (StackProg.Exec.act markTrueAct (store tail (digits.map digitSym).reverse (BSym.one :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A nonempty block with most significant digit zero is rejected. -/
theorem parseCanonicalBlockProg_reject_high_zero (pre : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store ((pre ++ [false]).map digitSym ++ BSym.sep :: tail) [] status)
      (store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status))
      (3 * (pre ++ [false]).length + 7) := by
  let digits := pre ++ [false]
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = false := by
    simp [digits, canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markFalseAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 1 := by
    rw [← markFalse_step]
    exact StackProg.Exec.act _ _
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg, digits] <;> omega


/-- A minus sign where the delimiter is required remains rejected by the full
    two-stage parser, regardless of the scanned digit sequence. -/
theorem parseCanonicalBlockProg_reject_minus (digits : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_minus digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct
        (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A missing separator at end of input remains rejected by both stages. -/
theorem parseCanonicalBlockProg_reject_eof (digits : List Bool) (status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_eof digits [] status
  have ht : canonicalTest (fun k ↦
      (store [] (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct (store [] (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega


/-- Every Boolean block is empty, ends in one, or ends in zero. -/
private theorem digit_end_cases (digits : List Bool) :
    digits = [] ∨ (∃ pre, digits = pre ++ [true]) ∨ ∃ pre, digits = pre ++ [false] := by
  cases hr : digits.reverse with
  | nil =>
    left
    have h := congrArg List.reverse hr
    simpa using h
  | cons b pre =>
    have h : digits = pre.reverse ++ [b] := by
      have h' := congrArg List.reverse hr
      simpa using h'
    cases b with
    | false => exact Or.inr (Or.inr ⟨pre.reverse, h⟩)
    | true => exact Or.inr (Or.inl ⟨pre.reverse, h⟩)

/-- Every alphabet string decomposes into its maximal 0/1 prefix followed by
    a separator, a minus sign, or end of input. -/
private theorem split_digit_prefix (input : List BSym) :
    ∃ digits : List Bool, ∃ stop : List BSym,
      input = digits.map digitSym ++ stop ∧
        (stop = [] ∨ (∃ tail, stop = BSym.sep :: tail) ∨ ∃ tail, stop = BSym.minus :: tail) := by
  induction input with
  | nil => exact ⟨[], [], rfl, Or.inl rfl⟩
  | cons a input ih =>
    cases a with
    | zero =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨false :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | one =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨true :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | minus => exact ⟨[], BSym.minus :: input, by simp, Or.inr (Or.inr ⟨input, rfl⟩)⟩
    | sep => exact ⟨[], BSym.sep :: input, by simp, Or.inr (Or.inl ⟨input, rfl⟩)⟩

/-- The concrete canonical-block parser terminates on every input in linear
    stack-program time, including malformed input and end of input. -/
theorem parseCanonicalBlockProg_total (input status : List BSym) :
    ∃ out steps, parseCanonicalBlockProg.Exec (store input [] status) out steps ∧
      steps ≤ 3 * input.length + 7 := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3 * digits.length + 7 ≤ 3 * (digits.map digitSym ++ stop).length + 7 := by
    simp only [List.length_append, List.length_map]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status),
      3 * digits.length + 7, ?_, hbound⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · refine ⟨store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status),
        3 * digits.length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_accept digits tail status (Or.inl hempty)
    · refine ⟨store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status),
        3 * digits.length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩)
    · subst digits
      refine ⟨store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status),
        3 * (pre ++ [false]).length + 7, ?_, hbound⟩
      exact parseCanonicalBlockProg_reject_high_zero pre tail status
  · subst stop
    refine ⟨store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status),
      3 * digits.length + 7, ?_, hbound⟩
    exact parseCanonicalBlockProg_reject_minus digits tail status

/-- On every input, the parser terminates with at most one output digit for
    each input symbol, including malformed and truncated encodings. -/
theorem parseCanonicalBlockProg_total_length (input status : List BSym) :
    ∃ rest digits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest digits outstatus) steps ∧
      steps ≤ 3*input.length+7 ∧ digits.length ≤ input.length := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3*digits.length+7 ≤ 3*(digits.map digitSym ++ stop).length+7 := by
    simp only [List.length_append, List.length_map]
    omega
  have hlen : (digits.map digitSym).reverse.length ≤ (digits.map digitSym ++ stop).length := by
    simp only [List.length_reverse, List.length_map, List.length_append]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨[], (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, ?_, hbound, hlen⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status,
        3*digits.length+7, parseCanonicalBlockProg_accept digits tail status (Or.inl hempty), hbound, hlen⟩
    · exact ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status,
        3*digits.length+7, parseCanonicalBlockProg_accept digits tail status (Or.inr ⟨pre, htrue⟩), hbound, hlen⟩
    · subst digits
      exact ⟨tail, ((pre ++ [false]).map digitSym).reverse, .zero :: .one :: status,
        3*(pre ++ [false]).length+7, parseCanonicalBlockProg_reject_high_zero pre tail status, hbound, hlen⟩
  · subst stop
    exact ⟨.minus :: tail, (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, parseCanonicalBlockProg_reject_minus digits tail status, hbound, hlen⟩

end TensorGraphPrefix3

namespace TensorGraphPrefix3

/-- Actual canonical natural blocks are parsed into the MSB-first digit stack. -/
theorem parseCanonicalBlockProg_encNat (n : ℕ) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (encNat n ++ tail) [] status)
      (store tail (n.bits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3*n.bits.length+7) := by
  have hmap : (n.bits.map fun b ↦ if b then BSym.one else BSym.zero) = n.bits.map digitSym := by
    apply List.map_congr_left
    intro b hb
    cases b <;> rfl
  have hcode : encNat n ++ tail = n.bits.map digitSym ++ BSym.sep :: tail := by
    simp only [encNat, List.append_assoc, List.singleton_append, hmap]
  rw [hcode]
  exact parseCanonicalBlockProg_accept n.bits tail status (TensorCanonicalDigits.nat_bits_canonical n)

end TensorGraphPrefix3

namespace TensorPrefixDecode

open StackProgPortLift TensorGraphPrefix3 TensorCappedDecode

/-- Input remainder, digit stack, unary value, copy, fuel, scratch, status. -/
def store7 (input digits value copy fuel scratch status : List BSym) : Fin 7 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then digits else if k = 2 then value
    else if k = 3 then copy else if k = 4 then fuel else if k = 5 then scratch else status

def parsePorts : Fin 3 ↪ Fin 7 := ⟨![0,1,6], by decide⟩
def parseInverse : Fin 7 → Option (Fin 3) := ![some 0,some 1,none,none,none,none,some 2]
def decodePorts : Fin 6 ↪ Fin 7 := ⟨![1,2,3,4,5,6], by decide⟩
def decodeInverse : Fin 7 → Option (Fin 6) := ![none,some 0,some 1,some 2,some 3,some 4,some 5]

private theorem parseInverse_correct (l : Fin 7) (k : Fin 3) :
    parseInverse l = some k ↔ parsePorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem decodeInverse_correct (l : Fin 7) (k : Fin 6) :
    decodeInverse l = some k ↔ decodePorts k = l := by fin_cases l <;> fin_cases k <;> decide

private def accepted (h : Fin 7 → Option BSym) : Bool := h 6 == some BSym.one
private def keepAct (_h : Fin 7 → Option BSym) (_k : Fin 7) : StackAct BSym := .keep

/-- Parse a canonical first block; only then run its capped unary decoder. -/
def prefixDecodeProg : StackProg (Fin 7) BSym :=
  .seq (liftProgC parsePorts parseInverse parseCanonicalBlockProg)
    (.branch accepted (liftProgC decodePorts decodeInverse cappedDecodeProg) (.act keepAct))

private theorem write_parse (a b c i ds v cp f tmp st : List BSym) :
    write parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) =
      store7 a b v cp f tmp c := by
  funext k
  fin_cases k
  · simpa [parsePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) (0 : Fin 3))
  · simpa [parsePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) (1 : Fin 3))
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (2 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (3 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (4 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (5 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) ho)
  · simpa [parsePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at parsePorts (TensorGraphPrefix3.store a b c) (store7 i ds v cp f tmp st) (2 : Fin 3))

private theorem write_decode (a b c d e f i ds v cp fuel tmp st : List BSym) :
    write decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) =
      store7 i a b c d e f := by
  funext k
  fin_cases k
  · have ho : ∀ j : Fin 6, decodePorts j ≠ (0 : Fin 7) := by
      intro j; fin_cases j <;> decide
    simpa [store7] using (StackProgPortLift.write_outside decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) ho)
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (0 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (1 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (2 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (3 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (4 : Fin 6))
  · simpa [decodePorts, TensorGraphPrefix3.store, TensorCappedDecode.store6, store7] using
      (StackProgPortLift.write_at decodePorts (TensorCappedDecode.store6 a b c d e f) (store7 i ds v cp fuel tmp st) (5 : Fin 6))

private theorem parse_exec7 (i ds v cp f tmp st i' ds' st' : List BSym) (steps : ℕ)
    (h : parseCanonicalBlockProg.Exec (TensorGraphPrefix3.store i ds st)
      (TensorGraphPrefix3.store i' ds' st') steps) :
    (liftProgC parsePorts parseInverse parseCanonicalBlockProg).Exec
      (store7 i ds v cp f tmp st) (store7 i' ds' v cp f tmp st') steps := by
  have hp : project parsePorts (store7 i ds v cp f tmp st) = TensorGraphPrefix3.store i ds st := by
    funext k
    fin_cases k <;> simp [project, parsePorts, store7, TensorGraphPrefix3.store]
  have hr := lift_exec parsePorts h (store7 i ds v cp f tmp st) hp
  rw [write_parse] at hr
  simpa only [liftProgC_eq_liftProg parsePorts parseInverse parseInverse_correct] using hr

private theorem decode_exec7 (i ds v cp f tmp st : List BSym) (out : Fin 6 → List BSym) (steps : ℕ)
    (h : cappedDecodeProg.Exec (TensorCappedDecode.store6 ds v cp f tmp st) out steps) :
    (liftProgC decodePorts decodeInverse cappedDecodeProg).Exec
      (store7 i ds v cp f tmp st) (write decodePorts out (store7 i ds v cp f tmp st)) steps := by
  have hp : project decodePorts (store7 i ds v cp f tmp st) = TensorCappedDecode.store6 ds v cp f tmp st := by
    funext k
    fin_cases k <;> simp [project, decodePorts, store7, TensorCappedDecode.store6]
  have hr := lift_exec decodePorts h (store7 i ds v cp f tmp st) hp
  simpa only [liftProgC_eq_liftProg decodePorts decodeInverse decodeInverse_correct] using hr

private theorem keep_exec (s : Fin 7 → List BSym) : (StackProg.act keepAct).Exec s s 1 := by
  have heq : StackProg.applyAct keepAct s = s := by
    funext k
    simp [StackProg.applyAct, keepAct, StackAct.apply]
  simpa only [heq] using StackProg.Exec.act keepAct s

/-- The combined executable halts for every input and every cap. The parser
    bounds its digit output by input length, so decoding is polynomial even on
    malformed input. -/
theorem prefixDecode_total (input status : List BSym) (cap : ℕ) :
    ∃ out steps,
      prefixDecodeProg.Exec
        (store7 input [] [] [] (List.replicate cap .one) [] status) out steps ∧
      steps ≤ (9*cap+15)*input.length + 3*input.length + 10 := by
  obtain ⟨rest, digits, outstatus, psteps, hp, hpbound, hdlen⟩ :=
    parseCanonicalBlockProg_total_length input status
  have hparse := parse_exec7 input [] [] [] (List.replicate cap .one) [] status
    rest digits outstatus psteps hp
  by_cases hok : outstatus.head? = some BSym.one
  · have hshape : ∃ tail, outstatus = .one :: tail := by
      cases outstatus with
      | nil => simp at hok
      | cons a tail =>
        cases a <;> simp_all
    obtain ⟨tail, rfl⟩ := hshape
    obtain ⟨out, dsteps, hdecode, hdbound, _⟩ := cappedDecode_total digits 0 cap tail
    have hdecode7 := decode_exec7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail) out dsteps (by
      simpa using hdecode)
    have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail) k).head?) = true := by rfl
    have hb := StackProg.Exec.branchTrue (q := .act keepAct) ha hdecode7
    have he := StackProg.Exec.seq hparse hb
    refine ⟨write decodePorts out (store7 rest digits [] [] (List.replicate cap .one) [] (.one :: tail)),
      psteps+1+(1+dsteps), he, ?_⟩
    have hm := Nat.mul_le_mul_left (9*cap+15) hdlen
    simp only [Nat.zero_add] at hdbound
    omega
  · have ha : accepted (fun k ↦
        (store7 rest digits [] [] (List.replicate cap .one) [] outstatus k).head?) = false := by
      simp [accepted, store7, hok]
    have hb := StackProg.Exec.branchFalse (p := liftProgC decodePorts decodeInverse cappedDecodeProg)
      ha (keep_exec (store7 rest digits [] [] (List.replicate cap .one) [] outstatus))
    have he := StackProg.Exec.seq hparse hb
    refine ⟨store7 rest digits [] [] (List.replicate cap .one) [] outstatus,
      psteps+1+2, he, ?_⟩
    have hn : 0 ≤ (9*cap+15)*input.length := Nat.zero_le _
    omega

/-- Canonical encNat n is parsed and converted to unary n when it fits the cap;
    the unconsumed suffix and remaining fuel are preserved exactly. -/
theorem prefixDecode_encNat (n cap : ℕ) (tail status : List BSym) (hcap : n ≤ cap) :
    ∃ steps,
      prefixDecodeProg.Exec
        (store7 (encNat n ++ tail) [] [] [] (List.replicate cap .one) [] status)
        (store7 tail [] (List.replicate n .one) [] (List.replicate (cap-n) .one) []
          (.one :: .one :: status)) steps ∧
      steps ≤ (9*cap+18)*n.bits.length+10 := by
  have hmap : (n.bits.map TensorGraphPrefix3.digitSym).reverse = scannerDigits n := by
    unfold scannerDigits
    congr 1
  have hp : parseCanonicalBlockProg.Exec
      (TensorGraphPrefix3.store (encNat n ++ tail) [] status)
      (TensorGraphPrefix3.store tail (scannerDigits n) (.one :: .one :: status))
      (3*n.bits.length+7) := by
    simpa only [hmap] using parseCanonicalBlockProg_encNat n tail status
  have hparse := parse_exec7 (encNat n ++ tail) [] [] [] (List.replicate cap .one) [] status
    tail (scannerDigits n) (.one :: .one :: status) (3*n.bits.length+7) hp
  obtain ⟨dsteps, hd, hdbound⟩ := cappedDecode_scannerDigits n cap (.one :: status) hcap
  have hdecode7 := decode_exec7 tail (scannerDigits n) [] [] (List.replicate cap .one) []
    (.one :: .one :: status)
    (TensorCappedDecode.store6 [] (List.replicate n .one) [] (List.replicate (cap-n) .one) [] (.one :: .one :: status)) dsteps hd
  rw [write_decode] at hdecode7
  have ha : accepted (fun k ↦
      (store7 tail (scannerDigits n) [] [] (List.replicate cap .one) [] (.one :: .one :: status) k).head?) = true := by rfl
  have hb := StackProg.Exec.branchTrue (q := .act keepAct) ha hdecode7
  have he := StackProg.Exec.seq hparse hb
  refine ⟨(3*n.bits.length+7)+1+(1+dsteps), he, ?_⟩
  nlinarith

end TensorPrefixDecode

namespace TensorGraphPrefix3

/-- All-input parser classification: a successful marker identifies an exact
    canonical natural-number prefix and its true MSB-first digits. -/
theorem parseCanonicalBlockProg_total_canonical (input status : List BSym) :
    ∃ rest outdigits outstatus steps,
      parseCanonicalBlockProg.Exec (store input [] status) (store rest outdigits outstatus) steps ∧
      steps ≤ 3*input.length+7 ∧ outdigits.length ≤ input.length ∧
      ((∃ n, input = encNat n ++ rest ∧ outdigits = TensorCappedDecode.scannerDigits n ∧
          outstatus = .one :: .one :: status) ∨ outstatus.head? ≠ some .one) := by
  obtain ⟨digits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  have hbound : 3*digits.length+7 ≤ 3*(digits.map digitSym ++ stop).length+7 := by
    simp only [List.length_append, List.length_map]
    omega
  have hlen : (digits.map digitSym).reverse.length ≤ (digits.map digitSym ++ stop).length := by
    simp only [List.length_reverse, List.length_map, List.length_append]
    omega
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    refine ⟨[], (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, ?_, hbound, hlen, Or.inr (by simp)⟩
    simpa using parseCanonicalBlockProg_reject_eof digits status
  · subst stop
    rcases digit_end_cases digits with hempty | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · have hcanonical : digits = [] ∨ ∃ pre, digits = pre ++ [true] := Or.inl hempty
      obtain ⟨n, hn⟩ := (TensorCanonicalDigits.canonical_digits_iff digits).mp hcanonical
      refine ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status, 3*digits.length+7,
        parseCanonicalBlockProg_accept digits tail status hcanonical, hbound, hlen, Or.inl ⟨n, ?_, ?_, rfl⟩⟩
      · rw [← hn]
        simp [encNat, digitSym, List.append_assoc]
      · rw [← hn]
        rfl
    · have hcanonical : digits = [] ∨ ∃ pre, digits = pre ++ [true] := Or.inr ⟨pre, htrue⟩
      obtain ⟨n, hn⟩ := (TensorCanonicalDigits.canonical_digits_iff digits).mp hcanonical
      refine ⟨tail, (digits.map digitSym).reverse, .one :: .one :: status, 3*digits.length+7,
        parseCanonicalBlockProg_accept digits tail status hcanonical, hbound, hlen, Or.inl ⟨n, ?_, ?_, rfl⟩⟩
      · rw [← hn]
        simp [encNat, digitSym, List.append_assoc]
      · rw [← hn]
        rfl
    · subst digits
      exact ⟨tail, ((pre ++ [false]).map digitSym).reverse, .zero :: .one :: status,
        3*(pre ++ [false]).length+7, parseCanonicalBlockProg_reject_high_zero pre tail status,
        hbound, hlen, Or.inr (by simp)⟩
  · subst stop
    exact ⟨.minus :: tail, (digits.map digitSym).reverse, .zero :: .zero :: status,
      3*digits.length+7, parseCanonicalBlockProg_reject_minus digits tail status,
      hbound, hlen, Or.inr (by simp)⟩

end TensorGraphPrefix3




namespace CanonicalParserProgress

theorem exec_det {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ {u : K → List A} {m : ℕ}, p.Exec s u m → t = u := by
  induction h with
  | act f s =>
      intro u m h2
      cases h2
      rfl
  | seq hab hbc ihab ihbc =>
      intro u m h2
      cases h2 with
      | seq hab' hbc' =>
          have e : _ = _ := ihab hab'
          rw [← e] at hbc'
          exact ihbc hbc'
  | branchTrue ht hb ih =>
      intro u m h2
      cases h2 with
      | branchTrue _ hb' => exact ih hb'
      | branchFalse hf _ =>
          rw [ht] at hf
          cases hf
  | branchFalse ht hb ih =>
      intro u m h2
      cases h2 with
      | branchFalse _ hb' => exact ih hb'
      | branchTrue hf _ =>
          rw [ht] at hf
          cases hf
  | loopFalse ht =>
      intro u m h2
      cases h2 with
      | loopFalse _ => rfl
      | loopTrue ht' _ _ =>
          rw [ht] at ht'
          cases ht'
  | loopTrue ht hb hrest ihab ihrest =>
      intro u m h2
      cases h2 with
      | loopFalse ht' =>
          rw [ht] at ht'
          cases ht'
      | loopTrue _ hb' hrest' =>
          have e : _ = _ := ihab hb'
          rw [← e] at hrest'
          exact ihrest hrest'




end CanonicalParserProgress

open CanonicalParserProgress

/-- On any input, the public canonical block parser's success marker proves
    that it consumed at least one source symbol, even for the empty code. -/
theorem solution (input status rest digits markerTail : List BSym) (steps : ℕ)
    (h : CookPvsNP.CanonicalBlockParser.parseCanonicalBlockProg.Exec
      (CookPvsNP.CanonicalBlockParser.store input [] status)
      (CookPvsNP.CanonicalBlockParser.store rest digits (.one :: markerTail)) steps) :
    rest.length < input.length := by
  have hl : TensorGraphPrefix3.parseCanonicalBlockProg.Exec
      (TensorGraphPrefix3.store input [] status)
      (TensorGraphPrefix3.store rest digits (.one :: markerTail)) steps := h
  obtain ⟨rest', digits', outstatus, otherSteps, hrun, _, _, hclass⟩ :=
    TensorGraphPrefix3.parseCanonicalBlockProg_total_canonical input status
  have heq := exec_det hl hrun
  have hrest : rest = rest' := by
    simpa [TensorGraphPrefix3.store] using congrFun heq (0 : Fin 3)
  have hstatus : .one :: markerTail = outstatus := by
    simpa [TensorGraphPrefix3.store] using congrFun heq (2 : Fin 3)
  rcases hclass with ⟨n, hin, _, _⟩ | hbad
  · have hn : 0 < (encNat n).length := by simp [encNat]
    rw [hin, ← hrest]
    simp only [List.length_append]
    omega
  · rw [← hstatus] at hbad
    simp at hbad

