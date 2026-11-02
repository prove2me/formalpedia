-- Prove2me | solution 1 for CookPvsNP.unary_to_encNat_stack
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:48:13.650564+00:00
-- url     : https://prove2.me/submissions/db18e0ab-1bb7-4485-93f3-843b95d553a4

import Definitions.Def_TensorUnaryHalf
import Theorems.Thm_TensorUnaryHalf_halfProg_exec
import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer

namespace TensorUnaryBinaryWriterInternal

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


namespace TensorUnaryBinaryProgram
open CookPvsNP ProjSchedTW.Complexity StackProgPortLift

/-- The five ports are preserved input, output, current dividend, quotient,
    and a shared delimiter/parity/reversed-bit accumulator. -/
def store (input output dividend quotient bits : List BSym) : Fin 5 → List BSym :=
  fun k ↦ if k=0 then input else if k=1 then output else if k=2 then dividend else if k=3 then quotient else bits

private def halfPorts : Fin 3 ↪ Fin 5 := ⟨![2,3,4], by decide⟩
private def halfDecode : Fin 5 → Option (Fin 3) := ![none,none,some 0,some 1,some 2]
private theorem halfDecode_correct (l : Fin 5) (k : Fin 3) :
    halfDecode l = some k ↔ halfPorts k = l := by fin_cases l <;> fin_cases k <;> decide

private def hasDividend (h : Fin 5 → Option BSym) : Bool := h 2 == some .one
private def oddMarker (h : Fin 5 → Option BSym) : Bool := h 4 == some .one

/-- Pop an optional parity marker and delimiter, then push the corresponding
    binary digit onto the shared reversed-bit accumulator. -/
def recordBitProg : StackProg (Fin 5) BSym :=
  .branch oddMarker
    (.seq (popProg 4) (.seq (popProg 4) (pushProg 4 .one)))
    (.seq (popProg 4) (pushProg 4 .zero))

/-- One long-division pass, after a separator isolates its parity marker. -/
def binaryPassProg : StackProg (Fin 5) BSym :=
  .seq (pushProg 4 .sep)
    (.seq (liftProgC halfPorts halfDecode TensorUnaryHalf.halfProg)
      (.seq recordBitProg (transferProg 3 (fun k ↦ decide (k=2)))))

/-- A fixed five-stack candidate for canonical unary-to-binary emission.
    The source counter is preserved. The existing output tail is not touched
    until the separator and reversed bit accumulator are transferred onto it. -/
def unaryBinaryProg : StackProg (Fin 5) BSym :=
  .seq (copyProg 0 2 4)
    (.seq (.loop hasDividend binaryPassProg)
      (.seq (pushProg 1 .sep) (transferProg 4 (fun k ↦ decide (k=1)))))

end TensorUnaryBinaryProgram

open StackProgPortLift

namespace TensorUnaryBinaryProgram

/-- Zero emits its canonical separator and preserves any pre-existing tail. -/
theorem unaryBinaryProg_zero (tail : List BSym) :
    unaryBinaryProg.Exec (store [] tail [] [] [])
      (store [] (encNat 0 ++ tail) [] [] []) 9 := by
  classical
  let s := store [] tail [] [] []
  let t := store [] (.sep :: tail) [] [] []
  have hs4 : s 4 = [] := by simp [s, store]
  have hc : (copyProg (0 : Fin 5) 2 4).Exec s s 3 := by
    have h := stack_copy (0 : Fin 5) 2 4 (by decide) (by decide) (by decide) s hs4
    have he : Function.update s 2 (s 0 ++ s 2) = s := by
      funext k; fin_cases k <;> simp [s, store, Function.update]
    rw [he] at h
    simpa [s, store] using h
  have hl : (StackProg.loop hasDividend binaryPassProg).Exec s s 1 := by
    apply StackProg.Exec.loopFalse
    simp [hasDividend, s, store]
  have hp : (pushProg (1 : Fin 5) .sep).Exec s t 1 := by
    have he : StackProg.applyAct (fun _ k ↦ if k=(1 : Fin 5) then .push BSym.sep else .keep) s = t := by
      funext k; fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, s, t, store]
    simpa only [pushProg, he] using StackProg.Exec.act (fun _ k ↦ if k=(1 : Fin 5) then .push BSym.sep else .keep) s
  have ht : (transferProg (4 : Fin 5) (fun k ↦ decide (k=1))).Exec t t 1 := by
    have h := stack_transfer (4 : Fin 5) (fun k ↦ decide (k=1)) t
    have he : transferStore (4 : Fin 5) (fun k ↦ decide (k=1)) t = t := by
      funext k; fin_cases k <;> simp [transferStore, t, store]
    rw [he] at h
    simpa [t, store] using h
  have he := StackProg.Exec.seq hc (StackProg.Exec.seq hl (StackProg.Exec.seq hp ht))
  simpa [unaryBinaryProg, s, t, encNat, Nat.zero_bits] using he

end TensorUnaryBinaryProgram

namespace TensorUnaryBinaryProgram

private theorem pop_acc (input output dividend quotient : List BSym) (a : BSym) (bits : List BSym) :
    (popProg (4 : Fin 5)).Exec (store input output dividend quotient (a :: bits))
      (store input output dividend quotient bits) 1 := by
  have he : StackProg.applyAct (fun _ k ↦ if k=(4 : Fin 5) then .pop else .keep)
      (store input output dividend quotient (a :: bits)) = store input output dividend quotient bits := by
    funext k; fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, store]
  simpa only [popProg, he] using StackProg.Exec.act
    (fun _ k ↦ if k=(4 : Fin 5) then .pop else .keep) (store input output dividend quotient (a :: bits))

private theorem push_acc (input output dividend quotient bits : List BSym) (a : BSym) :
    (pushProg (4 : Fin 5) a).Exec (store input output dividend quotient bits)
      (store input output dividend quotient (a :: bits)) 1 := by
  have he : StackProg.applyAct (fun _ k ↦ if k=(4 : Fin 5) then .push a else .keep)
      (store input output dividend quotient bits) = store input output dividend quotient (a :: bits) := by
    funext k; fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, store]
  simpa only [pushProg, he] using StackProg.Exec.act
    (fun _ k ↦ if k=(4 : Fin 5) then .push a else .keep) (store input output dividend quotient bits)

/-- An even-pass marker is the delimiter alone; it becomes a zero digit. -/
theorem recordBit_even (input output dividend quotient bits : List BSym) :
    recordBitProg.Exec (store input output dividend quotient (.sep :: bits))
      (store input output dividend quotient (.zero :: bits)) 4 := by
  have h := StackProg.Exec.seq (pop_acc input output dividend quotient .sep bits)
    (push_acc input output dividend quotient bits .zero)
  exact StackProg.Exec.branchFalse (test := oddMarker) (by rfl) h

/-- An odd-pass marker is one followed by the delimiter; it becomes one digit. -/
theorem recordBit_odd (input output dividend quotient bits : List BSym) :
    recordBitProg.Exec (store input output dividend quotient (.one :: .sep :: bits))
      (store input output dividend quotient (.one :: bits)) 6 := by
  have h := StackProg.Exec.seq (pop_acc input output dividend quotient .one (.sep :: bits))
    (StackProg.Exec.seq (pop_acc input output dividend quotient .sep bits)
      (push_acc input output dividend quotient bits .one))
  exact StackProg.Exec.branchTrue (test := oddMarker) (by rfl) h

end TensorUnaryBinaryProgram

namespace TensorUnaryBinaryProgram

private theorem halfWrite (t : Fin 3 → List BSym) (s : Fin 5 → List BSym) :
    write halfPorts t s = fun k ↦ if k=2 then t 0 else if k=3 then t 1 else if k=4 then t 2 else s k := by
  funext k
  fin_cases k
  · simpa using (write_outside halfPorts t s (l := 0) (by intro j; fin_cases j <;> decide))
  · simpa using (write_outside halfPorts t s (l := 1) (by intro j; fin_cases j <;> decide))
  · simpa [halfPorts] using (write_at halfPorts t s 0)
  · simpa [halfPorts] using (write_at halfPorts t s 1)
  · simpa [halfPorts] using (write_at halfPorts t s 2)

/-- Given the standalone unary-halving theorem, one binary division pass
    leaves the quotient as its next dividend and pushes the correct parity bit. -/
theorem binaryPassProg_exec (n : ℕ) (input output bits : List BSym)
    (hhalf : ∀ (k : ℕ) (q r : List BSym), TensorUnaryHalf.halfProg.Exec
      (TensorUnaryHalf.store (List.replicate k .one) q r)
      (TensorUnaryHalf.store [] (List.replicate (k/2) .one ++ q)
        ((if k%2=0 then [] else [.one]) ++ r)) (6*((k+1)/2)+1)) :
    binaryPassProg.Exec (store input output (List.replicate n .one) [] bits)
      (store input output (List.replicate (n/2) .one) []
        ((if n%2=0 then .zero else .one) :: bits))
      (1+1+((6*((n+1)/2)+1)+1+
        ((if n%2=0 then 4 else 6)+1+(3*(n/2)+1)))) := by
  classical
  let s := store input output (List.replicate n .one) [] bits
  let a := store input output (List.replicate n .one) [] (.sep :: bits)
  let b := store input output [] (List.replicate (n/2) .one)
    ((if n%2=0 then [] else [.one]) ++ (.sep :: bits))
  let bit := if n%2=0 then BSym.zero else .one
  let c := store input output [] (List.replicate (n/2) .one) (bit :: bits)
  let d := store input output (List.replicate (n/2) .one) [] (bit :: bits)
  have hp := push_acc input output (List.replicate n .one) [] bits .sep
  have hproj : project halfPorts a = TensorUnaryHalf.store (List.replicate n .one) [] (.sep :: bits) := by
    funext k; fin_cases k <;> simp [project, halfPorts, a, store, TensorUnaryHalf.store]
  have hw : write halfPorts (TensorUnaryHalf.store []
      (List.replicate (n/2) .one ++ []) ((if n%2=0 then [] else [.one]) ++ (.sep :: bits))) a = b := by
    funext k; fin_cases k <;> simp [halfWrite, a, b, store, TensorUnaryHalf.store]
  have hh := lift_exec halfPorts (hhalf n [] (.sep :: bits)) a hproj
  rw [hw] at hh
  have hr : recordBitProg.Exec b c (if n%2=0 then 4 else 6) := by
    by_cases hn : n%2=0
    · simpa [b, c, bit, hn] using recordBit_even input output [] (List.replicate (n/2) .one) bits
    · simpa [b, c, bit, hn] using recordBit_odd input output [] (List.replicate (n/2) .one) bits
  have ht : (transferProg (3 : Fin 5) (fun k ↦ decide (k=2))).Exec c d (3*(n/2)+1) := by
    have h := stack_transfer (3 : Fin 5) (fun k ↦ decide (k=2)) c
    have he : transferStore (3 : Fin 5) (fun k ↦ decide (k=2)) c = d := by
      funext k; fin_cases k <;> simp [transferStore, c, d, store]
    rw [he] at h
    simpa [c, store] using h
  have he := StackProg.Exec.seq hp (StackProg.Exec.seq hh (StackProg.Exec.seq hr ht))
  simpa only [binaryPassProg, liftProgC_eq_liftProg halfPorts halfDecode halfDecode_correct,
    s, a, b, c, d, bit] using he

end TensorUnaryBinaryProgram

open ProjSchedTW.Complexity

/-- A nonzero natural's canonical LSB-first binary representation starts with
    its parity bit, followed by the representation of its integer half. -/
theorem encNat_bits_step (n : ℕ) (hn : 0 < n) :
    (Nat.bits n).map (fun b ↦ if b then BSym.one else BSym.zero) =
      (if n % 2 = 0 then BSym.zero else BSym.one) ::
        (Nat.bits (n/2)).map (fun b ↦ if b then BSym.one else BSym.zero) := by
  have hmod : n % 2 < 2 := Nat.mod_lt n (by decide)
  have hdiv := Nat.mod_add_div n 2
  by_cases h : n % 2 = 0
  · have hq : n/2 ≠ 0 := by omega
    have he : n = 2*(n/2) := by omega
    conv_lhs => rw [he, Nat.bit0_bits _ hq]
    simp [h]
  · have h1 : n % 2 = 1 := by omega
    have he : n = 2*(n/2)+1 := by omega
    conv_lhs => rw [he, Nat.bit1_bits]
    simp [h]

namespace TensorUnaryBinaryProgram

/-- Repeated halving writes the canonical digits in reverse on the shared
    accumulator. This loop theorem assumes only the separate halving contract. -/
theorem binaryLoop_exec (n : ℕ) (input output bits : List BSym)
    (hhalf : ∀ (k : ℕ) (q r : List BSym), TensorUnaryHalf.halfProg.Exec
      (TensorUnaryHalf.store (List.replicate k .one) q r)
      (TensorUnaryHalf.store [] (List.replicate (k/2) .one ++ q)
        ((if k%2=0 then [] else [.one]) ++ r)) (6*((k+1)/2)+1)) :
    ∃ steps, steps ≤ 100*(n+1)^2 ∧
      (StackProg.loop hasDividend binaryPassProg).Exec
        (store input output (List.replicate n .one) [] bits)
        (store input output [] []
          (((Nat.bits n).map (fun b ↦ if b then BSym.one else BSym.zero)).reverse ++ bits)) steps := by
  induction n using Nat.strong_induction_on generalizing bits with
  | h n ih =>
    by_cases hz : n=0
    · subst n
      refine ⟨1, by norm_num, ?_⟩
      simp only [List.replicate_zero, Nat.zero_bits, List.map_nil, List.reverse_nil, List.nil_append]
      apply StackProg.Exec.loopFalse
      simp [hasDividend, store]
    · have hn : 0<n := by omega
      have hlt : n/2 < n := Nat.div_lt_self hn (by decide)
      let bit := if n%2=0 then BSym.zero else .one
      let pc := 1+1+((6*((n+1)/2)+1)+1+
        ((if n%2=0 then 4 else 6)+1+(3*(n/2)+1)))
      have ht : hasDividend (fun k ↦ (store input output (List.replicate n .one) [] bits k).head?) = true := by
        cases n with
        | zero => contradiction
        | succ n => simp [hasDividend, store, List.replicate_succ]
      have hp : binaryPassProg.Exec (store input output (List.replicate n .one) [] bits)
          (store input output (List.replicate (n/2) .one) [] (bit :: bits)) pc := by
        simpa [bit, pc] using binaryPassProg_exec n input output bits hhalf
      obtain ⟨d, hd, hloop⟩ := ih (n/2) hlt (bit :: bits)
      have hbits := encNat_bits_step n hn
      have hend :
          (((Nat.bits (n/2)).map (fun b ↦ if b then BSym.one else BSym.zero)).reverse ++ (bit :: bits)) =
          (((Nat.bits n).map (fun b ↦ if b then BSym.one else BSym.zero)).reverse ++ bits) := by
        rw [hbits]
        simp [bit, List.reverse_cons, List.append_assoc]
      have he := StackProg.Exec.loopTrue ht hp hloop
      rw [hend] at he
      refine ⟨1+pc+1+d, ?_, he⟩
      have hdiv1 : n/2 ≤ n := Nat.div_le_self n 2
      have hdiv2 : (n+1)/2 ≤ n+1 := Nat.div_le_self (n+1) 2
      have hpc : pc ≤ 20*(n+1) := by
        dsimp [pc]
        split <;> omega
      have hq : n/2+1 ≤ n := by omega
      have hsq : (n/2+1)^2 ≤ n^2 := Nat.pow_le_pow_left hq 2
      nlinarith

end TensorUnaryBinaryProgram

open CookPvsNP

/-- A single atomic stack action can increase any one stack by at most one. -/
private theorem stack_applyAct_length_le {K A : Type} (f : (K → Option A) → K → StackAct A)
    (s : K → List A) (k : K) :
    ((StackProg.applyAct f s) k).length ≤ (s k).length + 1 := by
  simp only [StackProg.applyAct]
  cases h : f (fun j ↦ (s j).head?) k with
  | keep => simp [StackAct.apply]
  | push a => simp [StackAct.apply]
  | pop =>
    cases hs : s k with
    | nil => simp [StackAct.apply, hs]
    | cons a tail => simp [StackAct.apply, hs] <;> omega

/-- Every individual stack in a structured execution grows by at most the
    total source-step count, irrespective of the program or input alphabet. -/
theorem stack_exec_length_le {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ k, (t k).length ≤ (s k).length + n := by
  induction h with
  | act f s => exact stack_applyAct_length_le f s
  | seq hp hq ihp ihq =>
    intro k
    have h1 := ihp k
    have h2 := ihq k
    omega
  | branchTrue ht hp ih =>
    intro k
    have h1 := ih k
    omega
  | branchFalse ht hp ih =>
    intro k
    have h1 := ih k
    omega
  | loopFalse ht =>
    intro k
    omega
  | loopTrue ht hp hl ihp ihl =>
    intro k
    have h1 := ihp k
    have h2 := ihl k
    omega

namespace TensorUnaryBinaryProgram

/-- A fixed five-stack unary-to-canonical-binary writer follows from the
    separate exact unary-halving theorem. The source counter and arbitrary
    output tail are preserved, and the runtime is quadratically bounded. -/
theorem unary_to_encNat_of_half
    (hhalf : ∀ (k : ℕ) (q r : List BSym), TensorUnaryHalf.halfProg.Exec
      (TensorUnaryHalf.store (List.replicate k .one) q r)
      (TensorUnaryHalf.store [] (List.replicate (k/2) .one ++ q)
        ((if k%2=0 then [] else [.one]) ++ r)) (6*((k+1)/2)+1)) :
    ∃ (p : StackProg (Fin 5) BSym) (C : ℕ),
      ∀ (n : ℕ) (tail : List BSym), ∃ steps,
        p.Exec
          (fun k ↦ if k=0 then List.replicate n .one else if k=1 then tail else [])
          (fun k ↦ if k=0 then List.replicate n .one else if k=1 then encNat n ++ tail else []) steps ∧
        steps ≤ C*(n+1)^2 := by
  refine ⟨unaryBinaryProg, 420, ?_⟩
  intro n tail
  let unary := List.replicate n BSym.one
  let digits := (Nat.bits n).map (fun b ↦ if b then BSym.one else BSym.zero)
  let s := store unary tail [] [] []
  let t := store unary tail unary [] []
  let u := store unary tail [] [] digits.reverse
  let w := store unary (.sep :: tail) [] [] digits.reverse
  let f := store unary (digits ++ .sep :: tail) [] [] []
  have hs4 : s 4 = [] := by simp [s, store]
  have hc : (copyProg (0 : Fin 5) 2 4).Exec s t (6*n+3) := by
    have h := stack_copy (0 : Fin 5) 2 4 (by decide) (by decide) (by decide) s hs4
    have he : Function.update s 2 (s 0 ++ s 2) = t := by
      funext k; fin_cases k <;> simp [s, t, store, Function.update]
    rw [he] at h
    simpa [s, store, unary] using h
  obtain ⟨d, hd, hl⟩ := binaryLoop_exec n unary tail [] hhalf
  have hl' : (StackProg.loop hasDividend binaryPassProg).Exec t u d := by
    simpa [t, u, store, unary, digits] using hl
  have hlen : digits.length ≤ d := by
    have h := stack_exec_length_le hl' 4
    simpa [t, u, store] using h
  have hp : (pushProg (1 : Fin 5) .sep).Exec u w 1 := by
    have he : StackProg.applyAct (fun _ k ↦ if k=(1 : Fin 5) then .push BSym.sep else .keep) u = w := by
      funext k; fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, u, w, store]
    simpa only [pushProg, he] using StackProg.Exec.act (fun _ k ↦ if k=(1 : Fin 5) then .push BSym.sep else .keep) u
  have ht : (transferProg (4 : Fin 5) (fun k ↦ decide (k=1))).Exec w f (3*digits.length+1) := by
    have h := stack_transfer (4 : Fin 5) (fun k ↦ decide (k=1)) w
    have he : transferStore (4 : Fin 5) (fun k ↦ decide (k=1)) w = f := by
      funext k; fin_cases k <;> simp [transferStore, w, f, store]
    rw [he] at h
    simpa [w, store] using h
  let steps := (6*n+3)+1+(d+1+(1+1+(3*digits.length+1)))
  refine ⟨steps, ?_, ?_⟩
  · have he := StackProg.Exec.seq hc (StackProg.Exec.seq hl' (StackProg.Exec.seq hp ht))
    have hstart : s = (fun k ↦ if k=0 then List.replicate n .one else if k=1 then tail else []) := by
      funext k; fin_cases k <;> simp [s, store, unary]
    have hfinal : f = (fun k ↦ if k=0 then List.replicate n .one else if k=1 then encNat n ++ tail else []) := by
      funext k; fin_cases k <;> simp [f, store, unary, digits, encNat, List.append_assoc]
    rw [hstart, hfinal] at he
    simpa only [unaryBinaryProg, steps] using he
  · dsimp only [steps]
    have hn : n ≤ (n+1)^2 := by nlinarith
    nlinarith

end TensorUnaryBinaryProgram


end TensorUnaryBinaryWriterInternal

open CookPvsNP ProjSchedTW.Complexity

theorem solution :
    ∃ (p : StackProg (Fin 5) BSym) (C : ℕ),
      ∀ (n : ℕ) (tail : List BSym), ∃ steps,
        p.Exec
          (fun k ↦ if k=0 then List.replicate n .one else if k=1 then tail else [])
          (fun k ↦ if k=0 then List.replicate n .one else if k=1 then encNat n ++ tail else []) steps ∧
        steps ≤ C*(n+1)^2 := by
  exact TensorUnaryBinaryWriterInternal.TensorUnaryBinaryProgram.unary_to_encNat_of_half TensorUnaryHalf.halfProg_exec
