-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:36:27.679787+00:00
-- url     : https://prove2.me/submissions/e2c1c829-48de-486e-9f4d-1f59f229b0c0

import Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_9
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_11
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_12
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_2
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.left : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start a := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.right : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction a))
      b := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.head : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.tail : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Walk.cost_telescope : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (p : Fin n → Real),
      @Eq.{1} Real
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin k) Real
            (fun e =>
              @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
            es))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (p u) (p v)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Walk.eq_of_empty : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Eq.{1} (List.{0} (Fin k)) es (@List.nil.{0} (Fin k)) → @Eq.{1} (Fin n) u v := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.list_sum_ofReal : ∀ {k : Nat} (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (es : List.{0} (Fin k)),
      @Eq.{1} ENNReal
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero
          (@List.map.{0, 0} (Fin k) ENNReal (fun e => ENNReal.ofReal (w e)) es))
        (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.distance_le_walk : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (w : Fin k → ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero (@List.map.{0, 0} (Fin k) ENNReal w es)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.update : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (target : Fin i.n) (candidate : Nat),
      (∀ (v u : Fin i.n),
          @Ne.{1} Nat (@Fin.val i.n v)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n u))) →
        @Eq.{1} (Nat → Nat) t.natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem (@Fin.val i.n target)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n target))
              candidate) →
          @Eq.{1} (Nat → Real) t.realMem
              (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (@Fin.val i.n target)
                (@Nat.cast.{0} Real Real.instNatCast candidate)) →
            DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l
              (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative target
                (@Option.some.{0} Nat candidate))
              t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.delete : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    ∀ (e : Fin i.k),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val i.k e) →
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.deletedData s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.deletion : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (e : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p c e) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheImage.initial : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j cache : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    (∀ (v : Fin i.n),
        And
          (@Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
            (g.natMem (@Fin.val i.n v)))
          (And
            (@Eq.{1} Real
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (DecrAlmostLinearSSSP.Decremental.delta i j) (g.realMem (@Fin.val i.n v))))
            (@Eq.{1} ENNReal
              (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))))) →
      (∀ (v : Fin i.n),
          And
            (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat (g.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (g.realMem (@Fin.val i.n v)))) →
        DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache
          (fun v => DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)) s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {g : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve g b ptr s →
    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n i.source))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ScanTable.refresh : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).records
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).caches
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      b s →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (bnew : Fin i.n → ENNReal),
      DecrAlmostLinearSSSP.Decremental.Native.CacheImage i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).caches
            i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
          bnew t →
        (∀ (address : Nat),
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                    (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                    i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).records
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).caches
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@Function.update.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (fun a => Fin i.n → ENNReal)
              (instDecidableEqFin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) b j bnew)
            t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j q : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q s g.natMem g.realMem →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q t g.natMem g.realMem := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.reports : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (r : Nat),
      @LE.le.{0} Nat instLENat r reserve →
        @Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).reports
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).reports
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue.head : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.cache : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      And
        (@Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))
        (@Eq.{1} Real
          (t.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory.update : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {a b : DecrAlmostLinearSSSP.Decremental.AdapterState i} {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a s →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s u →
        DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve
            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) u t →
          (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
              DecrAlmostLinearSSSP.Decremental.Native.CacheImage i
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b q) t) →
            DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                final (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b j) t →
              DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve
                (@Function.update.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (fun a => DecrAlmostLinearSSSP.Decremental.Machine)
                  (instDecidableEqFin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) f j final)
                b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.core_indegree_pos : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : Fin b.input.n),
  @Ne.{1} (Fin b.input.n) v b.input.source →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (DecrAlmostLinearSSSP.Decremental.indegree b v) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.core_A_ge : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (DecrAlmostLinearSSSP.Decremental.A b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.core_Q_ge : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Nat.cast.{0} Real Real.instNatCast b.input.n))
    (DecrAlmostLinearSSSP.Decremental.Q b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.core_cost_bounds : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.cost b active
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
    (@LE.le.{0} Real Real.instLE
      (DecrAlmostLinearSSSP.Decremental.cost b active
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 8)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
          (@Nat.cast.{0} Real Real.instNatCast b.input.n)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.core_coefficient_bounds : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (DecrAlmostLinearSSSP.Decremental.coefficient b e))
    (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.coefficient b e)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (DecrAlmostLinearSSSP.Decremental.A b)
        (@Nat.cast.{0} Real Real.instNatCast b.input.size))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.core_kappa_bounds : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (And
      (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.n))
              (DecrAlmostLinearSSSP.Decremental.A b))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (DecrAlmostLinearSSSP.Decremental.kappa b))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.2.2.2.2
section s0
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s0
section s1
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s1
section s2
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s2
section s3
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s3
section s4
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s4
section s5
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s5
section s6
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s6
section s7
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s7
section s8
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s8
section s9
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s9
section s10
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s10
section s11
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s11
section s12
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s12
section s13
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s13
section s14
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s14
section s15
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Structured
end s15
section s16
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s16
section s17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s17
section s18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s18
section s19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s19
section s20
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s20
section s21
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s21
section s22
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s22
section s23
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s23
section s24
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s24
section s25
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s25
section s26
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s26
section s27
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s27
section s28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s28
section s29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s29
section s30
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s30
section s31
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s31
section s32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s32
section s33
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s33
section s34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s34
section s35
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s35
section s36
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s36
section s37
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Structured
end s38
section s39
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s39
section s40
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s40
section s41
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s41
section s42
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s42
section s43
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s43
section s44
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s44
section s45
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s46
section s47
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s47
section s48
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s48
section s49
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s49
section s50
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s50
section s51
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s53
section s54
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s54
section s55
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s56
section s57
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
end DecrAlmostLinearSSSP.Decremental.Instrumented
end s58
section s59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
end DecrAlmostLinearSSSP.Decremental.Instrumented
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s60
section s61
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s64
section s65
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s66
section s67
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s72
section s73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s73
section s74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s74
section s75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s75
section s76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s76
section s77
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s77
section s78
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s78
section s79
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s79
section s80
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s80
section s81
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s81
section s82
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s82
section s83
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s83
section s84
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s85
section s86
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s86
section s87
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s87
section s88
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s88
section s89
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s89
section s90
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s90
section s91
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s93
section s94
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s95
section s96
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s96
section s97
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s97
section s98
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s98
section s99
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s99
section s100
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s100
section s101
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s102
section s103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s103
section s104
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s104
section s105
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s105
section s106
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s106
section s107
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s107
section s108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s108
section s109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s110
section s111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s111
section s112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s112
section s113
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s113
section s114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s116
section s117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s117
section s118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s118
section s119
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s120
section s121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s123
section s124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s124
section s125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s126
section s127
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s127
section s128
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s128
section s129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s129
section s130
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s130
section s131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s131
section s132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s132
section s133
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s134
section s135
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s135
section s136
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s136
section s137
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s137
section s138
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s138
section s139
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s139
section s140
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s140
section s141
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s141
section s142
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s142
section s143
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s143
section s144
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s144
section s145
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s145
section s146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma K_inverse_square_bound (K : ℝ) (hK : 32 ≤ K) :
    0 < K ^ (-2 : ℤ) ∧ K ^ (-2 : ℤ) ≤ 1 / 1024 := by
  have hKpos : 0 < K := by linarith
  refine ⟨zpow_pos hKpos _, ?_⟩
  simp only [zpow_neg, zpow_ofNat, ← one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < K ^ 2) (by norm_num : (0 : ℝ) < 1024)).mpr
  nlinarith
end DecrAlmostLinearSSSP.Decremental
end s146
section s147
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma capacity_pos (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (e : Edge b) : 0 < capacity b active p e := by
  have hc := (core_coefficient_bounds b e).1
  have hk := (core_kappa_bounds b).1
  unfold capacity
  exact div_pos (by linarith) (lt_of_lt_of_le hk (le_max_right _ _))
lemma gradient_update (b : Core) (f : Edge b → ℝ) (e : Edge b) (t : ℝ) (v : Fin b.input.n) :
    gradient b (Function.update f e t) v = gradient b f v -
      (if v = tail b e then t - f e else 0) + (if v = head b e then t - f e else 0) := by
  classical
  have hfun : (fun d => ((if head b d = v then Function.update f e t d else 0) -
      (if tail b d = v then Function.update f e t d else 0))) =
      Function.update (fun d => ((if head b d = v then f d else 0) -
        (if tail b d = v then f d else 0))) e
        ((if head b e = v then t else 0) - (if tail b e = v then t else 0)) := by
    funext d
    by_cases hd : d = e
    · subst d; simp
    · simp [Function.update_of_ne hd]
  unfold gradient
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ e)]
  clear hfun
  have hsum := Finset.add_sum_erase Finset.univ
    (fun d : Edge b => ((if head b d = v then f d else 0) -
      (if tail b d = v then f d else 0))) (Finset.mem_univ e)
  rw [← hsum, Finset.sdiff_singleton_eq_erase]
  simp only [@eq_comm _ v (tail b e), @eq_comm _ v (head b e)]
  by_cases hhead : head b e = v <;> by_cases htail : tail b e = v
  all_goals simp only [hhead, htail, if_true, if_false]
  all_goals ring
lemma gradient_dot (b : Core) (f : Edge b → ℝ) (x : Fin b.input.n → ℝ) :
    dot (gradient b f) x = - ∑ e, f e * incidence b x e := by
  classical
  unfold dot gradient incidence
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (e : Edge b) :
      (∑ v, ((if head b e = v then f e else 0) - (if tail b e = v then f e else 0)) * x v) =
        -(f e * (x (tail b e) - x (head b e))) := by
    simp_rw [sub_mul, ite_mul, zero_mul]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp_rw [hinner]
  rw [Finset.sum_neg_distrib]
end DecrAlmostLinearSSSP.Decremental
end s147
section s148
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma physical_norm_cut {n k : ℕ} (h : Physical n k) (C : Finset (Fin n))
    (tau : ℝ) (ht : 0 ≤ tau) :
    physicalNorm h (cutDirection C tau) = tau * cutCapacity h C := by
  classical
  unfold physicalNorm cutCapacity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : h.graph.tail e ∈ C <;> by_cases hb : h.graph.head e ∈ C
  all_goals simp [cutDirection, ha, hb, abs_of_nonneg ht, mul_comm]
lemma dot_cut {n : ℕ} (g : Fin n → ℝ) (C : Finset (Fin n)) (tau : ℝ) :
    dot g (cutDirection C tau) = tau * ∑ v ∈ C, g v := by
  classical
  calc
    dot g (cutDirection C tau) = ∑ v ∈ C, g v * cutDirection C tau v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro v _ hv
      simp only [cutDirection, if_neg hv, mul_zero]
    _ = ∑ v ∈ C, tau * g v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [cutDirection, if_pos hv, mul_comm]
    _ = _ := (Finset.mul_sum _ _ _).symm
lemma cachedPhysical_norm_eq (b : Core) (s : State b) (x : Fin b.input.n → ℝ) :
    physicalNorm (cachedPhysical b s) x = norm b s.cache x := by
  classical
  simp only [physicalNorm, cachedPhysical, norm]
  exact Equiv.sum_comp (Fintype.equivFin (Edge b)).symm (fun e : Edge b => s.cache e * |incidence b x e|)
lemma toggle_potential (b : Core) (K : ℝ) (s : State b) (r : CutReply b) :
    potential b (toggle b K s r).active (labels b (toggle b K s r)) =
      potential b s.active (fun v => labels b s v + cutDirection r.cut (1 / (K ^ 2 * r.U)) v) := by
  classical
  unfold potential
  apply Finset.sum_congr rfl
  intro e _
  congr 2
  dsimp [slack, incidence, labels, toggle, cutDirection]
  split_ifs <;> ring
end DecrAlmostLinearSSSP.Decremental
end s148
section s149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma toggle_numeric_bounds (K : ℝ) (hK : 32 ≤ K) :
    0 < 1 / (K ^ 2 - 1) ∧ 1 / (K ^ 2 - 1) < 1 ∧
    K ^ (-2 : ℤ) * (1 / (K ^ 2 - 1)) ≤ 2 / K ^ 4 ∧
    (1 / (K ^ 2 - 1)) ^ 2 / (1 - 1 / (K ^ 2 - 1)) ≤ 2 / K ^ 4 ∧
    1 / (8 * K ^ 3) ≤ 1 / (4 * K ^ 3) - 4 / K ^ 4 := by
  have hKpos : 0 < K := by linarith
  have h1 : 0 < K ^ 2 - 1 := by nlinarith
  have h2 : 0 < K ^ 2 - 2 := by nlinarith
  have hq : 1 / (K ^ 2 - 1) < 1 := (div_lt_one h1).mpr (by nlinarith)
  refine ⟨by positivity, hq, ?_, ?_, ?_⟩
  · have hid : K ^ (-2 : ℤ) * (1 / (K ^ 2 - 1)) = 1 / ((K ^ 2 - 1) * K ^ 2) := by
      simp only [zpow_neg, zpow_ofNat, ← one_div]
      field_simp [hKpos.ne', h1.ne', h2.ne', show (-2 + K ^ 2) ≠ 0 by linarith]
      <;> ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < (K ^ 2 - 1) * K ^ 2) (by positivity : 0 < K ^ 4)).mpr
    nlinarith [sq_nonneg K]
  · have hid : (1 / (K ^ 2 - 1)) ^ 2 / (1 - 1 / (K ^ 2 - 1)) =
        1 / ((K ^ 2 - 1) * (K ^ 2 - 2)) := by
      field_simp [hKpos.ne', h1.ne', h2.ne']
      <;> ring_nf
      <;> nlinarith only [mul_inv_cancel₀ (show (-2 + K ^ 2) ≠ 0 by linarith)]
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < (K ^ 2 - 1) * (K ^ 2 - 2)) (by positivity : 0 < K ^ 4)).mpr
    have ht : 0 ≤ K ^ 2 * (K ^ 2 - 6) := mul_nonneg (sq_nonneg _) (by nlinarith)
    nlinarith only [ht]
  · have hid : 1 / (4 * K ^ 3) - 4 / K ^ 4 - 1 / (8 * K ^ 3) = (K - 32) / (8 * K ^ 4) := by
      field_simp [hKpos.ne', h1.ne', h2.ne', show (-2 + K ^ 2) ≠ 0 by linarith]
      <;> ring
    have hh : 0 ≤ (K - 32) / (8 * K ^ 4) := div_nonneg (sub_nonneg.mpr hK) (by positivity)
    linarith only [hid, hh]
end DecrAlmostLinearSSSP.Decremental
end s149
section s150
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma clippedLog_secant_upper {κ a b : ℝ} (hk : 0 < κ) :
    clippedLog κ b - clippedLog κ a ≤ (a - b) / max b κ := by
  by_cases ha : κ ≤ a <;> by_cases hb : κ ≤ b
  · have hap : 0 < a := hk.trans_le ha
    have hbp : 0 < b := hk.trans_le hb
    have hl := Real.log_le_sub_one_of_pos (div_pos hap hbp)
    rw [Real.log_div hap.ne' hbp.ne'] at hl
    simp only [clippedLog, if_pos ha, if_pos hb, max_eq_left hb, sub_div, div_self hbp.ne']
    linarith
  · have hap : 0 < a := hk.trans_le ha
    have hl := Real.log_le_sub_one_of_pos (div_pos hap hk)
    rw [Real.log_div hap.ne' hk.ne'] at hl
    simp only [clippedLog, if_pos ha, if_neg hb, max_eq_right (le_of_not_ge hb), sub_div]
    linarith
  · have hbp : 0 < b := hk.trans_le hb
    have hl := Real.log_le_sub_one_of_pos (div_pos hk hbp)
    rw [Real.log_div hk.ne' hbp.ne'] at hl
    have hdiv : (κ - a) / b ≤ (κ - a) / κ :=
      div_le_div_of_nonneg_left (by linarith : 0 ≤ κ - a) hk hb
    rw [sub_div, sub_div, div_self hk.ne'] at hdiv
    simp only [clippedLog, if_neg ha, if_pos hb, max_eq_left hb, sub_div, div_self hbp.ne']
    linarith
  · simp only [clippedLog, if_neg ha, if_neg hb, max_eq_right (le_of_not_ge hb), sub_div]
    linarith
lemma clippedLog_remainder {κ a d : ℝ} (hk : 0 < κ) :
    clippedLog κ (a + d) - clippedLog κ a + d / max a κ ≤
      d ^ 2 / (max a κ * max (a + d) κ) := by
  have ht : 0 < max a κ := lt_of_lt_of_le hk (le_max_right _ _)
  have hu : 0 < max (a + d) κ := lt_of_lt_of_le hk (le_max_right _ _)
  have hs := clippedLog_secant_upper (a := a) (b := a + d) hk
  have hd : |max (a + d) κ - max a κ| ≤ |d| := by
    simpa only [add_sub_cancel_left] using abs_max_sub_max_le_abs (a + d) a κ
  have hprod : d * (max (a + d) κ - max a κ) ≤ d ^ 2 := by
    calc
      _ ≤ |d * (max (a + d) κ - max a κ)| := le_abs_self _
      _ = |d| * |max (a + d) κ - max a κ| := abs_mul _ _
      _ ≤ |d| * |d| := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = d ^ 2 := by rw [← sq_abs]; ring
  have halg : (a - (a + d)) / max (a + d) κ + d / max a κ =
      d * (max (a + d) κ - max a κ) / (max a κ * max (a + d) κ) := by
    field_simp
    ring
  calc
    _ ≤ (a - (a + d)) / max (a + d) κ + d / max a κ := by linarith only [hs]
    _ = _ := halg
    _ ≤ _ := div_le_div_of_nonneg_right hprod (by positivity)
lemma weighted_clippedLog_remainder {κ a d mu q : ℝ} (hk : 0 < κ) (hmu : 1 ≤ mu)
    (hq : q < 1) (hd : |d| ≤ q * max a κ) :
    mu * (clippedLog κ (a + d) - clippedLog κ a + d / max a κ) ≤
      ((mu / max a κ) * |d|) ^ 2 / (1 - q) := by
  let t := max a κ
  let u := max (a + d) κ
  have ht : 0 < t := lt_of_lt_of_le hk (le_max_right _ _)
  have hu : 0 < u := lt_of_lt_of_le hk (le_max_right _ _)
  have hmu0 : 0 < mu := by linarith
  have hq0 : 0 < 1 - q := by linarith
  have hdiff : |u - t| ≤ |d| := by
    simpa only [add_sub_cancel_left] using abs_max_sub_max_le_abs (a + d) a κ
  have hden : (1 - q) * t ≤ mu * u := by
    have hh := (abs_le.mp hdiff).1
    have hm : u ≤ mu * u := by nlinarith only [hmu, hu.le]
    nlinarith only [hh, hd, hm]
  have hfrac : mu * (d ^ 2 / (t * u)) ≤ ((mu / t) * |d|) ^ 2 / (1 - q) := by
    have hmult := mul_le_mul_of_nonneg_right hden
      (show 0 ≤ mu * d ^ 2 * t by positivity)
    have hid : ((mu / t) * |d|) ^ 2 / (1 - q) =
        mu ^ 2 * d ^ 2 / (t ^ 2 * (1 - q)) := by
      rw [mul_pow, div_pow, sq_abs]
      field_simp
      <;> ring
    rw [hid, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < t * u) (by positivity : 0 < t ^ 2 * (1 - q))).mpr
    nlinarith only [hmult]
  exact (mul_le_mul_of_nonneg_left (clippedLog_remainder (a := a) (d := d) hk) hmu0.le).trans hfrac
end DecrAlmostLinearSSSP.Decremental
end s150
section s151
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma potential_remainder (b : Core) (active : Finset (Fin b.input.k))
    (p x : Fin b.input.n → ℝ) (q : ℝ) (hq : q < 1)
    (hnorm : norm b (capacity b active p) x ≤ q) :
    potential b active (fun v => p v + x v) - potential b active p -
      dot (gradient b (capacity b active p)) x ≤ q ^ 2 / (1 - q) := by
  classical
  let f := capacity b active p
  have hf (e : Edge b) : 0 < f e := capacity_pos b active p e
  have hterm (e : Edge b) : f e * |incidence b x e| ≤ norm b f x :=
    Finset.single_le_sum (fun d _ => mul_nonneg (hf d).le (abs_nonneg _)) (Finset.mem_univ e)
  have hdelta (e : Edge b) : |incidence b x e| ≤ q * max (slack b active p e) (kappa b) := by
    have hk := (core_kappa_bounds b).1
    have ht : 0 < max (slack b active p e) (kappa b) := lt_of_lt_of_le hk (le_max_right _ _)
    have hh := (hterm e).trans hnorm
    change (coefficient b e / max (slack b active p e) (kappa b)) * |incidence b x e| ≤ q at hh
    rw [div_mul_eq_mul_div] at hh
    have hm := (div_le_iff₀ ht).mp hh
    have hmu := (core_coefficient_bounds b e).1
    have hle : |incidence b x e| ≤ coefficient b e * |incidence b x e| := by
      nlinarith only [hmu, abs_nonneg (incidence b x e)]
    exact hle.trans hm
  have hpoint (e : Edge b) := weighted_clippedLog_remainder
    (a := slack b active p e) (d := incidence b x e) (q := q)
    (core_kappa_bounds b).1 (core_coefficient_bounds b e).1 hq (hdelta e)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun e _ => hpoint e
  have hslack (e : Edge b) : slack b active (fun v => p v + x v) e =
      slack b active p e + incidence b x e := by dsimp [slack, incidence]; ring
  have hleft : (∑ e, coefficient b e *
      (clippedLog (kappa b) (slack b active p e + incidence b x e) -
        clippedLog (kappa b) (slack b active p e) +
          incidence b x e / max (slack b active p e) (kappa b))) =
      potential b active (fun v => p v + x v) - potential b active p -
        dot (gradient b f) x := by
    rw [gradient_dot]
    simp only [potential, hslack, sub_neg_eq_add]
    simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp [f, capacity]
    ring
  rw [hleft] at hsum
  have hr : (∑ e, ((coefficient b e / max (slack b active p e) (kappa b)) * |incidence b x e|) ^ 2 / (1 - q)) =
      (∑ e, (f e * |incidence b x e|) ^ 2) / (1 - q) := by
    rw [Finset.sum_div]
    rfl
  rw [hr] at hsum
  have hsquares : (∑ e, (f e * |incidence b x e|) ^ 2) ≤ (norm b f x) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun e _ => mul_nonneg (hf e).le (abs_nonneg _))
  have hn0 : 0 ≤ norm b f x := Finset.sum_nonneg fun e _ => mul_nonneg (hf e).le (abs_nonneg _)
  have hsq : (norm b f x) ^ 2 ≤ q ^ 2 := by nlinarith only [hnorm, hn0]
  exact hsum.trans (div_le_div_of_nonneg_right (hsquares.trans hsq) (by linarith))
end DecrAlmostLinearSSSP.Decremental
end s151
section s152
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma sum_replace_two {n : ℕ} (f g : Fin n → ℕ) (a z : Fin n) (haz : a ≠ z)
    (heq : ∀ v, v ≠ a → v ≠ z → g v = f v) :
    (∑ v, g v) = (∑ v, f v) + g a + g z - f a - f z := by
  classical
  have hsum (f : Fin n → ℕ) : (∑ v, f v) =
      f a + f z + ∑ v ∈ (Finset.univ.erase a).erase z, f v := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)]
    rw [← Finset.add_sum_erase (Finset.univ.erase a) f (a := z) (by simp [haz.symm])]
    omega
  have hr : (∑ v ∈ (Finset.univ.erase a).erase z, g v) =
      ∑ v ∈ (Finset.univ.erase a).erase z, f v := by
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
    exact heq v hv.2 hv.1
  rw [hsum f, hsum g, hr]
  omega
lemma refresh_counter (b : Core) (s : State b) (e : Edge b)
    (hc : s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v)) :
    (refresh b s e).nonzeroEntries = ∑ v, nonzero ((refresh b s e).cachedGradient v) := by
  classical
  let a := tail b e
  let z := head b e
  let d := capacity b s.active (labels b s) e - s.cache e
  let g : Fin b.input.n → ℝ := fun v => s.cachedGradient v - (if v = a then d else 0) +
    (if v = z then d else 0)
  change (if a = z then s.nonzeroEntries else
    s.nonzeroEntries + nonzero (g a) + nonzero (g z) -
      nonzero (s.cachedGradient a) - nonzero (s.cachedGradient z)) = ∑ v, nonzero (g v)
  by_cases haz : a = z
  · rw [if_pos haz, hc]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [g]
    rw [haz]
    congr 1
    ring
  · rw [if_neg haz, hc]
    symm
    apply sum_replace_two _ _ a z haz
    intro v hva hvz
    simp only [g, if_neg hva, if_neg hvz, sub_zero, add_zero]
lemma attained_counter (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) :
    s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v) := by
  induction hs with
  | start => rfl
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · rw [repairStep, if_neg hstop]
      cases hp : s.pending with
      | nil =>
        simp only []
        split_ifs <;> exact ih
      | cons e es => exact refresh_counter b s e ih
  | @deletion s hs hstop e he ih => exact refresh_counter b _ (.inl e) ih
lemma zero_counter_gradient (b : Core) (s : State b)
    (hc : s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v))
    (hz : s.nonzeroEntries = 0) : s.cachedGradient = 0 := by
  funext v
  have hv : nonzero (s.cachedGradient v) ≤ ∑ w, nonzero (s.cachedGradient w) :=
    Finset.single_le_sum (f := fun w => nonzero (s.cachedGradient w)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  rw [← hc, hz] at hv
  change s.cachedGradient v = 0
  by_contra hne
  simp only [nonzero, if_neg hne] at hv
  omega
end DecrAlmostLinearSSSP.Decremental
end s152
section s153
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma actual_toggle_descent (b : Core) (K : ℝ) (hK : 32 ≤ K) (choose : State b → CutReply b)
    (hcut : CutQuality b K choose) (s : State b) (hs : Attained b K choose s)
    (hrunning : s.stopped = false) (hdrain : s.pending = []) (hnonzero : s.nonzeroEntries ≠ 0)
    (htest : (choose s).G / (choose s).U < -1 / (4 * K)) :
    potential b s.active (labels b s) -
      potential b (repairStep b K choose s).active (labels b (repairStep b K choose s)) ≥
        1 / (8 * K ^ 3) := by
  classical
  have hKpos : 0 < K := by linarith
  have hgrad : s.cachedGradient ≠ 0 := by
    intro hg
    have hc := attained_counter b K choose s hs
    rw [hg] at hc
    simp only [Pi.zero_apply, nonzero, if_true, Finset.sum_const_zero] at hc
    exact hnonzero hc
  let r := choose s
  have hqual := hcut s hs hdrain hgrad
  have hU : 0 < r.U := hqual.2.1
  let tau : ℝ := 1 / (K ^ 2 * r.U)
  let x := cutDirection r.cut tau
  let q : ℝ := 1 / (K ^ 2 - 1)
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hr := K_inverse_square_bound K hK
  obtain ⟨hqpos, hq1, herrornum, hremnum, hlast⟩ := toggle_numeric_bounds K hK
  obtain ⟨hedge, herror, hnorm⟩ := cache_accuracy b K hK choose hcut s hs hdrain
  have hxcache : norm b s.cache x ≤ 1 / K ^ 2 := by
    rw [← cachedPhysical_norm_eq, physical_norm_cut _ _ _ htau]
    have hh := mul_le_mul_of_nonneg_left hqual.2.2.2.1 htau
    have hid : tau * r.U = 1 / K ^ 2 := by dsimp [tau]; field_simp
    exact hh.trans hid.le
  have hx : norm b (capacity b s.active (labels b s)) x ≤ q := by
    have hh := (hnorm x).1.trans hxcache
    have hr1 : 0 < 1 - K ^ (-2 : ℤ) := by linarith only [hr.2]
    have hn : norm b (capacity b s.active (labels b s)) x ≤ (1 / K ^ 2) / (1 - K ^ (-2 : ℤ)) :=
      (le_div_iff₀ hr1).mpr (by simpa only [mul_comm] using hh)
    have hid : (1 / K ^ 2) / (1 - K ^ (-2 : ℤ)) = q := by
      dsimp [q]
      simp only [zpow_neg, zpow_ofNat, ← one_div]
      field_simp
      <;> ring
    exact hn.trans hid.le
  have hcx : dot s.cachedGradient x = tau * r.G := by
    rw [dot_cut]
    have hG : r.G = ∑ v ∈ r.cut, s.cachedGradient v := hqual.2.2.1
    rw [← hG]
  have htest' : tau * r.G ≤ -1 / (4 * K ^ 3) := by
    have hleft : tau * r.G = ((choose s).G / (choose s).U) / K ^ 2 := by
      dsimp [tau, r]
      field_simp
      <;> ring
    have hright : (-1 / (4 * K)) / K ^ 2 = -1 / (4 * K ^ 3) := by
      field_simp
      <;> ring
    rw [hleft, ← hright]
    exact div_le_div_of_nonneg_right htest.le (sq_nonneg K)
  have hslope : dot (gradient b (capacity b s.active (labels b s))) x ≤
      -1 / (4 * K ^ 3) + 2 / K ^ 4 := by
    have he := herror x
    rw [show dot (fun v => gradient b (capacity b s.active (labels b s)) v - s.cachedGradient v) x =
      dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x from
        by simp only [dot, sub_mul, Finset.sum_sub_distrib]] at he
    have hh := (abs_le.mp he).2
    have hmul := mul_le_mul_of_nonneg_left hx hr.1.le
    rw [hcx] at hh
    nlinarith only [hh, hmul, herrornum, htest']
  have hrem := potential_remainder b s.active (labels b s) x q hq1 hx
  have hstep : repairStep b K choose s = toggle b K s r := by
    simp only [repairStep, hrunning, Bool.false_eq_true, if_false, hdrain, hnonzero,
      freshReply, not_le.mpr htest, r]
  rw [hstep, toggle_potential]
  change potential b s.active (labels b s) - potential b s.active (fun v => labels b s v + x v) ≥ _
  dsimp [q] at hrem
  rw [neg_div] at hslope
  simp only [div_eq_mul_inv] at hrem hremnum hslope hlast ⊢
  nlinarith only [hrem, hremnum, hslope, hlast]
end DecrAlmostLinearSSSP.Decremental
end s153
section s154
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma cache_model_positive (b : Core) (s : State b) (e : Edge b) : 0 < cacheModel b s e := by
  have hmu := (core_coefficient_bounds b e).1
  have hk := (core_kappa_bounds b).1
  unfold cacheModel
  exact div_pos (by linarith) (lt_of_lt_of_le hk (le_max_right _ _))
lemma refresh_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K) (s : State b) (e : Edge b)
    (hmodel : ∀ d, d ≠ e → s.cache d = cacheModel b s d)
    (hgrad : s.cachedGradient = gradient b s.cache)
    (hdet : ∀ d, d ∉ s.pending →
      |s.cache d * (s.y (tail b d) - s.y (head b d) - s.baseline d)| < K ^ (-2 : ℤ)) :
    CacheInvariant b K (refresh b s e) := by
  classical
  constructor
  · intro d
    by_cases hd : d = e
    · subst d
      simp only [refresh, cacheModel, Function.update_self, capacity, slack, incidence, labels]
      congr 2
      ring
    · simpa only [refresh, cacheModel, Function.update_of_ne hd] using hmodel d hd
  · ext v
    change s.cachedGradient v - (if v = tail b e then capacity b s.active (labels b s) e - s.cache e else 0) +
      (if v = head b e then capacity b s.active (labels b s) e - s.cache e else 0) =
        gradient b (Function.update s.cache e (capacity b s.active (labels b s) e)) v
    rw [gradient_update, hgrad]
  · intro d hnot
    by_cases hd : d = e
    · subst d
      simp only [refresh, Function.update_self, sub_self, mul_zero, abs_zero]
      exact zpow_pos hK _
    · have hnot' : d ∉ s.pending := by
        intro hmem
        apply hnot
        simp only [refresh, List.mem_filter, decide_eq_true_eq]
        exact ⟨hmem, hd⟩
      simpa only [refresh, Function.update_of_ne hd] using hdet d hnot'
lemma initial_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K) :
    CacheInvariant b K (initializeState b) := by
  classical
  constructor
  · intro e
    simp only [initializeState, cacheModel, capacity, slack, incidence, Pi.zero_apply]
    congr 2
    ring
  · rfl
  · intro e _
    simp only [initializeState, Pi.zero_apply, sub_self, mul_zero, abs_zero]
    exact zpow_pos hK _
lemma toggle_cacheInvariant (b : Core) (K : ℝ) (s : State b) (r : CutReply b)
    (hs : CacheInvariant b K s) : CacheInvariant b K (toggle b K s r) := by
  classical
  refine ⟨hs.model, hs.gradient_eq, ?_⟩
  intro e he
  simpa only [toggle, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
    decide_eq_true_eq, not_le] using he
lemma delete_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K) (s : State b) (e : Fin b.input.k)
    (hs : CacheInvariant b K s) : CacheInvariant b K (deleteState b s e) := by
  classical
  apply refresh_cacheInvariant b K hK
  · intro d hd
    have hm := hs.model d
    cases d with
    | inl d =>
      have hde : d ≠ e := by simpa using hd
      simpa only [cacheModel, cost, Finset.mem_erase, hde, ne_eq, not_false_eq_true, true_and] using hm
    | inr d => exact hm
  · exact hs.gradient_eq
  · exact hs.detector
lemma attained_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K)
    (choose : State b → CutReply b) (s : State b) (hs : Attained b K choose s) :
    CacheInvariant b K s := by
  induction hs with
  | start => exact initial_cacheInvariant b K hK
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · rw [repairStep, if_neg hstop]
      cases hp : s.pending with
      | nil =>
        simp only []
        by_cases hz : s.nonzeroEntries = 0
        · rw [if_pos hz]
          refine ⟨ih.model, ih.gradient_eq, ?_⟩
          intro e _
          exact ih.detector e (by simp [hp])
        · rw [if_neg hz]
          by_cases ht : (choose s).G / (choose s).U ≥ -1 / (4 * K)
          · simp only [freshReply, ht, if_true]
            refine ⟨ih.model, ih.gradient_eq, ?_⟩
            intro e _
            exact ih.detector e (by simp [hp])
          · simp only [freshReply, ht, if_false]
            exact toggle_cacheInvariant b K s (choose s) ih
      | cons e es =>
        simp only []
        exact refresh_cacheInvariant b K hK s e (fun d _ => ih.model d) ih.gradient_eq ih.detector
  | deletion hs hstop e he ih => exact delete_cacheInvariant b K hK _ e ih
end DecrAlmostLinearSSSP.Decremental
end s154
section s155
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma clipped_capacity_comparison {mu κ old now r : ℝ}
    (hmu : 1 ≤ mu) (hk : 0 < κ)
    (hdrift : |(mu / max old κ) * (now - old)| ≤ r) :
    (1 - r) * (mu / max now κ) ≤ mu / max old κ ∧
      mu / max old κ ≤ (1 + r) * (mu / max now κ) := by
  let t := max old κ
  let u := max now κ
  have ht : 0 < t := lt_of_lt_of_le hk (le_max_right _ _)
  have hu : 0 < u := lt_of_lt_of_le hk (le_max_right _ _)
  have hmu0 : 0 < mu := by linarith
  have hdrift' : mu * |now - old| ≤ r * t := by
    have hh : mu / t * |now - old| ≤ r := by
      change |(mu / t) * (now - old)| ≤ r at hdrift
      rwa [abs_mul, abs_of_pos (div_pos hmu0 ht)] at hdrift
    rw [div_mul_eq_mul_div] at hh
    exact (div_le_iff₀ ht).mp hh
  have hdiff : |u - t| ≤ r * t := by
    calc
      |u - t| ≤ |now - old| := abs_max_sub_max_le_abs now old κ
      _ ≤ mu * |now - old| := by nlinarith [abs_nonneg (now - old)]
      _ ≤ r * t := hdrift'
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
  have hl : (1 - r) * t ≤ u := by linarith
  have hh : u ≤ (1 + r) * t := by linarith
  constructor
  · change (1 - r) * (mu / u) ≤ mu / t
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hu ht).mpr
    have h := mul_le_mul_of_nonneg_left hl hmu0.le
    nlinarith only [h]
  · change mu / t ≤ (1 + r) * (mu / u)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ ht hu).mpr
    have h := mul_le_mul_of_nonneg_left hh hmu0.le
    nlinarith only [h]
lemma cache_edge_comparison (b : Core) (K : ℝ) (s : State b)
    (hs : CacheInvariant b K s) (hdrain : s.pending = []) :
    ∀ e, (1 - K ^ (-2 : ℤ)) * capacity b s.active (labels b s) e ≤ s.cache e ∧
      s.cache e ≤ (1 + K ^ (-2 : ℤ)) * capacity b s.active (labels b s) e := by
  intro e
  let old := cost b s.active e + initialLabel b (tail b e) - initialLabel b (head b e) + s.baseline e
  have hdelta : slack b s.active (labels b s) e - old =
      s.y (tail b e) - s.y (head b e) - s.baseline e := by
    dsimp [slack, incidence, labels, old]
    ring
  have hd := (hs.detector e (by simp [hdrain])).le
  rw [hs.model e] at hd
  have hh := clipped_capacity_comparison (core_coefficient_bounds b e).1 (core_kappa_bounds b).1
    (old := old) (now := slack b s.active (labels b s) e) (r := K ^ (-2 : ℤ))
    (by simpa only [cacheModel, ← hdelta] using hd)
  simpa only [capacity, hs.model e, cacheModel] using hh
lemma gradient_sub (b : Core) (f g : Edge b → ℝ) :
    gradient b (fun e => f e - g e) = fun v => gradient b f v - gradient b g v := by
  classical
  funext v
  unfold gradient
  have hpoint (e : Edge b) :
      ((if head b e = v then f e - g e else 0) - (if tail b e = v then f e - g e else 0)) =
        ((if head b e = v then f e else 0) - (if tail b e = v then f e else 0)) -
        ((if head b e = v then g e else 0) - (if tail b e = v then g e else 0)) := by
    split_ifs <;> ring
  simp_rw [hpoint, Finset.sum_sub_distrib]
lemma gradient_norm_comparison (b : Core) (f g : Edge b → ℝ) (r : ℝ)
    (hedge : ∀ e, (1 - r) * f e ≤ g e ∧ g e ≤ (1 + r) * f e) :
    (∀ x, |dot (fun v => gradient b f v - gradient b g v) x| ≤ r * norm b f x) ∧
    (∀ x, (1 - r) * norm b f x ≤ norm b g x ∧ norm b g x ≤ (1 + r) * norm b f x) := by
  classical
  constructor
  · intro x
    rw [← gradient_sub, gradient_dot, abs_neg]
    have habs (e : Edge b) : |f e - g e| ≤ r * f e := by
      exact abs_le.mpr ⟨by nlinarith [(hedge e).2], by nlinarith [(hedge e).1]⟩
    calc
      |∑ e, (f e - g e) * incidence b x e| ≤ ∑ e, |(f e - g e) * incidence b x e| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e, r * (f e * |incidence b x e|) := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_right (habs e) (abs_nonneg (incidence b x e))
        nlinarith only [hh]
      _ = r * norm b f x := by rw [← Finset.mul_sum]; rfl
  · intro x
    constructor
    · unfold norm
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      have hh := mul_le_mul_of_nonneg_right (hedge e).1 (abs_nonneg (incidence b x e))
      nlinarith only [hh]
    · unfold norm
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      have hh := mul_le_mul_of_nonneg_right (hedge e).2 (abs_nonneg (incidence b x e))
      nlinarith only [hh]
end DecrAlmostLinearSSSP.Decremental
end s155
section s156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma invariant_cache_accuracy (b : Core) (K : ℝ) (s : State b)
    (hi : CacheInvariant b K s) (hdrain : s.pending = []) :
    (∀ e, (1-K^(-2 : ℤ))*capacity b s.active (labels b s) e ≤ s.cache e ∧
      s.cache e ≤ (1+K^(-2 : ℤ))*capacity b s.active (labels b s) e) ∧
    (∀ x, |dot (fun v => gradient b (capacity b s.active (labels b s)) v-s.cachedGradient v) x| ≤
      K^(-2 : ℤ)*norm b (capacity b s.active (labels b s)) x) ∧
    (∀ x, (1-K^(-2 : ℤ))*norm b (capacity b s.active (labels b s)) x ≤ norm b s.cache x ∧
      norm b s.cache x ≤ (1+K^(-2 : ℤ))*norm b (capacity b s.active (labels b s)) x) := by
  have he := cache_edge_comparison b K s hi hdrain
  have hg := gradient_norm_comparison b (capacity b s.active (labels b s)) s.cache (K^(-2 : ℤ)) he
  refine ⟨he,?_,hg.2⟩
  intro x
  simpa only [hi.gradient_eq] using hg.1 x
end DecrAlmostLinearSSSP.Decremental
end s156
section s157
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma invariant_toggle_descent (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (s : State b) (hi : CacheInvariant b K s) (hdrain : s.pending = [])
    (r : CutReply b) (hqual : RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut)
    (htest : r.G / r.U < -1/(4*K)) :
    potential b s.active (labels b s)-potential b (toggle b K s r).active (labels b (toggle b K s r)) ≥
      1/(8*K^3) := by
  classical
  have hKpos : 0 < K := by linarith
  have hU : 0 < r.U := hqual.2.1
  let tau : ℝ := 1 / (K ^ 2 * r.U)
  let x := cutDirection r.cut tau
  let q : ℝ := 1 / (K ^ 2 - 1)
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hr := K_inverse_square_bound K hK
  obtain ⟨hqpos, hq1, herrornum, hremnum, hlast⟩ := toggle_numeric_bounds K hK
  obtain ⟨hedge, herror, hnorm⟩ := invariant_cache_accuracy b K s hi hdrain
  have hxcache : norm b s.cache x ≤ 1 / K ^ 2 := by
    rw [← cachedPhysical_norm_eq, physical_norm_cut _ _ _ htau]
    have hh := mul_le_mul_of_nonneg_left hqual.2.2.2.1 htau
    have hid : tau * r.U = 1 / K ^ 2 := by dsimp [tau]; field_simp
    exact hh.trans hid.le
  have hx : norm b (capacity b s.active (labels b s)) x ≤ q := by
    have hh := (hnorm x).1.trans hxcache
    have hr1 : 0 < 1 - K ^ (-2 : ℤ) := by linarith only [hr.2]
    have hn : norm b (capacity b s.active (labels b s)) x ≤ (1 / K ^ 2) / (1 - K ^ (-2 : ℤ)) :=
      (le_div_iff₀ hr1).mpr (by simpa only [mul_comm] using hh)
    have hid : (1 / K ^ 2) / (1 - K ^ (-2 : ℤ)) = q := by
      dsimp [q]
      simp only [zpow_neg, zpow_ofNat, ← one_div]
      field_simp
      <;> ring
    exact hn.trans hid.le
  have hcx : dot s.cachedGradient x = tau * r.G := by
    rw [dot_cut]
    have hG : r.G = ∑ v ∈ r.cut, s.cachedGradient v := hqual.2.2.1
    rw [← hG]
  have htest' : tau * r.G ≤ -1 / (4 * K ^ 3) := by
    have hleft : tau * r.G = (r.G / r.U) / K ^ 2 := by
      dsimp [tau]
      field_simp
      <;> ring
    have hright : (-1 / (4 * K)) / K ^ 2 = -1 / (4 * K ^ 3) := by
      field_simp
      <;> ring
    rw [hleft, ← hright]
    exact div_le_div_of_nonneg_right htest.le (sq_nonneg K)
  have hslope : dot (gradient b (capacity b s.active (labels b s))) x ≤
      -1 / (4 * K ^ 3) + 2 / K ^ 4 := by
    have he := herror x
    rw [show dot (fun v => gradient b (capacity b s.active (labels b s)) v - s.cachedGradient v) x =
      dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x from
        by simp only [dot, sub_mul, Finset.sum_sub_distrib]] at he
    have hh := (abs_le.mp he).2
    have hmul := mul_le_mul_of_nonneg_left hx hr.1.le
    rw [hcx] at hh
    nlinarith only [hh, hmul, herrornum, htest']
  have hrem := potential_remainder b s.active (labels b s) x q hq1 hx
  rw [toggle_potential]
  change potential b s.active (labels b s) - potential b s.active (fun v => labels b s v + x v) ≥ _
  dsimp [q] at hrem
  rw [neg_div] at hslope
  simp only [div_eq_mul_inv] at hrem hremnum hslope hlast ⊢
  nlinarith only [hrem, hremnum, hslope, hlast]
end DecrAlmostLinearSSSP.Decremental
end s157
section s158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma reportedToggle_cacheInvariant (b : Core) (K : ℝ) (s : State b) (r : CutReply b)
    (reports : List (Edge b)) (hs : CacheInvariant b K s)
    (hcomplete : ReportsComplete b K s r reports) : CacheInvariant b K (reportedToggle b K s r reports) := by
  refine ⟨hs.model,hs.gradient_eq,?_⟩
  intro e he
  exact lt_of_not_ge (fun hh => he (hcomplete e hh))
lemma reportedToggle_descent (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (s : State b) (hi : CacheInvariant b K s) (hdrain : s.pending = [])
    (r : CutReply b) (hqual : RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut)
    (htest : r.G/r.U < -1/(4*K)) (reports : List (Edge b)) :
    potential b s.active (labels b s)-
      potential b (reportedToggle b K s r reports).active (labels b (reportedToggle b K s r reports)) ≥ 1/(8*K^3) :=
  invariant_toggle_descent b K hK s hi hdrain r hqual htest
end DecrAlmostLinearSSSP.Decremental
end s158
section s159
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma refresh_sample_baseline (b : Core) (s : State b) (e : Edge b)
    (hs : ∀ v : ReturnVertex b, s.sample v.val = initialLabel b v.val + s.baseline (.inr v)) :
    ∀ v : ReturnVertex b, (refresh b s e).sample v.val =
      initialLabel b v.val + (refresh b s e).baseline (.inr v) := by
  classical
  intro v
  cases e with
  | inl e =>
    have he : (Sum.inr v : Edge b) ≠ Sum.inl e := by intro h; cases h
    simpa only [refresh, Function.update_of_ne he] using hs v
  | inr w =>
    by_cases hv : v = w
    · subst w
      simp only [refresh, Function.update_self, labels, tail, head]
      ring
    · have hval : v.val ≠ w.val := fun h => hv (Subtype.ext h)
      have he : (Sum.inr v : Edge b) ≠ Sum.inr w := fun h => hv (Sum.inr.inj h)
      simpa only [refresh, Function.update_of_ne hval, Function.update_of_ne he] using hs v
lemma attained_sample_baseline (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) :
    ∀ v : ReturnVertex b, s.sample v.val = initialLabel b v.val + s.baseline (.inr v) := by
  induction hs with
  | start => intro v; simp [initializeState]
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · rw [repairStep, if_neg hstop]
      cases hp : s.pending with
      | nil =>
        simp only []
        split_ifs <;> exact ih
      | cons e es => exact refresh_sample_baseline b s e ih
  | @deletion s hs hstop e he ih => exact refresh_sample_baseline b _ (.inl e) ih
lemma core_A_accuracy (b : Core) : 32 ≤ A b * b.input.accuracy := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have he := b.valid.2.2.2.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 1 ≤ logarithm2 (b.input.size + 1) := by
    unfold logarithm2
    apply (le_div_iff₀ hlog2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ b.input.size + 1)
  have ha : 32 * logarithm2 (b.input.size + 1) / b.input.accuracy ≤ A b := Nat.le_ceil _
  have hh := (div_le_iff₀ he).mp ha
  nlinarith
lemma attained_stopped_drained (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) : Stable b s → s.pending = [] := by
  induction hs with
  | start => simp [Stable, initializeState]
  | @repair s hs ih =>
    intro hstable
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih hstop
    · change (repairStep b K choose s).stopped = true at hstable
      cases hp : s.pending with
      | nil =>
        by_cases hz : s.nonzeroEntries = 0
        · simp only [repairStep, if_neg hstop, hp, if_pos hz]
        · by_cases ht : (choose s).G / (choose s).U ≥ -1 / (4 * K)
          · simp only [repairStep, if_neg hstop, hp, if_neg hz, freshReply, if_pos ht]
          · simp only [repairStep, if_neg hstop, hp, if_neg hz, freshReply, if_neg ht, toggle] at hstable
            exact False.elim (hstop hstable)
      | cons e es =>
        simp only [repairStep, if_neg hstop, hp, refresh] at hstable
        exact False.elim (hstop hstable)
  | @deletion s hs hstop e he ih => simp [Stable, deleteState, refresh]
end DecrAlmostLinearSSSP.Decremental
end s159
section s160
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma refresh_output_sample (b : Core) (s : State b) (e : Edge b)
    (hs : ∀ v, s.output v = if v = b.input.source then 0 else readout b (s.sample v)) :
    ∀ v, (refresh b s e).output v =
      if v = b.input.source then 0 else readout b ((refresh b s e).sample v) := by
  classical
  intro v
  cases e with
  | inl e => exact hs v
  | inr w =>
    by_cases hv : v = w.val
    · subst v
      simp only [refresh,Function.update_self,if_neg w.property]
    · simpa only [refresh,Function.update_of_ne hv] using hs v
lemma attained_output_sample (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) :
    ∀ v, s.output v = if v = b.input.source then 0 else readout b (s.sample v) := by
  induction hs with
  | start => intro v; rfl
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep,if_pos hstop] using ih
    · rw [repairStep,if_neg hstop]
      cases hp : s.pending with
      | nil => simp only []; split_ifs <;> exact ih
      | cons e es => exact refresh_output_sample b s e ih
  | @deletion s hs hstop e he ih => exact refresh_output_sample b _ (.inl e) ih
end DecrAlmostLinearSSSP.Decremental
end s160
section s161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma indegree_le_count (b : Core) (v : Fin b.input.n) :
    indegree b v ≤ ∑ e : Fin b.input.k, if b.input.graph.head e = v then 1 else 0 := by
  classical
  unfold indegree
  split_ifs with hv
  · exact Nat.zero_le _
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
lemma return_indegree_sum (b : Core) :
    (∑ v : ReturnVertex b, indegree b v.val) ≤ b.input.k := by
  classical
  let R : Finset (Fin b.input.n) := Finset.univ.filter (fun v => v ≠ b.input.source)
  have hsum : (∑ v : ReturnVertex b, indegree b v.val) = ∑ v ∈ R, indegree b v := by
    exact (Finset.sum_subtype R (by intro v; simp [R]) (indegree b)).symm
  rw [hsum]
  calc
    (∑ v ∈ R, indegree b v) ≤ ∑ v : Fin b.input.n, indegree b v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun _ _ _ => Nat.zero_le _)
    _ ≤ ∑ v : Fin b.input.n, ∑ e : Fin b.input.k, if b.input.graph.head e = v then 1 else 0 :=
      Finset.sum_le_sum fun v _ => indegree_le_count b v
    _ = b.input.k := by rw [Finset.sum_comm]; simp
lemma coefficient_sum_sharp (b : Core) :
    (∑ e, coefficient b e) ≤ 2 * A b * b.input.size := by
  have hq : (∑ v : ReturnVertex b, (indegree b v.val : ℝ)) ≤ b.input.size := by
    exact_mod_cast (return_indegree_sum b).trans b.valid.2.1
  have hk : (b.input.k : ℝ) ≤ b.input.size := by exact_mod_cast b.valid.2.1
  have hA := core_A_ge b
  have hm : (0 : ℝ) ≤ b.input.size := Nat.cast_nonneg _
  rw [Fintype.sum_sum_type]
  simp only [coefficient, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ A b by linarith)
  nlinarith
lemma core_cost_lower (b : Core) (active : Finset (Fin b.input.k)) (e : Fin b.input.k) :
    1 / Q b ≤ cost b active (.inl e) := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hw : (1 : ℝ) ≤ b.input.W := by exact_mod_cast b.valid.2.2.1
  have hQ : 0 < Q b := by have := core_Q_ge b; linarith
  have hH : 1 ≤ H b := by dsimp [H]; nlinarith [mul_le_mul hn hw (by norm_num) (by linarith)]
  simp only [cost]
  split_ifs
  · apply div_le_div_of_nonneg_right _ hQ.le
    exact_mod_cast (b.valid.2.2.2.2.2 e).1
  · exact div_le_div_of_nonneg_right hH hQ.le
lemma kappa_le_initial_slack (b : Core) : kappa b ≤ 1 / (2 * Q b) := by
  have hA := core_A_ge b
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ := core_Q_ge b
  have hQpos : 0 < Q b := by linarith
  have hAm : 1 ≤ A b * b.input.size := by nlinarith
  have hbig : 2 * Q b ≤ (A b * b.input.size * Q b) ^ 2 := by
    have hh : 2 ≤ A b * b.input.size * Q b := by nlinarith
    have hhi : Q b ≤ A b * b.input.size * Q b := by nlinarith
    nlinarith
  simp only [kappa, zpow_neg, zpow_ofNat, ← one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < (A b * b.input.size * Q b) ^ 2) (by positivity : 0 < 2 * Q b)).mpr
  simpa only [one_mul] using hbig
lemma initial_slack_lower (b : Core) (e : Edge b) :
    1 / (2 * Q b) ≤ slack b Finset.univ (initialLabel b) e := by
  have hQpos : 0 < Q b := by
    have hQ := core_Q_ge b
    have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
    linarith
  cases e with
  | inl e =>
    have hc := core_cost_lower b Finset.univ e
    have hhead := b.no_incoming_source e
    by_cases htail : b.input.graph.tail e = b.input.source
    · have heq : slack b Finset.univ (initialLabel b) (.inl e) =
          cost b Finset.univ (.inl e) - 1 / (2 * Q b) := by
        simp [slack, incidence, tail, head, initialLabel, hhead, htail] <;> ring
      rw [heq]
      have hid : 1 / (2 * Q b) + 1 / (2 * Q b) = 1 / Q b := by ring
      linarith
    · have heq : slack b Finset.univ (initialLabel b) (.inl e) = cost b Finset.univ (.inl e) := by
        simp [slack, incidence, tail, head, initialLabel, hhead, htail] <;> ring
      rw [heq]
      have hh : 1 / (2 * Q b) ≤ 1 / Q b := by apply div_le_div_of_nonneg_left (by norm_num) hQpos; linarith
      exact hh.trans hc
  | inr v => simp [slack, cost, incidence, tail, head, initialLabel, v.property]
end DecrAlmostLinearSSSP.Decremental
end s161
section s162
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma initial_potential_upper (b : Core) :
    potential b Finset.univ (initialLabel b) ≤
      2 * A b * b.input.size * Real.log (2 * Q b) := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ : 4 * (b.input.n : ℝ) ≤ Q b := core_Q_ge b
  have hQpos : 0 < Q b := by linarith
  have hlog : 0 ≤ Real.log (2 * Q b) := Real.log_nonneg (by linarith)
  have hpoint (e : Edge b) : clippedLog (kappa b) (slack b Finset.univ (initialLabel b) e) ≤
      Real.log (2 * Q b) := by
    have hl := initial_slack_lower b e
    have hk := (kappa_le_initial_slack b).trans hl
    rw [clippedLog, if_pos hk]
    have hh := Real.log_le_log (by positivity : 0 < 1 / (2 * Q b)) hl
    rw [one_div, Real.log_inv] at hh
    linarith
  calc
    potential b Finset.univ (initialLabel b) ≤ ∑ e, coefficient b e * Real.log (2 * Q b) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hpoint e) (by have := (core_coefficient_bounds b e).1; linarith)
    _ = (∑ e, coefficient b e) * Real.log (2 * Q b) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (coefficient_sum_sharp b) hlog
lemma clippedLog_antitone {κ a b : ℝ} (hk : 0 < κ) (hab : a ≤ b) :
    clippedLog κ b ≤ clippedLog κ a := by
  have hh := clippedLog_secant_upper (a := a) (b := b) hk
  have hr : (a - b) / max b κ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hab)
    (le_trans hk.le (le_max_right _ _))
  linarith
lemma cost_erase_ge (b : Core) (active : Finset (Fin b.input.k)) (e : Fin b.input.k) (d : Edge b) :
    cost b active d ≤ cost b (active.erase e) d := by
  classical
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hw : (1 : ℝ) ≤ b.input.W := by exact_mod_cast b.valid.2.2.1
  have hQpos : 0 < Q b := by have := core_Q_ge b; linarith
  cases d with
  | inr v => rfl
  | inl d =>
    by_cases hd : d = e
    · subst d
      have herase : cost b (active.erase e) (.inl e) = H b / Q b := by simp [cost]
      rw [herase]
      by_cases he : e ∈ active
      · rw [cost, if_pos he]
        apply div_le_div_of_nonneg_right _ hQpos.le
        have hweight : (b.input.weight e : ℝ) ≤ b.input.W := by exact_mod_cast (b.valid.2.2.2.2.2 e).2
        dsimp [H]
        nlinarith
      · simp [cost, he]
    · simp [cost, Finset.mem_erase, hd]
lemma deleted_potential_le (b : Core) (s : State b) (e : Fin b.input.k) :
    potential b (deleteState b s e).active (labels b (deleteState b s e)) ≤
      potential b s.active (labels b s) := by
  classical
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ coefficient b d by
    have := (core_coefficient_bounds b d).1; linarith)
  apply clippedLog_antitone (core_kappa_bounds b).1
  change cost b s.active d + incidence b (labels b s) d ≤
    cost b (s.active.erase e) d + incidence b (labels b s) d
  linarith only [cost_erase_ge b s.active e d]
end DecrAlmostLinearSSSP.Decremental
end s162
section s163
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma attained_energy (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (choose : State b → CutReply b) (hcut : CutQuality b K choose)
    (s : State b) (hs : Attained b K choose s) :
    potential b s.active (labels b s) + (s.toggles : ℝ) * (1 / (8 * K ^ 3)) ≤
      potential b Finset.univ (initialLabel b) := by
  classical
  induction hs with
  | start =>
    have hl : labels b (initializeState b) = initialLabel b := by
      funext v
      simp [labels, initializeState]
    rw [hl]
    simp [initializeState]
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · cases hp : s.pending with
      | cons e es =>
        simp only [repairStep, if_neg hstop, hp]
        change potential b s.active (labels b s) + (s.toggles : ℝ) * (1 / (8 * K ^ 3)) ≤ _
        exact ih
      | nil =>
        by_cases hz : s.nonzeroEntries = 0
        · simp only [repairStep, if_neg hstop, hp, if_pos hz]
          change potential b s.active (labels b s) + (s.toggles : ℝ) * (1 / (8 * K ^ 3)) ≤ _
          exact ih
        · by_cases ht : (choose s).G / (choose s).U ≥ -1 / (4 * K)
          · simp only [repairStep, if_neg hstop, hp, if_neg hz, freshReply, if_pos ht]
            change potential b s.active (labels b s) + (s.toggles : ℝ) * (1 / (8 * K ^ 3)) ≤ _
            exact ih
          · have hf : s.stopped = false := Bool.eq_false_iff.mpr hstop
            have hd := toggle_descent b K hK choose hcut s hs hf hp hz (lt_of_not_ge ht)
            have hcount : (repairStep b K choose s).toggles = s.toggles + 1 := by
              simp only [repairStep, if_neg hstop, hp, if_neg hz, freshReply, if_neg ht, toggle]
            rw [hcount, Nat.cast_add, Nat.cast_one]
            linarith
  | @deletion s hs hstop e he ih =>
    have hd := deleted_potential_le b s e
    change potential b (deleteState b s e).active (labels b (deleteState b s e)) +
      (s.toggles : ℝ) * (1 / (8 * K ^ 3)) ≤ _
    linarith
lemma attained_toggle_count (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (choose : State b → CutReply b) (hcut : CutQuality b K choose)
    (s : State b) (hs : Attained b K choose s) :
    (s.toggles : ℝ) ≤ 16 * K ^ 3 * A b * b.input.size * Real.log (2 * Q b) := by
  have hKpos : 0 < K := by linarith
  have he := attained_energy b K hK choose hcut s hs
  have hi := initial_potential_upper b
  have hl := potential_lower_bound b s.active (labels b s) (by simp [labels, initialLabel])
  have hh : (s.toggles : ℝ) / (8 * K ^ 3) ≤
      2 * A b * b.input.size * Real.log (2 * Q b) := by
    rw [div_eq_mul_one_div]
    linarith only [he, hi, hl]
  have hb := (div_le_iff₀ (by positivity : 0 < 8 * K ^ 3)).mp hh
  nlinarith only [hb]
end DecrAlmostLinearSSSP.Decremental
end s163
section s164
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma RuntimeInvariant.initial (b : Core) (K : ℝ) (hK : 0 < K) :
    RuntimeInvariant b K (initializeState b) := by
  refine ⟨initial_cacheInvariant b K hK,rfl,?_,?_,?_⟩
  · intro v; simp [initializeState]
  · intro v; rfl
  · have hh : labels b (initializeState b) = initialLabel b := by
      funext v; simp [labels,initializeState]
    rw [hh]
    simp [initializeState]
lemma RuntimeInvariant.refresh (b : Core) (K : ℝ) (hK : 0 < K) (s : State b)
    (hs : RuntimeInvariant b K s) (e : Edge b) : RuntimeInvariant b K (refresh b s e) := by
  refine ⟨refresh_cacheInvariant b K hK s e (fun d _ => hs.cache.model d) hs.cache.gradient_eq hs.cache.detector,
    refresh_counter b s e hs.counter,refresh_sample_baseline b s e hs.sample,
    refresh_output_sample b s e hs.output,hs.energy⟩
lemma RuntimeInvariant.delete (b : Core) (K : ℝ) (hK : 0 < K) (s : State b)
    (hs : RuntimeInvariant b K s) (e : Fin b.input.k) : RuntimeInvariant b K (deleteState b s e) := by
  refine ⟨delete_cacheInvariant b K hK s e hs.cache,
    refresh_counter b _ (.inl e) hs.counter,refresh_sample_baseline b _ (.inl e) hs.sample,
    refresh_output_sample b _ (.inl e) hs.output,?_⟩
  have hh := deleted_potential_le b s e
  change potential b (deleteState b s e).active (labels b (deleteState b s e)) +
    (s.toggles : ℝ)*(1/(8*K^3)) ≤ _
  linarith only [hh,hs.energy]
lemma RuntimeInvariant.toggle (b : Core) (K : ℝ) (hK : 32 ≤ K) (s : State b)
    (hs : RuntimeInvariant b K s) (hdrain : s.pending = []) (r : CutReply b)
    (hqual : RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut)
    (htest : r.G/r.U < -1/(4*K)) (reports : List (Edge b))
    (hcomplete : ReportsComplete b K s r reports) : RuntimeInvariant b K (reportedToggle b K s r reports) := by
  refine ⟨reportedToggle_cacheInvariant b K s r reports hs.cache hcomplete,
    hs.counter,hs.sample,hs.output,?_⟩
  have hh := reportedToggle_descent b K hK s hs.cache hdrain r hqual htest reports
  change potential b (reportedToggle b K s r reports).active (labels b (reportedToggle b K s r reports))+
    ((s.toggles+1 : ℕ) : ℝ)*(1/(8*K^3)) ≤ _
  rw [Nat.cast_add,Nat.cast_one]
  linarith only [hh,hs.energy]
end DecrAlmostLinearSSSP.Decremental
end s164
section s165
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma RuntimeInvariant.toggle_count (b : Core) (K : ℝ) (hKpos : 0 < K)
    (s : State b) (hs : RuntimeInvariant b K s) :
    (s.toggles : ℝ) ≤ 16*K^3*A b*b.input.size*Real.log (2*Q b) := by
  have he := hs.energy
  have hi := initial_potential_upper b
  have hl := potential_lower_bound b s.active (labels b s) (by simp [labels, initialLabel])
  have hh : (s.toggles : ℝ) / (8 * K ^ 3) ≤
      2 * A b * b.input.size * Real.log (2 * Q b) := by
    rw [div_eq_mul_one_div]
    linarith only [he, hi, hl]
  have hb := (div_le_iff₀ (by positivity : 0 < 8 * K ^ 3)).mp hh
  nlinarith only [hb]
end DecrAlmostLinearSSSP.Decremental
end s165
section s166
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma RuntimeInvariant.toggles_lt_limit (b : Core) (K : ℝ) (hK : 0 < K)
    (s : State b) (hs : RuntimeInvariant b K s) : s.toggles < repairLimit b K := by
  have hh := hs.toggle_count b K hK s
  have hc := Nat.le_ceil (16*K^3*A b*b.input.size*Real.log (2*Q b))
  have ht : s.toggles ≤ ⌈16*K^3*A b*b.input.size*Real.log (2*Q b)⌉₊ := by exact_mod_cast hh.trans hc
  exact Nat.lt_succ_of_le ht
lemma runtimeRank_refresh (b : Core) (K : ℝ) (s : State b) (e : Edge b) (es : List (Edge b))
    (hstop : s.stopped = false) (hp : s.pending = e::es) :
    Prod.Lex Nat.lt Nat.lt (runtimeRepairRank b K (refresh b s e)) (runtimeRepairRank b K s) := by
  have hlen : (refresh b s e).pending.length ≤ es.length := by
    change (s.pending.filter (fun d => d ≠ e)).length ≤ es.length
    rw [hp]
    simp only [List.filter_cons,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,if_false]
    exact List.length_filter_le _ _
  have hsame : (refresh b s e).stopped = false := hstop
  simp only [runtimeRepairRank,hstop,hsame,Bool.false_eq_true,if_false]
  apply Prod.Lex.right
  change (refresh b s e).pending.length+1 < s.pending.length+1
  rw [hp]
  simp only [List.length_cons]
  omega
lemma runtimeRank_toggle (b : Core) (K : ℝ) (hK : 0 < K) (s : State b)
    (hs : RuntimeInvariant b K s) (hstop : s.stopped = false)
    (r : CutReply b) (reports : List (Edge b)) :
    Prod.Lex Nat.lt Nat.lt (runtimeRepairRank b K (reportedToggle b K s r reports)) (runtimeRepairRank b K s) := by
  have ht := hs.toggles_lt_limit b K hK s
  have hsame : (reportedToggle b K s r reports).stopped = false := hstop
  simp only [runtimeRepairRank,hstop,hsame,Bool.false_eq_true,if_false]
  apply Prod.Lex.left
  change repairLimit b K-(s.toggles+1)+1 < repairLimit b K-s.toggles+1
  omega
lemma runtimeRank_stop (b : Core) (K : ℝ) (s : State b) (hstop : s.stopped = false) :
    Prod.Lex Nat.lt Nat.lt (runtimeRepairRank b K {s with stopped := true}) (runtimeRepairRank b K s) := by
  simpa [runtimeRepairRank,hstop] using
    (Prod.Lex.left (ra := Nat.lt) (rb := Nat.lt) (0 : ℕ) (s.pending.length+1) (Nat.zero_lt_succ (repairLimit b K-s.toggles)))
lemma runtimeRank_wellFounded (b : Core) (K : ℝ) :
    WellFounded (InvImage (Prod.Lex Nat.lt Nat.lt) (runtimeRepairRank b K)) :=
  InvImage.wf _ (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
end DecrAlmostLinearSSSP.Decremental
end s166
section s167
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma sample_accuracy_of_drift {p sample κ mu eps r : ℝ}
    (hk : 0 < κ) (hp : κ < p) (hmu : 0 < mu)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hmueps : 32 ≤ mu * eps) (hr : r ≤ 1)
    (hdrift : |(mu / max sample κ) * (p - sample)| ≤ r) :
    (1 - eps / 8) * p ≤ sample ∧ sample ≤ (1 + eps / 8) * p := by
  let w := |p - sample|
  have hw : 0 ≤ w := abs_nonneg _
  have ht : 0 < max sample κ := lt_of_lt_of_le hk (le_max_right _ _)
  have hbound : mu * w ≤ max sample κ := by
    have hd : mu / max sample κ * w ≤ r := by
      simpa only [abs_mul, abs_of_pos (div_pos hmu ht)] using hdrift
    rw [div_mul_eq_mul_div] at hd
    have hh := (div_le_iff₀ ht).mp hd
    have hh' := mul_le_mul_of_nonneg_right hr ht.le
    linarith
  have hm : max sample κ ≤ p + w := by
    apply max_le
    · have hh := neg_le_abs (p - sample)
      dsimp [w]
      linarith
    · linarith
  have h1 := mul_le_mul_of_nonneg_right hmueps hw
  have h2 := mul_le_mul_of_nonneg_left (hbound.trans hm) heps.le
  have h3 := mul_le_mul_of_nonneg_right heps1 hw
  have hw' : w ≤ (eps / 8) * p := by nlinarith only [h1, h2, h3, hw]
  obtain ⟨hl, hu⟩ := abs_le.mp hw'
  constructor <;> linarith
lemma return_accuracy (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (choose : State b → CutReply b) (hcut : CutQuality b K choose)
    (s : State b) (hs : Attained b K choose s) (hstable : Stable b s) :
    ∀ v, v ≠ b.input.source →
      (1 - b.input.accuracy / 8) * labels b s v ≤ s.sample v ∧
      s.sample v ≤ (1 + b.input.accuracy / 8) * labels b s v := by
  intro v hv
  let r : ReturnVertex b := ⟨v, hv⟩
  have hi := attained_cacheInvariant b K (by linarith : 0 < K) choose s hs
  have hsample := attained_sample_baseline b K choose s hs r
  have hdrain := attained_stopped_drained b K choose s hs hstable
  have hsource : labels b s b.input.source = 0 := by simp [labels, initialLabel]
  have hpositive := (stable_labels b K hK choose hcut s hs hstable).2.1 (.inr r)
  simp only [slack, cost, incidence, tail, head, hsource, sub_zero, zero_add] at hpositive
  have hcache : s.cache (.inr r) =
      (A b * indegree b v) / max (s.sample v) (kappa b) := by
    rw [hi.model]
    unfold cacheModel
    simp only [coefficient, cost, tail, head]
    have hsrc : initialLabel b b.input.source = 0 := by simp [initialLabel]
    rw [hsrc, zero_add, sub_zero, ← hsample]
  have hdelta : s.y v - s.y b.input.source - s.baseline (.inr r) = labels b s v - s.sample v := by
    rw [hsample]
    dsimp [labels]
    ring
  have hd := (hi.detector (.inr r) (by simp [hdrain])).le
  simp only [tail, head] at hd
  rw [hcache, hdelta] at hd
  have hq : (1 : ℝ) ≤ indegree b v := by exact_mod_cast core_indegree_pos b v hv
  have hA := core_A_ge b
  have hAeps := core_A_accuracy b
  have heps := b.valid.2.2.2.1
  have hmu : 0 < A b * indegree b v := by positivity
  have hmueps : 32 ≤ (A b * indegree b v) * b.input.accuracy := by
    have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ A b * b.input.accuracy by positivity)
    nlinarith only [hh, hAeps]
  exact sample_accuracy_of_drift (core_kappa_bounds b).1 hpositive hmu heps b.valid.2.2.2.2.1
    hmueps ((K_inverse_square_bound K hK).2.trans (by norm_num)) hd
end DecrAlmostLinearSSSP.Decremental
end s167
section s168
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma cached_physical_norm (b : Core) (s : State b) (x : Fin b.input.n → ℝ) :
    physicalNorm (cachedPhysical b s) x = norm b s.cache x := by
  classical
  simp only [physicalNorm, cachedPhysical, norm]
  exact Equiv.sum_comp (Fintype.equivFin (Edge b)).symm (fun e : Edge b => s.cache e * |incidence b x e|)
lemma dot_neg_right {n : ℕ} (g x : Fin n → ℝ) :
    dot g (fun v => -x v) = -dot g x := by
  simp only [dot, mul_neg, Finset.sum_neg_distrib]
lemma dot_sub_left {n : ℕ} (f g x : Fin n → ℝ) :
    dot (fun v => f v - g v) x = dot f x - dot g x := by
  simp only [dot, sub_mul, Finset.sum_sub_distrib]
lemma norm_neg (b : Core) (f : Edge b → ℝ) (x : Fin b.input.n → ℝ) :
    norm b f (fun v => -x v) = norm b f x := by
  simp only [norm, incidence, neg_sub_neg, abs_sub_comm]
lemma gradient_abs_le_norm (b : Core) (f : Edge b → ℝ) (hf : ∀ e, 0 ≤ f e)
    (x : Fin b.input.n → ℝ) : |dot (gradient b f) x| ≤ norm b f x := by
  rw [gradient_dot, abs_neg]
  calc
    |∑ e, f e * incidence b x e| ≤ ∑ e, |f e * incidence b x e| := Finset.abs_sum_le_sum_abs _ _
    _ = norm b f x := by simp only [abs_mul, abs_of_nonneg (hf _), norm]
lemma ratio_direction_lower {K N G U d : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hstop : -1 / (4 * K) ≤ G / U) (hbound : G / U ≤ (d / N) / K) :
    -N / 4 ≤ d := by
  have hh := (le_div_iff₀ hK).mp (hstop.trans hbound)
  have hid : (-1 / (4 * K)) * K = -(1 / 4 : ℝ) := by field_simp <;> ring
  rw [hid] at hh
  have hh' := (le_div_iff₀ hN).mp hh
  nlinarith only [hh']
lemma stopping_balance (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (choose : State b → CutReply b) (hcut : CutQuality b K choose)
    (s : State b) (hs : Attained b K choose s) (hdrain : s.pending = [])
    (hstop : s.cachedGradient = 0 ∨ ∃ r : CutReply b,
      RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut ∧ -1 / (4 * K) ≤ r.G / r.U) :
    Balanced b s.active (labels b s) := by
  have hKpos : 0 < K := by linarith
  have hr := K_inverse_square_bound K hK
  have hcache := attained_cacheInvariant b K hKpos choose s hs
  obtain ⟨hedge, herror, hnorm⟩ := cache_accuracy b K hK choose hcut s hs hdrain
  have hcache0 (e : Edge b) : 0 ≤ s.cache e := by
    have hf := capacity_pos b s.active (labels b s) e
    have hh := (hedge e).1
    nlinarith
  have hnorm0 (x : Fin b.input.n → ℝ) : 0 ≤ norm b s.cache x :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hcache0 e) (abs_nonneg _)
  have hcached (x : Fin b.input.n → ℝ) :
      |dot s.cachedGradient x| ≤ (1 / 4 : ℝ) * norm b s.cache x := by
    rcases hstop with hz | ⟨r, hqual, hstop⟩
    · simp only [hz, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, abs_zero]
      exact mul_nonneg (by norm_num) (hnorm0 x)
    · by_cases hn : 0 < norm b s.cache x
      · have hp := hqual.2.2.2.2 x (by rwa [cached_physical_norm])
        have hm := hqual.2.2.2.2 (fun v => -x v) (by rwa [cached_physical_norm, norm_neg])
        rw [cached_physical_norm] at hp hm
        change r.G / r.U ≤ (dot s.cachedGradient x / norm b s.cache x) / K at hp
        change r.G / r.U ≤ (dot s.cachedGradient (fun v => -x v) / norm b s.cache (fun v => -x v)) / K at hm
        have hp' := ratio_direction_lower hKpos hn hstop hp
        simp only [dot_neg_right, norm_neg] at hm
        have hm' := ratio_direction_lower hKpos hn hstop hm
        exact abs_le.mpr ⟨by linarith only [hp'], by linarith only [hm']⟩
      · have habs := gradient_abs_le_norm b s.cache hcache0 x
        rw [← hcache.gradient_eq] at habs
        have hz : norm b s.cache x = 0 := le_antisymm (not_lt.mp hn) (hnorm0 x)
        rw [hz] at habs ⊢
        simpa only [mul_zero] using habs
  intro x _
  have herr := herror x
  rw [dot_sub_left] at herr
  have ht := hcached x
  have hupper := (hnorm x).2
  have hnf : 0 ≤ norm b (capacity b s.active (labels b s)) x :=
    Finset.sum_nonneg fun e _ => mul_nonneg (capacity_pos b s.active (labels b s) e).le (abs_nonneg _)
  have hcoef : K ^ (-2 : ℤ) + (1 + K ^ (-2 : ℤ)) / 4 ≤ (1 / 3 : ℝ) := by linarith only [hr.2]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef hnf
  have htri : |dot (gradient b (capacity b s.active (labels b s))) x| ≤
      |dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x| +
        |dot s.cachedGradient x| := by
    simpa only [sub_add_cancel] using abs_add_le
      (dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x) (dot s.cachedGradient x)
  nlinarith only [herr, ht, hupper, hcoef', htri]
end DecrAlmostLinearSSSP.Decremental
end s168
section s169
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma invariant_stopping_balance (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (s : State b) (hcache : CacheInvariant b K s) (hdrain : s.pending = [])
    (hstop : s.cachedGradient = 0 ∨ ∃ r : CutReply b,
      RatioGuarantee (cachedPhysical b s) K r.G r.U r.cut ∧ -1 / (4 * K) ≤ r.G / r.U) :
    Balanced b s.active (labels b s) := by
  have hKpos : 0 < K := by linarith
  have hr := K_inverse_square_bound K hK
  obtain ⟨hedge, herror, hnorm⟩ := invariant_cache_accuracy b K s hcache hdrain
  have hcache0 (e : Edge b) : 0 ≤ s.cache e := by
    have hf := capacity_pos b s.active (labels b s) e
    have hh := (hedge e).1
    nlinarith
  have hnorm0 (x : Fin b.input.n → ℝ) : 0 ≤ norm b s.cache x :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hcache0 e) (abs_nonneg _)
  have hcached (x : Fin b.input.n → ℝ) :
      |dot s.cachedGradient x| ≤ (1 / 4 : ℝ) * norm b s.cache x := by
    rcases hstop with hz | ⟨r, hqual, hstop⟩
    · simp only [hz, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, abs_zero]
      exact mul_nonneg (by norm_num) (hnorm0 x)
    · by_cases hn : 0 < norm b s.cache x
      · have hp := hqual.2.2.2.2 x (by rwa [cached_physical_norm])
        have hm := hqual.2.2.2.2 (fun v => -x v) (by rwa [cached_physical_norm, norm_neg])
        rw [cached_physical_norm] at hp hm
        change r.G / r.U ≤ (dot s.cachedGradient x / norm b s.cache x) / K at hp
        change r.G / r.U ≤ (dot s.cachedGradient (fun v => -x v) / norm b s.cache (fun v => -x v)) / K at hm
        have hp' := ratio_direction_lower hKpos hn hstop hp
        simp only [dot_neg_right, norm_neg] at hm
        have hm' := ratio_direction_lower hKpos hn hstop hm
        exact abs_le.mpr ⟨by linarith only [hp'], by linarith only [hm']⟩
      · have habs := gradient_abs_le_norm b s.cache hcache0 x
        rw [← hcache.gradient_eq] at habs
        have hz : norm b s.cache x = 0 := le_antisymm (not_lt.mp hn) (hnorm0 x)
        rw [hz] at habs ⊢
        simpa only [mul_zero] using habs
  intro x _
  have herr := herror x
  rw [dot_sub_left] at herr
  have ht := hcached x
  have hupper := (hnorm x).2
  have hnf : 0 ≤ norm b (capacity b s.active (labels b s)) x :=
    Finset.sum_nonneg fun e _ => mul_nonneg (capacity_pos b s.active (labels b s) e).le (abs_nonneg _)
  have hcoef : K ^ (-2 : ℤ) + (1 + K ^ (-2 : ℤ)) / 4 ≤ (1 / 3 : ℝ) := by linarith only [hr.2]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef hnf
  have htri : |dot (gradient b (capacity b s.active (labels b s))) x| ≤
      |dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x| +
        |dot s.cachedGradient x| := by
    simpa only [sub_add_cancel] using abs_add_le
      (dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x) (dot s.cachedGradient x)
  nlinarith only [herr, ht, hupper, hcoef', htri]
end DecrAlmostLinearSSSP.Decremental
end s169
section s170
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma invariant_return_accuracy (b : Core) (K : ℝ) (hK : 32 ≤ K) (s : State b)
    (hi : CacheInvariant b K s) (hdrain : s.pending = [])
    (hsample : ∀ v : ReturnVertex b, s.sample v.val = initialLabel b v.val+s.baseline (.inr v))
    (hall : AllTarget b s.active (labels b s)) :
    ∀ v, v ≠ b.input.source →
      (1-b.input.accuracy/8)*labels b s v ≤ s.sample v ∧
      s.sample v ≤ (1+b.input.accuracy/8)*labels b s v := by
  intro v hv
  let r : ReturnVertex b := ⟨v, hv⟩
  have hsample := hsample r
  have hsource : labels b s b.input.source = 0 := by simp [labels, initialLabel]
  have hpositive := hall.1 (.inr r)
  simp only [slack, cost, incidence, tail, head, hsource, sub_zero, zero_add] at hpositive
  have hcache : s.cache (.inr r) =
      (A b * indegree b v) / max (s.sample v) (kappa b) := by
    rw [hi.model]
    unfold cacheModel
    simp only [coefficient, cost, tail, head]
    have hsrc : initialLabel b b.input.source = 0 := by simp [initialLabel]
    rw [hsrc, zero_add, sub_zero, ← hsample]
  have hdelta : s.y v - s.y b.input.source - s.baseline (.inr r) = labels b s v - s.sample v := by
    rw [hsample]
    dsimp [labels]
    ring
  have hd := (hi.detector (.inr r) (by simp [hdrain])).le
  simp only [tail, head] at hd
  rw [hcache, hdelta] at hd
  have hq : (1 : ℝ) ≤ indegree b v := by exact_mod_cast core_indegree_pos b v hv
  have hA := core_A_ge b
  have hAeps := core_A_accuracy b
  have heps := b.valid.2.2.2.1
  have hmu : 0 < A b * indegree b v := by positivity
  have hmueps : 32 ≤ (A b * indegree b v) * b.input.accuracy := by
    have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ A b * b.input.accuracy by positivity)
    nlinarith only [hh, hAeps]
  exact sample_accuracy_of_drift (core_kappa_bounds b).1 hpositive hmu heps b.valid.2.2.2.2.1
    hmueps ((K_inverse_square_bound K hK).2.trans (by norm_num)) hd
end DecrAlmostLinearSSSP.Decremental
end s170
section s171
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s171
section s172
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma coreLength_pos (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (e : Fin b.input.k) : 0 < coreLength b active p e :=
  lt_of_lt_of_le (core_kappa_bounds b).1 (le_max_right _ _)
lemma core_label_edge_bound (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (e : Fin b.input.k) : p (b.input.graph.tail e) - p (b.input.graph.head e) ≤ coreLength b active p e := by
  have hh : slack b active p (.inl e) ≤ coreLength b active p e := le_max_left _ _
  have hc := (core_cost_bounds b active e).1
  dsimp [slack, incidence, tail, head] at hh
  linarith
lemma coreDistance_lower (b : Core) (active : Finset (Fin b.input.k))
    (v : Fin b.input.n) (hv : v ≠ b.input.source) :
    ENNReal.ofReal (1 / Q b) ≤ coreDistance b active v := by
  classical
  unfold coreDistance distance
  apply le_iInf
  intro es
  apply le_iInf
  intro he
  rw [list_sum_ofReal _ (fun e => (core_cost_bounds b active e).1)]
  apply ENNReal.ofReal_le_ofReal
  have hne : es ≠ [] := by
    intro hh
    exact hv (he.eq_of_empty hh).symm
  cases es with
  | nil => exact False.elim (hne rfl)
  | cons e fs =>
    simp only [List.map_cons, List.sum_cons]
    have hr : 0 ≤ (fs.map (fun e => cost b active (.inl e))).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; exact (core_cost_bounds b active d).1)
    linarith [core_cost_lower b active e]
lemma coreDistance_ell_walk (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0)
    (t : Fin b.input.n) (es : List (Fin b.input.k)) (he : Walk b.input.graph Finset.univ b.input.source t es) :
    coreDistance b active t ≤ ENNReal.ofReal (p t + (es.map (coreLength b active p)).sum) := by
  have hcost := distance_le_walk he (fun e => ENNReal.ofReal (cost b active (.inl e)))
  rw [list_sum_ofReal _ (fun e => (core_cost_bounds b active e).1)] at hcost
  have ht : (es.map (fun e => slack b active p (.inl e))).sum =
      (es.map (fun e => cost b active (.inl e))).sum + p b.input.source - p t := by
    simp only [slack, incidence, tail, head]
    rw [List.sum_map_add, he.cost_telescope p]
    ring
  have hsum : (es.map (fun e => slack b active p (.inl e))).sum ≤
      (es.map (coreLength b active p)).sum := List.sum_le_sum (fun e _ => le_max_left _ _)
  rw [hs] at ht
  exact hcost.trans (ENNReal.ofReal_le_ofReal (by linarith only [ht, hsum]))
end DecrAlmostLinearSSSP.Decremental
end s172
section s173
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s173
section s174
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s174
section s175
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s175
section s176
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s176
section s177
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s177
section s178
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s178
section s179
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s179
section s180
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s180
section s181
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s181
section s182
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s182
section s183
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s183
section s184
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s184
section s185
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s185
section s186
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s186
section s187
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s187
section s188
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSetup
open Structured
open RegisterSave
end DecrAlmostLinearSSSP.Decremental.SourceSetup
end s188
section s189
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s189
section s190
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s190
section s191
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace RegisterSave
end RegisterSave
namespace SourceSetup
end SourceSetup
end DecrAlmostLinearSSSP.Decremental
end s191
section s192
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSnapshot
open Structured
open RegisterSave
end DecrAlmostLinearSSSP.Decremental.SourceSnapshot
end s192
section s193
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceCall
end s193
section s194
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s194
section s195
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s195
section s196
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s196
section s197
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s197
section s198
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s198
section s199
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s199
section s200
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CorePending
end s200
section s201
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s201
section s202
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end s202
section s203
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s203
section s204
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRecord
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRecord
end s204
section s205
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress
end s205
section s206
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient
end s206
section s207
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDegree
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreDegree
end s207
section s208
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s208
section s209
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s209
section s210
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s210
section s211
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s211
section s212
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s212
section s213
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s213
section s214
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s214
section s215
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDegree
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreDegree
end s215
section s216
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreTape
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreTape
end s216
section s217
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialDifference
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialDifference
end s217
section s218
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s218
section s219
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s219
section s220
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s220
section s221
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s221
section s222
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s222
section s223
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s223
section s224
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s224
section s225
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Clear
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Clear
end s225
section s226
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s226
section s227
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s227
section s228
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Adjacency
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s228
section s229
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end s229
section s230
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s230
section s231
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s231
section s232
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s232
section s233
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end s233
section s234
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s234
section s235
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end s235
section s236
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end s236
section s237
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s237
section s238
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end s238
section s239
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s239
section s240
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s240
section s241
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s241
section s242
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRecord
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRecord
end s242
section s243
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreOutput
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreOutput
end s243
section s244
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreOutput
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreOutput
end s244
section s245
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReturn
end s245
section s246
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s246
section s247
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNonzero
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNonzero
end s247
section s248
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradient
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradient
end s248
section s249
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradient
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreGradient
end s249
section s250
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
end s250
section s251
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
end s251
section s252
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s252
section s253
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s253
section s254
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s254
section s255
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end s255
section s256
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end s256
section s257
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s257
section s258
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s258
section s259
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s259
section s260
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s260
section s261
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end s261
section s262
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s262
section s263
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s263
section s264
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s264
section s265
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s265
section s266
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s266
section s267
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s267
section s268
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end s268
section s269
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeStore
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeStore
end s269
section s270
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions
end s270
section s271
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s271
section s272
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s272
section s273
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s273
section s274
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s274
section s275
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s275
section s276
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s276
section s277
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s277
section s278
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
namespace DecrAlmostLinearSSSP.Decremental.CorePending
end DecrAlmostLinearSSSP.Decremental.CorePending
end s278
section s279
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CorePending
end s279
section s280
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
end DecrAlmostLinearSSSP.Decremental.CorePending
end s280
section s281
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s281
section s282
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s282
section s283
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s283
section s284
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s284
section s285
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s285
section s286
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s286
section s287
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s287
section s288
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s288
section s289
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s289
section s290
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s290
section s291
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s291
section s292
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s292
section s293
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s293
section s294
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s294
section s295
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s295
section s296
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s296
section s297
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s297
section s298
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s298
section s299
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s299
section s300
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s300
section s301
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s301
section s302
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s302
section s303
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s303
section s304
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s304
section s305
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s305
section s306
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s306
section s307
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s307
section s308
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s308
section s309
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s309
section s310
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s310
section s311
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s311
section s312
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s312
section s313
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s313
section s314
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s314
section s315
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s315
section s316
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s316
section s317
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s317
section s318
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s318
section s319
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s319
section s320
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s320
section s321
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s321
section s322
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s322
section s323
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s323
section s324
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
end s324
section s325
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end s325
section s326
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s326
section s327
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s327
section s328
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
end s328
section s329
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s329
section s330
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s330
section s331
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s331
section s332
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s332
section s333
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s333
section s334
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s334
section s335
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s335
section s336
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s336
section s337
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s337
section s338
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s338
section s339
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s339
section s340
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
end s340
section s341
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s341
section s342
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s342
section s343
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s343
section s344
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s344
section s345
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s345
section s346
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s346
section s347
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s347
section s348
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s348
section s349
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s349
section s350
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s350
section s351
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s351
section s352
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s352
section s353
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s353
section s354
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s354
section s355
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s355
section s356
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRatioGuard
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRatioGuard
end s356
section s357
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s357
section s358
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s358
section s359
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s359
section s360
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s360
section s361
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s361
section s362
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
end s362
section s363
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s363
section s364
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s364
section s365
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
end s365
section s366
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepairControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRepairControl
end s366
section s367
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s367
section s368
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s368
section s369
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s369
section s370
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s370
section s371
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s371
section s372
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s372
section s373
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s373
section s374
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s374
section s375
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s375
section s376
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s376
section s377
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s377
section s378
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s378
section s379
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s379
section s380
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s380
section s381
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s381
section s382
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s382
section s383
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s383
section s384
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s384
section s385
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s385
section s386
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s386
section s387
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s387
section s388
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s388
section s389
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s389
section s390
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s390
section s391
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s391
section s392
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s392
section s393
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s393
section s394
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreQuality
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreQuality
end s394
section s395
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s395
section s396
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCeiling
end s396
section s397
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCeiling
end s397
section s398
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s398
section s399
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s399
section s400
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s400
section s401
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s401
section s402
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
end s402
section s403
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
end s403
section s404
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
end s404
section s405
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s405
section s406
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s406
section s407
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s407
section s408
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s408
section s409
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s409
section s410
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s410
section s411
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s411
section s412
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s412
section s413
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s413
section s414
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Fill
open Structured
end DecrAlmostLinearSSSP.Decremental.Fill
end s414
section s415
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SnapshotFill
open Structured
end DecrAlmostLinearSSSP.Decremental.SnapshotFill
end s415
section s416
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s416
section s417
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s417
section s418
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s418
section s419
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s419
section s420
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s420
section s421
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s421
section s422
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s422
section s423
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s423
section s424
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s424
section s425
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s425
section s426
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s426
section s427
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s427
section s428
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s428
section s429
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s429
section s430
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s430
section s431
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s431
section s432
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s432
section s433
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s433
section s434
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s434
section s435
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s435
section s436
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s436
section s437
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s437
section s438
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s438
section s439
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s439
section s440
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s440
section s441
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s441
section s442
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s442
theorem solution : (((((((∀ (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HPow.hPow.{0, 0, 0} Real Int Real
          (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
      (@LE.le.{0} Real Real.instLE
        (@HPow.hPow.{0, 0, 0} Real Int Real
          (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 1024)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.capacity b active p e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (t : Real) (v : Fin b.input.n),
  @Eq.{1} Real
    (DecrAlmostLinearSSSP.Decremental.gradient b
      (@Function.update.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (fun a => Real)
        (fun a b_1 =>
          @instDecidableEqSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
            (instDecidableEqFin b.input.k) (DecrAlmostLinearSSSP.Decremental.instDecidableEqReturnVertex b) a b_1)
        f e t)
      v)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.gradient b f v)
        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) t (f e))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.head b e))
        (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.head b e))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) t (f e))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real)
  (x : Fin b.input.n → Real),
  @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.dot b.input.n (DecrAlmostLinearSSSP.Decremental.gradient b f) x)
    (@Neg.neg.{0} Real Real.instNeg
      (∑ e,
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (f e)
          (DecrAlmostLinearSSSP.Decremental.incidence b x e)))))) ∧ (((∀ {n k : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k) (C : Finset.{0} (Fin n)) (tau : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tau →
    @Eq.{1} Real
      (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k h (@DecrAlmostLinearSSSP.Decremental.cutDirection n C tau))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) tau
        (@DecrAlmostLinearSSSP.Decremental.cutCapacity n k h C))) ∧ (∀ {n : Nat} (g : Fin n → Real) (C : Finset.{0} (Fin n)) (tau : Real),
  @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.dot n g (@DecrAlmostLinearSSSP.Decremental.cutDirection n C tau))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) tau (∑ v ∈ C, g v)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (x : Fin b.input.n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) x)
    (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
  @Eq.{1} Real
    (DecrAlmostLinearSSSP.Decremental.potential b
      (@DecrAlmostLinearSSSP.Decremental.State.active b (DecrAlmostLinearSSSP.Decremental.toggle b K s r))
      (DecrAlmostLinearSSSP.Decremental.labels b (DecrAlmostLinearSSSP.Decremental.toggle b K s r)))
    (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s) fun v =>
      @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (DecrAlmostLinearSSSP.Decremental.labels b s v)
        (@DecrAlmostLinearSSSP.Decremental.cutDirection b.input.n (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))
          v))) ∧ (∀ (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (And
            (@LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
            (@LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))))))) ∧ ((((∀ {κ a b : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.clippedLog κ b) (DecrAlmostLinearSSSP.Decremental.clippedLog κ a))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) a b)
        (@Max.max.{0} Real Real.instMax b κ))) ∧ (∀ {κ a d : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (DecrAlmostLinearSSSP.Decremental.clippedLog κ
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a d))
          (DecrAlmostLinearSSSP.Decremental.clippedLog κ a))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d
          (@Max.max.{0} Real Real.instMax a κ)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) d
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Max.max.{0} Real Real.instMax a κ)
          (@Max.max.{0} Real Real.instMax (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a d)
            κ))))) ∧ ((∀ {κ a d mu q : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) mu →
      @LT.lt.{0} Real Real.instLT q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup d)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) q
              (@Max.max.{0} Real Real.instMax a κ)) →
          @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) mu
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (DecrAlmostLinearSSSP.Decremental.clippedLog κ
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a d))
                  (DecrAlmostLinearSSSP.Decremental.clippedLog κ a))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d
                  (@Max.max.{0} Real Real.instMax a κ))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                    (@Max.max.{0} Real Real.instMax a κ))
                  (@abs.{0} Real Real.lattice Real.instAddGroup d))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) q))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p x : Fin b.input.n → Real)
  (q : Real),
  @LT.lt.{0} Real Real.instLT q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @LE.le.{0} Real Real.instLE
        (DecrAlmostLinearSSSP.Decremental.norm b (DecrAlmostLinearSSSP.Decremental.capacity b active p) x) q →
      @LE.le.{0} Real Real.instLE
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (DecrAlmostLinearSSSP.Decremental.potential b active fun v =>
              @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p v) (x v))
            (DecrAlmostLinearSSSP.Decremental.potential b active p))
          (@DecrAlmostLinearSSSP.Decremental.dot b.input.n
            (DecrAlmostLinearSSSP.Decremental.gradient b (DecrAlmostLinearSSSP.Decremental.capacity b active p)) x))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) q
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) q))))) ∧ (((∀ {n : Nat} (f g : Fin n → Nat) (a z : Fin n),
  @Ne.{1} (Fin n) a z →
    (∀ (v : Fin n), @Ne.{1} (Fin n) v a → @Ne.{1} (Fin n) v z → @Eq.{1} Nat (g v) (f v)) →
      @Eq.{1} Nat (∑ v, g v)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (∑ v, f v) (g a)) (g z))
            (f a))
          (f z))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
      (∑ v, DecrAlmostLinearSSSP.Decremental.nonzero (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v)) →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b (DecrAlmostLinearSSSP.Decremental.refresh b s e))
      (∑ v,
        DecrAlmostLinearSSSP.Decremental.nonzero
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b (DecrAlmostLinearSSSP.Decremental.refresh b s e) v)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
      (∑ v, DecrAlmostLinearSSSP.Decremental.nonzero (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
      (∑ v, DecrAlmostLinearSSSP.Decremental.nonzero (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v)) →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
      DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
          DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
            @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
              @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                  (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
                  (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LT.lt.{0} Real Real.instLT
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.G b (choose s))
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.U b (choose s)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Neg.neg.{0} Real Real.instNeg
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 4)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                          K)) →
                    @GE.ge.{0} Real Real.instLE
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (DecrAlmostLinearSSSP.Decremental.potential b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                          (DecrAlmostLinearSSSP.Decremental.labels b s))
                        (DecrAlmostLinearSSSP.Decremental.potential b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b
                            (DecrAlmostLinearSSSP.Decremental.repairStep b K choose s))
                          (DecrAlmostLinearSSSP.Decremental.labels b
                            (DecrAlmostLinearSSSP.Decremental.repairStep b K choose s))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 8)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.cacheModel b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      (∀ (d : DecrAlmostLinearSSSP.Decremental.Edge b),
          @Ne.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) d e →
            @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.State.cache b s d)
              (DecrAlmostLinearSSSP.Decremental.cacheModel b s d)) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
            (DecrAlmostLinearSSSP.Decremental.gradient b (@DecrAlmostLinearSSSP.Decremental.State.cache b s)) →
          (∀ d ∉ @DecrAlmostLinearSSSP.Decremental.State.pending b s,
              @LT.lt.{0} Real Real.instLT
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@DecrAlmostLinearSSSP.Decremental.State.cache b s d)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@DecrAlmostLinearSSSP.Decremental.State.y b s (DecrAlmostLinearSSSP.Decremental.tail b d))
                        (@DecrAlmostLinearSSSP.Decremental.State.y b s (DecrAlmostLinearSSSP.Decremental.head b d)))
                      (@DecrAlmostLinearSSSP.Decremental.State.baseline b s d))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))) →
            DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.refresh b s e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.toggle b K s r)))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.deleteState b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
      (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.Attained b K choose s → DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s)) ∧ ((∀ {mu κ old now r : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) mu →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
      @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                (@Max.max.{0} Real Real.instMax old κ))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) now old)))
          r →
        And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                (@Max.max.{0} Real Real.instMax now κ)))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
              (@Max.max.{0} Real Real.instMax old κ)))
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
              (@Max.max.{0} Real Real.instMax old κ))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                (@Max.max.{0} Real Real.instMax now κ))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
        And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (DecrAlmostLinearSSSP.Decremental.labels b s) e))
            (@DecrAlmostLinearSSSP.Decremental.State.cache b s e))
          (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (DecrAlmostLinearSSSP.Decremental.labels b s) e)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f g : DecrAlmostLinearSSSP.Decremental.Edge b → Real),
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.gradient b fun e =>
      @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (f e) (g e))
    fun v =>
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (DecrAlmostLinearSSSP.Decremental.gradient b f v) (DecrAlmostLinearSSSP.Decremental.gradient b g v)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f g : DecrAlmostLinearSSSP.Decremental.Edge b → Real) (r : Real),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      And
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
            (f e))
          (g e))
        (@LE.le.{0} Real Real.instLE (g e)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
            (f e)))) →
    And
      (∀ (x : Fin b.input.n → Real),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@DecrAlmostLinearSSSP.Decremental.dot b.input.n
              (fun v =>
                @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (DecrAlmostLinearSSSP.Decremental.gradient b f v) (DecrAlmostLinearSSSP.Decremental.gradient b g v))
              x))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r
            (DecrAlmostLinearSSSP.Decremental.norm b f x)))
      (∀ (x : Fin b.input.n → Real),
        And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (DecrAlmostLinearSSSP.Decremental.norm b f x))
            (DecrAlmostLinearSSSP.Decremental.norm b g x))
          (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.norm b g x)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (DecrAlmostLinearSSSP.Decremental.norm b f x))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      And
        (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          And
            (@LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e))
              (@DecrAlmostLinearSSSP.Decremental.State.cache b s e))
            (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e))))
        (And
          (∀ (x : Fin b.input.n → Real),
            @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@DecrAlmostLinearSSSP.Decremental.dot b.input.n
                  (fun v =>
                    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (DecrAlmostLinearSSSP.Decremental.gradient b
                        (DecrAlmostLinearSSSP.Decremental.capacity b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                          (DecrAlmostLinearSSSP.Decremental.labels b s))
                        v)
                      (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v))
                  x))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (DecrAlmostLinearSSSP.Decremental.norm b
                  (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                    (DecrAlmostLinearSSSP.Decremental.labels b s))
                  x)))
          (∀ (x : Fin b.input.n → Real),
            And
              (@LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                  (DecrAlmostLinearSSSP.Decremental.norm b
                    (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s))
                    x))
                (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x))
              (@LE.le.{0} Real Real.instLE
                (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                  (DecrAlmostLinearSSSP.Decremental.norm b
                    (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s))
                    x))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
            @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                    (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r) (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r) →
              @LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)) →
                @GE.ge.{0} Real Real.instLE
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s))
                    (DecrAlmostLinearSSSP.Decremental.potential b
                      (@DecrAlmostLinearSSSP.Decremental.State.active b
                        (DecrAlmostLinearSSSP.Decremental.toggle b K s r))
                      (DecrAlmostLinearSSSP.Decremental.labels b (DecrAlmostLinearSSSP.Decremental.toggle b K s r))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 8)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b) (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s r reports →
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K
        (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
            @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                    (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r) (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r) →
              @LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)) →
                ∀ (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  @GE.ge.{0} Real Real.instLE
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                        (DecrAlmostLinearSSSP.Decremental.labels b s))
                      (DecrAlmostLinearSSSP.Decremental.potential b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b
                          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports))
                        (DecrAlmostLinearSSSP.Decremental.labels b
                          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
      @Eq.{1} Real
        (@DecrAlmostLinearSSSP.Decremental.State.sample b s
          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.initialLabel b
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b s
            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) →
    ∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
      @Eq.{1} Real
        (@DecrAlmostLinearSSSP.Decremental.State.sample b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.initialLabel b
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    ∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
      @Eq.{1} Real
        (@DecrAlmostLinearSSSP.Decremental.State.sample b s
          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.initialLabel b
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b s
            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (DecrAlmostLinearSSSP.Decremental.A b)
      b.input.accuracy)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    DecrAlmostLinearSSSP.Decremental.Stable b s →
      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  (∀ (v : Fin b.input.n),
      @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
        (@ite.{1} ENNReal (@Eq.{1} (Fin b.input.n) v b.input.source) (instDecidableEqFin b.input.n v b.input.source)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
          (DecrAlmostLinearSSSP.Decremental.readout b (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)))) →
    ∀ (v : Fin b.input.n),
      @Eq.{1} ENNReal
        (@DecrAlmostLinearSSSP.Decremental.State.output b (DecrAlmostLinearSSSP.Decremental.refresh b s e) v)
        (@ite.{1} ENNReal (@Eq.{1} (Fin b.input.n) v b.input.source) (instDecidableEqFin b.input.n v b.input.source)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
          (DecrAlmostLinearSSSP.Decremental.readout b
            (@DecrAlmostLinearSSSP.Decremental.State.sample b (DecrAlmostLinearSSSP.Decremental.refresh b s e) v)))))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    ∀ (v : Fin b.input.n),
      @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
        (@ite.{1} ENNReal (@Eq.{1} (Fin b.input.n) v b.input.source) (instDecidableEqFin b.input.n v b.input.source)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
          (DecrAlmostLinearSSSP.Decremental.readout b (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : Fin b.input.n),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.indegree b v)
    (∑ e,
      @ite.{1} Nat
        (@Eq.{1} (Fin b.input.n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e) v)
        (instDecidableEqFin b.input.n
          (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e) v)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat
    (∑ v,
      DecrAlmostLinearSSSP.Decremental.indegree b
        (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
    b.input.k) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (∑ e, DecrAlmostLinearSSSP.Decremental.coefficient b e)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.A b))
      (@Nat.cast.{0} Real Real.instNatCast b.input.size))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (DecrAlmostLinearSSSP.Decremental.Q b))
    (DecrAlmostLinearSSSP.Decremental.cost b active
      (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.kappa b)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.Q b)))
    (DecrAlmostLinearSSSP.Decremental.slack b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
      (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
      (DecrAlmostLinearSSSP.Decremental.initialLabel b))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.A b))
        (@Nat.cast.{0} Real Real.instNatCast b.input.size))
      (Real.log
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (∀ {κ a b : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE a b →
      @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.clippedLog κ b)
        (DecrAlmostLinearSSSP.Decremental.clippedLog κ a)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k)
  (d : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.cost b active d)
    (DecrAlmostLinearSSSP.Decremental.cost b (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k) active e)
      d)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
  @LE.le.{0} Real Real.instLE
    (DecrAlmostLinearSSSP.Decremental.potential b
      (@DecrAlmostLinearSSSP.Decremental.State.active b (DecrAlmostLinearSSSP.Decremental.deleteState b s e))
      (DecrAlmostLinearSSSP.Decremental.labels b (DecrAlmostLinearSSSP.Decremental.deleteState b s e)))
    (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
      (DecrAlmostLinearSSSP.Decremental.labels b s)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
      DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
          DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
            @LE.le.{0} Real Real.instLE
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 8)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
              (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                (DecrAlmostLinearSSSP.Decremental.initialLabel b))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
      DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
          DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
            @LE.le.{0} Real Real.instLE
              (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 16)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (DecrAlmostLinearSSSP.Decremental.A b))
                  (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                (Real.log
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.refresh b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        ∀ (e : Fin b.input.k),
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.deleteState b s e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
            @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                    (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r) (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r) →
              @LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)) →
                ∀ (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s r reports →
                    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (DecrAlmostLinearSSSP.Decremental.A b))
              (@Nat.cast.{0} Real Real.instNatCast b.input.size))
            (Real.log
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LT.lt.{0} Nat instLTNat (@DecrAlmostLinearSSSP.Decremental.State.toggles b s)
          (DecrAlmostLinearSSSP.Decremental.repairLimit b K))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (es : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e es) →
      @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt
        (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K (DecrAlmostLinearSSSP.Decremental.refresh b s e))
        (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b)
            (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
            @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt
              (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K
                (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports))
              (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
    @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt
      (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K
        (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
          (@DecrAlmostLinearSSSP.Decremental.State.y b s) (@DecrAlmostLinearSSSP.Decremental.State.cache b s)
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
          (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
          (@DecrAlmostLinearSSSP.Decremental.State.pending b s) Bool.true
          (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) (@DecrAlmostLinearSSSP.Decremental.State.history b s)))
      (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @WellFounded.{1} (DecrAlmostLinearSSSP.Decremental.State b)
    (@InvImage.{1, 1} (DecrAlmostLinearSSSP.Decremental.State b) (Prod.{0, 0} Nat Nat)
      (@Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt) (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K))))) ∧ (((∀ {p sample κ mu eps r : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LT.lt.{0} Real Real.instLT κ p →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) mu →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LE.le.{0} Real Real.instLE
                (@OfNat.ofNat.{0} Real (nat_lit 32)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) mu eps) →
              @LE.le.{0} Real Real.instLE r (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @LE.le.{0} Real Real.instLE
                    (@abs.{0} Real Real.lattice Real.instAddGroup
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                          (@Max.max.{0} Real Real.instMax sample κ))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p sample)))
                    r →
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        p)
                      sample)
                    (@LE.le.{0} Real Real.instLE sample
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        p))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
      DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
          DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
            DecrAlmostLinearSSSP.Decremental.Stable b s →
              ∀ (v : Fin b.input.n),
                @Ne.{1} (Fin b.input.n) v b.input.source →
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v))
                      (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                    (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (x : Fin b.input.n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) x)
    (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)) ∧ ((∀ {n : Nat} (g x : Fin n → Real),
  @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.dot n g fun v => @Neg.neg.{0} Real Real.instNeg (x v))
    (@Neg.neg.{0} Real Real.instNeg (@DecrAlmostLinearSSSP.Decremental.dot n g x))) ∧ (∀ {n : Nat} (f g x : Fin n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.dot n
      (fun v => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (f v) (g v)) x)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@DecrAlmostLinearSSSP.Decremental.dot n f x)
      (@DecrAlmostLinearSSSP.Decremental.dot n g x))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real)
  (x : Fin b.input.n → Real),
  @Eq.{1} Real (DecrAlmostLinearSSSP.Decremental.norm b f fun v => @Neg.neg.{0} Real Real.instNeg (x v))
    (DecrAlmostLinearSSSP.Decremental.norm b f x)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f e)) →
    ∀ (x : Fin b.input.n → Real),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@DecrAlmostLinearSSSP.Decremental.dot b.input.n (DecrAlmostLinearSSSP.Decremental.gradient b f) x))
        (DecrAlmostLinearSSSP.Decremental.norm b f x))) ∧ ((∀ {K N G U d : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) N →
      @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              K))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            G U) →
        @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) G U)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d N)
              K) →
          @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Neg.neg.{0} Real Real.instNeg N)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            d) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
      DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
          DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
            @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
                (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
              Or
                  (@Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
                    (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                        (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))))
                  (∃ r,
                    And
                      (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                        (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                            (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                        (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r))
                      (@LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Neg.neg.{0} Real Real.instNeg
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            K))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                          (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))) →
                DecrAlmostLinearSSSP.Decremental.Balanced b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          Or
              (@Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
                (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                    (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))))
              (∃ r,
                And
                  (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                    (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                      (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                        (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                    (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r))
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@Neg.neg.{0} Real Real.instNeg
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 4)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                        K))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                      (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))) →
            DecrAlmostLinearSSSP.Decremental.Balanced b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
              @Eq.{1} Real
                (@DecrAlmostLinearSSSP.Decremental.State.sample b s
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (DecrAlmostLinearSSSP.Decremental.initialLabel b
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b s
                    (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) →
            DecrAlmostLinearSSSP.Decremental.AllTarget b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (DecrAlmostLinearSSSP.Decremental.labels b s) →
              ∀ (v : Fin b.input.n),
                @Ne.{1} (Fin b.input.n) v b.input.source →
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v))
                      (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                    (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : Fin b.input.k),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.coreLength b active p e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : Fin b.input.k),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e))
      (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e)))
    (DecrAlmostLinearSSSP.Decremental.coreLength b active p e)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (v : Fin b.input.n),
  @Ne.{1} (Fin b.input.n) v b.input.source →
    @LE.le.{0} ENNReal ENNReal.instLE
      (ENNReal.ofReal
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (DecrAlmostLinearSSSP.Decremental.Q b)))
      (DecrAlmostLinearSSSP.Decremental.coreDistance b active v)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real),
  @Eq.{1} Real (p b.input.source) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∀ (t : Fin b.input.n) (es : List.{0} (Fin b.input.k)),
      @DecrAlmostLinearSSSP.Decremental.Walk b.input.n b.input.k b.input.graph
          (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k)) b.input.source t es →
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.coreDistance b active t)
          (ENNReal.ofReal
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p t)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin b.input.k) Real (DecrAlmostLinearSSSP.Decremental.coreLength b active p) es)))))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.K_inverse_square_bound,DecrAlmostLinearSSSP.Decremental.capacity_pos⟩,⟨DecrAlmostLinearSSSP.Decremental.gradient_update,DecrAlmostLinearSSSP.Decremental.gradient_dot⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.physical_norm_cut,DecrAlmostLinearSSSP.Decremental.dot_cut⟩,⟨DecrAlmostLinearSSSP.Decremental.cachedPhysical_norm_eq,⟨DecrAlmostLinearSSSP.Decremental.toggle_potential,DecrAlmostLinearSSSP.Decremental.toggle_numeric_bounds⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.clippedLog_secant_upper,DecrAlmostLinearSSSP.Decremental.clippedLog_remainder⟩,⟨DecrAlmostLinearSSSP.Decremental.weighted_clippedLog_remainder,DecrAlmostLinearSSSP.Decremental.potential_remainder⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.sum_replace_two,DecrAlmostLinearSSSP.Decremental.refresh_counter⟩,⟨DecrAlmostLinearSSSP.Decremental.attained_counter,⟨DecrAlmostLinearSSSP.Decremental.zero_counter_gradient,DecrAlmostLinearSSSP.Decremental.actual_toggle_descent⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.cache_model_positive,DecrAlmostLinearSSSP.Decremental.refresh_cacheInvariant⟩,⟨DecrAlmostLinearSSSP.Decremental.initial_cacheInvariant,DecrAlmostLinearSSSP.Decremental.toggle_cacheInvariant⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.delete_cacheInvariant,DecrAlmostLinearSSSP.Decremental.attained_cacheInvariant⟩,⟨DecrAlmostLinearSSSP.Decremental.clipped_capacity_comparison,⟨DecrAlmostLinearSSSP.Decremental.cache_edge_comparison,DecrAlmostLinearSSSP.Decremental.gradient_sub⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.gradient_norm_comparison,DecrAlmostLinearSSSP.Decremental.invariant_cache_accuracy⟩,⟨DecrAlmostLinearSSSP.Decremental.invariant_toggle_descent,⟨DecrAlmostLinearSSSP.Decremental.reportedToggle_cacheInvariant,DecrAlmostLinearSSSP.Decremental.reportedToggle_descent⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.refresh_sample_baseline,DecrAlmostLinearSSSP.Decremental.attained_sample_baseline⟩,⟨DecrAlmostLinearSSSP.Decremental.core_A_accuracy,⟨DecrAlmostLinearSSSP.Decremental.attained_stopped_drained,DecrAlmostLinearSSSP.Decremental.refresh_output_sample⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.attained_output_sample,DecrAlmostLinearSSSP.Decremental.indegree_le_count⟩,⟨DecrAlmostLinearSSSP.Decremental.return_indegree_sum,DecrAlmostLinearSSSP.Decremental.coefficient_sum_sharp⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.core_cost_lower,DecrAlmostLinearSSSP.Decremental.kappa_le_initial_slack⟩,⟨DecrAlmostLinearSSSP.Decremental.initial_slack_lower,⟨DecrAlmostLinearSSSP.Decremental.initial_potential_upper,DecrAlmostLinearSSSP.Decremental.clippedLog_antitone⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.cost_erase_ge,DecrAlmostLinearSSSP.Decremental.deleted_potential_le⟩,⟨DecrAlmostLinearSSSP.Decremental.attained_energy,⟨DecrAlmostLinearSSSP.Decremental.attained_toggle_count,DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.initial⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.refresh,DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.delete⟩,⟨DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle,⟨DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle_count,DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggles_lt_limit⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.runtimeRank_refresh,DecrAlmostLinearSSSP.Decremental.runtimeRank_toggle⟩,⟨DecrAlmostLinearSSSP.Decremental.runtimeRank_stop,DecrAlmostLinearSSSP.Decremental.runtimeRank_wellFounded⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.sample_accuracy_of_drift,DecrAlmostLinearSSSP.Decremental.return_accuracy⟩,⟨DecrAlmostLinearSSSP.Decremental.cached_physical_norm,⟨DecrAlmostLinearSSSP.Decremental.dot_neg_right,DecrAlmostLinearSSSP.Decremental.dot_sub_left⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.norm_neg,DecrAlmostLinearSSSP.Decremental.gradient_abs_le_norm⟩,⟨DecrAlmostLinearSSSP.Decremental.ratio_direction_lower,⟨DecrAlmostLinearSSSP.Decremental.stopping_balance,DecrAlmostLinearSSSP.Decremental.invariant_stopping_balance⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.invariant_return_accuracy,DecrAlmostLinearSSSP.Decremental.coreLength_pos⟩,⟨DecrAlmostLinearSSSP.Decremental.core_label_edge_bound,⟨DecrAlmostLinearSSSP.Decremental.coreDistance_lower,DecrAlmostLinearSSSP.Decremental.coreDistance_ell_walk⟩⟩⟩⟩⟩⟩⟩
