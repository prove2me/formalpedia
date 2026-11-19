-- Prove2me | solution 2 for DecrAlmostLinearSSSP.Decremental.polynomial_weight_sssp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T04:15:54.554963+00:00
-- url     : https://prove2.me/submissions/b362e3fb-78ac-4f04-b8d5-dfa6c6d92caf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_9
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_11
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_12
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_13
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_9
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_11
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_12
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_13
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_dynamic_cut_interface
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore
abbrev CutImplementation := NonemptyCut.Implementation
abbrev CutRun := NonemptyCut.Run
abbrev CutRun.start := @NonemptyCut.Run.start
abbrev CutRun.next := @NonemptyCut.Run.next
noncomputable abbrev ImplementsCut := NonemptyCut.Implements

instance core_vertex_neZero (b : Core) : NeZero b.input.n where
  out := by have hh := b.two;omega
end DecrAlmostLinearSSSP.Decremental.NonemptyCore
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 6000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.eval_code : ∀ (count sourceBase cacheBase stride F : Nat) (delta : Real) (flags : Nat → Nat) (values : Nat → Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))) sourceBase →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) cacheBase →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170)))) stride →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176)))) count →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                        (∀ (j : Nat),
                            @LT.lt.{0} Nat instLTNat j count →
                              @LE.le.{0} Nat instLENat (flags j)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j count →
                                @Eq.{1} Nat (flags j) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                  @LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (values j)) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j count →
                                  @Eq.{1} Nat
                                    (s.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (flags j))) →
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j count →
                                    @Eq.{1} Real
                                      (s.realMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                      (values j)) →
                                (∀ (j : Nat),
                                    @LT.lt.{0} Nat instLTNat j count →
                                      ∀ (k : Nat),
                                        @LT.lt.{0} Nat instLTNat k count →
                                          @Ne.{1} Nat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride
                                                j))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cacheBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) →
                                  ∃ cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        DecrAlmostLinearSSSP.Decremental.CacheCopy.code s cost t)
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) count)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride
                                                count)))
                                          (And
                                            (@Eq.{1} Nat
                                              (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cacheBase
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) count)))
                                            (And
                                              (@Eq.{1} Nat
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                              (And
                                                (∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j count →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j)))
                                                        (flags j))
                                                      (@Eq.{1} Real
                                                        (t.realMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j)))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) delta (values j))))
                                                (∀ (address : Nat),
                                                  (∀ (j : Nat),
                                                      @LT.lt.{0} Nat instLTNat j count →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j))) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop_eval : ∀ (x : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreCeiling.Rep x s →
    ∃ t cost,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop s cost t)
        (And
          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x))
          (And
            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
              (@Nat.cast.{0} Real Real.instNatCast
                (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                  (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x)))
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreCeiling.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreCeiling.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreCommit.head_eval : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                  (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
                    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.returnBit b e) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                        (DecrAlmostLinearSSSP.Decremental.capacity b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                          (DecrAlmostLinearSSSP.Decremental.labels b state) e) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (DecrAlmostLinearSSSP.Decremental.capacity b
                              (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                              (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                            (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)) →
                        (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                            @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                                (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                                (DecrAlmostLinearSSSP.Decremental.labels b state
                                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                    v))) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.CoreCommit.headCode s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.captured : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input
      (DecrAlmostLinearSSSP.Decremental.CoreControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreControl.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) k) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
      Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) k) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.parameters : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K (DecrAlmostLinearSSSP.Decremental.CoreControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 656) (instOfNatNat (nat_lit 656))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 658) (instOfNatNat (nat_lit 658))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.values : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (B : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
        And
          (DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B
            (DecrAlmostLinearSSSP.Decremental.CoreControl.result s))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).realReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.Image.final : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n base
      (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b b.input.k) s →
    ∀ (v : Fin b.input.n),
      @Eq.{1} Nat
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n v))))
        (DecrAlmostLinearSSSP.Decremental.indegree b v) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.eval_code : ∀ (vertex : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.nat_frame : ∀ (vertex k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.real_frame : ∀ (vertex k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.values : ∀ (vertex base v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
    @Eq.{1} Nat (s.natReg vertex) v →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        And
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s).realMem s.realMem) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDeletion.after_bounds : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
            (DecrAlmostLinearSSSP.Decremental.refresh b
              (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
              (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDeletion.before_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
        (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
        (DecrAlmostLinearSSSP.Decremental.logicalCount b) (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreDeletion.pending_model : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
  (state : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E state c →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @DecrAlmostLinearSSSP.Decremental.CutModel b l E
        (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b state e) c := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreDeletion.prepare_eval : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val b.input.k e) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreDeletion.prepareCode s cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                      (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b state e) t)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b
                          (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDeletion.refresh_validity : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          DecrAlmostLinearSSSP.Decremental.RefreshValidity b
            (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
            (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDeletion.refreshed_eq : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
    @Eq.{1} (DecrAlmostLinearSSSP.Decremental.State b)
      (DecrAlmostLinearSSSP.Decremental.refresh b (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
      (DecrAlmostLinearSSSP.Decremental.deleteState b s e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.values : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) e))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image.state_congr : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) {before after : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B before s →
    @Eq.{1} (Finset.{0} (Fin b.input.k)) (@DecrAlmostLinearSSSP.Decremental.State.active b after)
        (@DecrAlmostLinearSSSP.Decremental.State.active b before) →
      @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b → Real) (@DecrAlmostLinearSSSP.Decremental.State.cache b after)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b before) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.sample b after)
            (@DecrAlmostLinearSSSP.Decremental.State.sample b before) →
          DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B after s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGeometry.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 574) (instOfNatNat (nat_lit 574))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
        (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))))
      (And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (And
            (@Eq.{1} Real
              ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
                (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradient.code s cost
          (DecrAlmostLinearSSSP.Decremental.CoreGradient.result s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreGradient.result s).realMem
      (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620)))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))))))
    (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreGradient.result s).natMem s.natMem)
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGradient.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
            (DecrAlmostLinearSSSP.Decremental.nonzero
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))))))
          (DecrAlmostLinearSSSP.Decremental.nonzero
            (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.eval_code : ∀ {n : Nat} (base : Nat) (g : Fin n → Real) (a z : Fin n) (delta f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost t)
                    (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39))))
                      (And
                        (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                          (fun v =>
                            @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                                (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) delta
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                              (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) delta
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                          t)
                        (And
                          (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f)
                          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
                            (∀ (j : Nat),
                              @Ne.{1} Nat j
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n a))) →
                                @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n z))) →
                                  @Eq.{1} Real (t.realMem j) (s.realMem j)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 698) (instOfNatNat (nat_lit 698))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
              DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.eval_code : ∀ {n : Nat} (base : Nat) (g : Fin n → Real) (a z : Fin n) (f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.code s cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                    (And
                      (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                        (fun v =>
                          @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                              (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) f
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                            (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) f
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                        t)
                      (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
                        (∀ (j : Nat),
                          @Ne.{1} Nat j
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n a))) →
                            @Ne.{1} Nat j
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n z))) →
                              @Eq.{1} Real (t.realMem j) (s.realMem j))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.head_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.headCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.headPrepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant.start : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgesStarted s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant.step : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state upto s →
    @LT.lt.{0} Nat instLTNat upto (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody s
            (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (And
              (∀ (j : Nat),
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                      ∀ (offset : Nat),
                        @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                          @Ne.{1} Nat j
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Nat (t.natMem j) (s.natMem j))
              (∀ (j : Nat),
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant.start : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
      (DecrAlmostLinearSSSP.Decremental.logicalCount b) s →
    DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))),
        realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant.step : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state upto s →
    @LT.lt.{0} Nat instLTNat upto b.input.n →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code s
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
              (∀ (j : Nat),
                (∀ (v : Nat),
                    @LT.lt.{0} Nat instLTNat v b.input.n →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code
                    s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85))) b.input.size))
                    (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
                      (And
                        (∀ (j : Nat),
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                                ∀ (offset : Nat),
                                  @LT.lt.{0} Nat instLTNat offset
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                    @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                            @Eq.{1} Nat (t.natMem j) (s.natMem j))
                        (∀ (j : Nat),
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                                @Ne.{1} Nat j
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                            (∀ (v : Nat),
                                @LT.lt.{0} Nat instLTNat v b.input.n →
                                  @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                              @Eq.{1} Real (t.realMem j) (s.realMem j))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 694) (instOfNatNat (nat_lit 694))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.counter : ∀ (e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) e
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 680) (instOfNatNat (nat_lit 680))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k)) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 680) (instOfNatNat (nat_lit 680))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 684) (instOfNatNat (nat_lit 684))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 694) (instOfNatNat (nat_lit 694))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.correct : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
          And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
              (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s))
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
                (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s))
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Image.certified : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b state →
      And
        (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n b.input.source))
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
        (And
          (∀ (v : Fin b.input.n),
            And
              (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val b.input.n v))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq.{1} Nat (s.natMem (@Fin.val b.input.n v))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (s.realMem (@Fin.val b.input.n v))))
          (∀ (v : Fin b.input.n),
            And
              (@LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (b.input.weight e))
                  b.input.source v)
                (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v)))
              (And
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v))
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                    (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (b.input.weight e))
                      b.input.source v)))
                (Iff
                  (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v))
                    (@Top.top.{0} ENNReal ENNReal.instTop))
                  (Not
                    (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state) b.input.source v)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Image.command_frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
        DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
          (∀ (k : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                  DecrAlmostLinearSSSP.Decremental.CoreHost.NatRegisters k →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k) →
            (∀ (k : Nat),
                @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                    DecrAlmostLinearSSSP.Decremental.CoreHost.RealRegisters k →
                  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k) →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Image.state_congr : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  {before after : DecrAlmostLinearSSSP.Decremental.State b} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K before s →
    @Eq.{1} (Finset.{0} (Fin b.input.k)) (@DecrAlmostLinearSSSP.Decremental.State.active b after)
        (@DecrAlmostLinearSSSP.Decremental.State.active b before) →
      @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b → Real) (@DecrAlmostLinearSSSP.Decremental.State.cache b after)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b before) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b after)
            (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b before) →
          @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
              (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
              (@DecrAlmostLinearSSSP.Decremental.State.pending b before) →
            @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.sample b after)
                (@DecrAlmostLinearSSSP.Decremental.State.sample b before) →
              @Eq.{1} (Fin b.input.n → ENNReal) (@DecrAlmostLinearSSSP.Decremental.State.output b after)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b before) →
                DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Image.temp_nat : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      ∀ (k value : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            { realReg := s.realReg,
              natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
              realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves.seq : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {K : Real} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {a c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state a →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state c →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state (a.seq c) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_erase : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_insert : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.insertCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_paired : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.pairedCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_query : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    ∀ (source : Nat),
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_ratio : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.ratioCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.reports_environment : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B (DecrAlmostLinearSSSP.Decremental.logicalCount b) s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.reports_image : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost t →
        @DecrAlmostLinearSSSP.Decremental.CorePending.View (DecrAlmostLinearSSSP.Decremental.logicalCount b) B ys t →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                s t →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                  (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                      (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.Edge b))
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.Edge b)))
                      (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
                    ys)
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.source_frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N entry : Nat) (K : Real)
  (state : DecrAlmostLinearSSSP.Decremental.State b) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) s
          cost t →
        (∀ (address : Nat),
            (∀ (a : Nat),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code s
          cost (DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.result s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.nat_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.value : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
      (@Fin.val b.input.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e)) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
        (@Fin.val b.input.n b.input.source) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.Q b))) →
        @Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (DecrAlmostLinearSSSP.Decremental.initialLabel b
              (DecrAlmostLinearSSSP.Decremental.tail b
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b
              (DecrAlmostLinearSSSP.Decremental.head b
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.eval_code : ∀ {n l : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (graph : DecrAlmostLinearSSSP.Decremental.Physical n l)
  (m N : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    ∀ (ξ cap : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536)))) l →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540)))) m →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))) ξ →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508)))) cap →
                      ∃ t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
                            t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
                              (@DecrAlmostLinearSSSP.Decremental.cutInitial n l p graph m ξ cap) t)
                            (∀ (address : Nat),
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j N →
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.2.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 670) (instOfNatNat (nat_lit 670))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 672) (instOfNatNat (nat_lit 672))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 674) (instOfNatNat (nat_lit 674))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540))))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialize.boot_cut_input_eval : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N registers : Nat) (p cut : DecrAlmostLinearSSSP.Decremental.Program),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) registers →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutInputCode N registers)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                    b.input.size)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 32)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                          (DecrAlmostLinearSSSP.Decremental.logarithm2
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                        b.input.accuracy))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) registers))
              (@OfNat.ofNat.{0} Nat (nat_lit 105) (instOfNatNat (nat_lit 105)))))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) registers
              (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                cut
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                  (DecrAlmostLinearSSSP.Decremental.initializeState b) (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.kappa b)
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.eval_code : ∀ {n : Nat} (base counter : Nat) (heads : List.{0} (Fin n)) (g : Fin n → Real) (a z : Fin n) (f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base heads s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) counter) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))))
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base
                                (@List.cons.{0} (Fin n) z heads) t)
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                                  (fun v =>
                                    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                                        (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) f
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                      (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) f
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                  t)
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (And
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val n z))) →
                                        @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val n a))) →
                                        @Ne.{1} Nat j
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val n z))) →
                                          @Eq.{1} Real (t.realMem j) (s.realMem j))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant.start : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            (∀ (v : Fin b.input.n),
                And
                  (@Eq.{1} Nat (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (s.realMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.started s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant.step : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.k →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s
              cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83))))
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.captured : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.k e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val b.input.k e))) →
              @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                  (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b (@Fin.val b.input.k e)) s →
                @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b (@Fin.val b.input.k e)) s →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e) t)
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                  (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Fin.val b.input.k e)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  t)
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Fin.val b.input.k e)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    t)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Fin.val b.input.k e)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Fin.val b.input.k e)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                      (∀ (j : Nat),
                                        (∀ (offset : Nat),
                                            @LT.lt.{0} Nat instLTNat offset
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                              @Ne.{1} Nat j
                                                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                                  (@Sum.inl.{0, 0} (Fin b.input.k)
                                                    (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                                                  offset)) →
                                          @Ne.{1} Nat j
                                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B
                                                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k
                                                  b.input.graph e)) →
                                            @Ne.{1} Nat j
                                                (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B
                                                  (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k
                                                    b.input.graph e)) →
                                              And (@Eq.{1} Nat (t.natMem j) (s.natMem j))
                                                (@Eq.{1} Real (t.realMem j) (s.realMem j))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.parameters : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.captured : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost
        t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
            (@Fin.val b.input.n b.input.source) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.k e)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val b.input.k e))) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
                      (DecrAlmostLinearSSSP.Decremental.Q b) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (DecrAlmostLinearSSSP.Decremental.Q b))) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25))))
                            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e t)
                              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.parameters : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost
        t →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant.step : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.n →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body
              s cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 87) (instOfNatNat (nat_lit 87))))
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 506) (instOfNatNat (nat_lit 506))))
            (DecrAlmostLinearSSSP.Decremental.kappa b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code s
                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                  (DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                    (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                    (DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                      (DecrAlmostLinearSSSP.Decremental.capacity b
                        (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                        (DecrAlmostLinearSSSP.Decremental.initialLabel b)
                        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
                    (∀ (j : Nat),
                      (∀ (offset : Nat),
                          @LT.lt.{0} Nat instLTNat offset
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            @Ne.{1} Nat j
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                                offset)) →
                        And
                          (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).natMem j)
                            (s.natMem j))
                          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).realMem j)
                            (s.realMem j))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.nat_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame.trans : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame.trans : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.relation_wellFounded : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @WellFounded.{1} (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b)
    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.relation b K) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.capture_nat_frame : ∀ (N source dest : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.captureQueryCode N source dest p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.capture_real_frame : ∀ (N source dest : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k dest →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.captureQueryCode N source dest p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant_positive : ∀ (d N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant d N p C) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram_query : ∀ (qualityPower : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower p)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c
            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower p).query;
        { pc := __src.pc, realReg := __src.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) v,
          realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
          work := __src.work })
        d)
      (And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))
        (And (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (c.natMem v))
          (And (@Eq.{1} Real (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (c.realMem v))
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drain_running_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drain_threshold_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.dynamic_budget_arithmetic : ∀ (D C d h Γ K L M : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) D →
    @LE.le.{0} Real Real.instLE
        (@OfNat.ofNat.{0} Real (nat_lit 20)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
        C →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Γ →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    M →
                  ∀ (offset : Real),
                    @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) offset →
                      @LE.le.{0} Real Real.instLE offset
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 6)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
                            M) →
                        have T :=
                          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1040)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 1040) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1039) (instOfNatNat (nat_lit 1039)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1038) (instOfNatNat (nat_lit 1038)))))))
                                  d)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                L (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            M;
                        @LE.le.{0} Real Real.instLE
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D h) C)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 5)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                                              (@instHPow.{0, 0} Real Nat
                                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                              K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                          T))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        T))
                                    offset)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D h)
                                  (@OfNat.ofNat.{0} Real (nat_lit 20)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat
                                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                      K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  T)))
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@OfNat.ofNat.{0} Real (nat_lit 10000)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 10000) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 9999) (instOfNatNat (nat_lit 9999)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 9998)
                                                    (instOfNatNat (nat_lit 9998)))))))
                                          d)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) D C))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h))
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) Γ))
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    K (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  L (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              M)
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.erase_nat_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.eraseCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.erase_real_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.eraseCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.insert_nat_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.insertCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.insert_real_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.insertCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labels_addresses : ∀ {base : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat}
  {p : DecrAlmostLinearSSSP.Decremental.Program},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) s
      cost t →
    DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labels_loaded : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {e : DecrAlmostLinearSSSP.Decremental.Edge b} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat}
  {p : DecrAlmostLinearSSSP.Decremental.Program},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) s
      cost t →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
      DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labels_nat_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.live_append_singleton : ∀ {k : Nat} (deleted : List.{0} (Fin k)) (e : Fin k),
  @Eq.{1} (Finset.{0} (Fin k))
    (@DecrAlmostLinearSSSP.Decremental.live k
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
        (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k))) deleted
        (@List.cons.{0} (Fin k) e (@List.nil.{0} (Fin k)))))
    (@Finset.erase.{0} (Fin k) (instDecidableEqFin k) (@DecrAlmostLinearSSSP.Decremental.live k deleted) e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physical_refresh_nat_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physical_refresh_real_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratio_running_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratio_threshold_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.scale_bounds : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (h Γ a : Nat → Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (h
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Γ
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
        have m := @Nat.cast.{0} Real Real.instNatCast b.input.size;
        have M :=
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            m b.input.accuracy;
        have O := DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N b.input.size;
        have K :=
          DecrAlmostLinearSSSP.Decremental.computableCutQuality N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
        have L := DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size;
        And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) M)
          (And (@LE.le.{0} Real Real.instLE m M)
            (And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L)
              (And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  O)
                (And
                  (@LE.le.{0} Real Real.instLE
                    (a
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                    O)
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (h
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (Γ
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            K (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      O)
                    (@LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) L b.input.accuracy)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) O M))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stop_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stopCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stop_threshold_frame : DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stopCode
  (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggle_running_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggleCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggle_threshold_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggleCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.eval_code : ∀ (source target : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) s cost
          (DecrAlmostLinearSSSP.Decremental.CoreNonzero.result source target s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.nat_frame : ∀ (source target k : Nat),
  @Ne.{1} Nat k target →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.real_frame : ∀ (source target k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Nat)
  (r : Real),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620)))) v →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616)))) r →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
            (DecrAlmostLinearSSSP.Decremental.Q b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 534) (instOfNatNat (nat_lit 534))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (DecrAlmostLinearSSSP.Decremental.H b)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 518) (instOfNatNat (nat_lit 518))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                  (DecrAlmostLinearSSSP.Decremental.Q b)) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreOutput.code s
                    cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (And
                      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine v)
                        (DecrAlmostLinearSSSP.Decremental.readout b r))
                      (And
                        (@LE.le.{0} Nat instLENat (t.natMem v)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (And
                          (@Eq.{1} Nat (t.natMem v) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (t.realMem v))
                          (∀ (j : Nat),
                            @Ne.{1} Nat j v →
                              And (@Eq.{1} Nat (t.natMem j) (s.natMem j))
                                (@Eq.{1} Real (t.realMem j) (s.realMem j))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 622) (instOfNatNat (nat_lit 622))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreOutput.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 624) (instOfNatNat (nat_lit 624))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreOutput.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreParameters.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442)))) K →
      ∃ t cost,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.code s cost
            t)
          (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t)
            (And (DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 32)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                            (DecrAlmostLinearSSSP.Decremental.logarithm2
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                          b.input.accuracy)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 45) (instOfNatNat (nat_lit 45)))))
                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.trans : ∀ {B l : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l t u →
      DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.insert_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.insertCode s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.CorePending.inserted s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreQuality.eval_code : ∀ (N : Nat) (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
        ∃ t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreQuality.code N) s
              cost t)
            (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t)
              (And
                (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
                  (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size)))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        i.size)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.holds_iff : ∀ (K G U : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))) G →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))) U →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              K)) →
        Iff
          ((DecrAlmostLinearSSSP.Decremental.Structured.Test.realLess
                (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
                (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))).holds
            (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s))
          (@LT.lt.{0} Real Real.instLT
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) G U)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                K))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.host_image : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.source_image : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRecord.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (DecrAlmostLinearSSSP.Decremental.CoreRecord.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRecord.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRecord.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.computed : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
              (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.head b e)) →
              And
                (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
                  (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
                    (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                      (DecrAlmostLinearSSSP.Decremental.capacity b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (DecrAlmostLinearSSSP.Decremental.capacity b
                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                            (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                          (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                      (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                        @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                          @Eq.{1} Real
                            ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                              (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                            (DecrAlmostLinearSSSP.Decremental.labels b state
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRefresh.code s
      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
      (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.correct : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
        And
          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e
              (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e))))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.source_frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.credit_deletion : ∀ (N D oldWork newWork calls reports stopped cost : Nat),
  @LE.le.{0} Nat instLENat oldWork newWork →
    @LE.le.{0} Nat instLENat stopped (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat cost
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) newWork oldWork))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
            (@OfNat.ofNat.{0} Nat (nat_lit 240) (instOfNatNat (nat_lit 240)))) →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
              (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
            (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork calls reports stopped))
          (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            reports (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.credit_drain : ∀ (N D oldWork newWork calls reports cost : Nat),
  @LE.le.{0} Nat instLENat oldWork newWork →
    @LE.le.{0} Nat instLENat cost
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) newWork oldWork))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
          (@OfNat.ofNat.{0} Nat (nat_lit 219) (instOfNatNat (nat_lit 219)))) →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork calls reports
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          reports (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.credit_zero_stop : ∀ (N D work calls reports : Nat),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D work calls reports
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D work calls reports
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.debt_deletion : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k)
  (calls reports offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b (DecrAlmostLinearSSSP.Decremental.deleteState b s e)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        reports
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.debt_refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (calls reports offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
      DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        reports offset := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.debt_stop : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (calls nextCalls reports offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
      @LE.le.{0} Nat instLENat nextCalls
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b
          (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
            (@DecrAlmostLinearSSSP.Decremental.State.y b s) (@DecrAlmostLinearSSSP.Decremental.State.cache b s)
            (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
            (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
            (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
            (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s) Bool.true
            (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) (@DecrAlmostLinearSSSP.Decremental.State.history b s))
          nextCalls reports offset := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.ratio_accounting : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (before after : DecrAlmostLinearSSSP.Decremental.State b)
  (N D oldWork newWork oldCalls newCalls oldReports newReports oldToggles newToggles cost offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.RatioShape b K before after N D oldWork newWork oldCalls newCalls
      oldReports newReports oldToggles newToggles cost →
    @LE.le.{0} Nat instLENat oldWork newWork →
      @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b before) Bool.false →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b before)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b before oldCalls oldReports offset →
            @Eq.{1} Nat oldToggles (@DecrAlmostLinearSSSP.Decremental.State.toggles b before) →
              And (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after newCalls newReports offset)
                (And (@Eq.{1} Nat newToggles (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork oldCalls oldReports
                        (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b before)))
                    (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork newCalls newReports
                      (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b after)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit_le_one : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} (s : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b s)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.host_image : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 656) (instOfNatNat (nat_lit 656))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 658) (instOfNatNat (nat_lit 658))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.source_image : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.values : ∀ (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))) K →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            K))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReports.eval_code : ∀ (B l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (xs : List.{0} (Fin l))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
            g →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost
                t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                      (DecrAlmostLinearSSSP.Decremental.reportCount g))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                (And
                  (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                    (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs
                      (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g))
                    t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (And
                        (∀ (j : Nat),
                          @Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                        (And
                          (∀ (e : Fin l),
                            Iff
                              (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
                                (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs
                                  (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g))
                                e)
                              (Or
                                (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs
                                  e)
                                (@DecrAlmostLinearSSSP.Decremental.Reported l g e)))
                          (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReports.initial_reports_length : ∀ (l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} (Fin l)
      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l (@List.nil.{0} (Fin l))
        (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g)))
    (DecrAlmostLinearSSSP.Decremental.reportCount g) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReports.logical_membership : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))),
  (∀ (d : Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)),
      Iff
        (@Membership.mem.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
          (List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
          (@List.instMembership.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))) ys d)
        (@DecrAlmostLinearSSSP.Decremental.Reported (DecrAlmostLinearSSSP.Decremental.logicalCount b) g d)) →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      Iff
        (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
          (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (DecrAlmostLinearSSSP.Decremental.Edge b)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (DecrAlmostLinearSSSP.Decremental.Edge b))
              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                  (DecrAlmostLinearSSSP.Decremental.Edge b))
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.Edge b)
                (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                  (DecrAlmostLinearSSSP.Decremental.Edge b)))
              (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
            ys)
          e)
        (@DecrAlmostLinearSSSP.Decremental.Reported (DecrAlmostLinearSSSP.Decremental.logicalCount b) g
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReports.loop_eval : ∀ (B l : Nat) (reports : List.{0} Nat) (xs : List.{0} (Fin l)) (offset : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset (@List.length.{0} Nat reports))) →
          (∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{0} Nat reports)),
              @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset j)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@GetElem.getElem.{0, 0, 0} (List.{0} Nat) Nat Nat
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Nat as))
                    (@List.instGetElemNatLtLength.{0} Nat) reports j hj))) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.loop s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (@List.length.{0} Nat reports))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports) t)
                    (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@List.length.{0} Nat reports))))
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                          (And
                            (∀ (j : Nat),
                              @Eq.{1} Nat
                                (t.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (s.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                            (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.erase_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Fin k),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val k e)) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode s
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
              (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
              t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.erase_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.erase_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.insert_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Fin k)
  (a b : Fin n) (capacity : Real),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val k e)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n b) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) capacity →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.CoreRequest.insertCode s
                    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) t)
                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                      (@DecrAlmostLinearSSSP.Decremental.CutOp.insert n k e a b capacity))
                    t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_frame : ∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.paired_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a b : Fin n)
  (delta : Real),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreRequest.pairedCode s
                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))) t)
                (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                  (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                    (@DecrAlmostLinearSSSP.Decremental.CutOp.paired n k a b delta))
                  t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.query_eval : ∀ {n k : Nat} (B R N source : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin n),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Eq.{1} Nat (s.natReg source)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v)) →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source) s
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t)
                (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                  (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                    (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY n k v))
                  t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.ratio_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.ratioCode s
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) t)
          (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
            (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio n k))
            t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_frame : ∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.toggle_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (tau : Real),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Real
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))))
          tau →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode s
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
              (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle n k tau))
              t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (v sampleAddress : Nat) (r : Real),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578)))) sampleAddress →
      @Ne.{1} Nat sampleAddress v →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616)))) r →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
                  (DecrAlmostLinearSSSP.Decremental.Q b) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 534) (instOfNatNat (nat_lit 534))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (DecrAlmostLinearSSSP.Decremental.H b)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 518) (instOfNatNat (nat_lit 518))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                        (DecrAlmostLinearSSSP.Decremental.Q b)) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.CoreReturn.code s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                          (And
                            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine v)
                              (DecrAlmostLinearSSSP.Decremental.readout b r))
                            (And (@Eq.{1} Real (t.realMem sampleAddress) r)
                              (And
                                (@LE.le.{0} Nat instLENat (t.natMem v)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (And
                                  (@Eq.{1} Nat (t.natMem v)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (t.realMem v))
                                  (And (∀ (j : Nat), @Ne.{1} Nat j v → @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j v →
                                        @Ne.{1} Nat j sampleAddress → @Eq.{1} Real (t.realMem j) (s.realMem j)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 622) (instOfNatNat (nat_lit 622))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReturn.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 624) (instOfNatNat (nat_lit 624))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReturn.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.value : ∀ (base v q : Nat) (A : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
      @Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
          q →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 504) (instOfNatNat (nat_lit 504)))) A →
          @Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) A
              (@Nat.cast.{0} Real Real.instNatCast q)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.call : ∀ (B R N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g final : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      (∃ r,
          @Eq.{1} Nat R
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Bool g.halted Bool.false →
            @Eq.{1} Bool g.fault Bool.false →
              DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                DecrAlmostLinearSSSP.Decremental.Ends p g final →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                            (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                        (And (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N final t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t final)
                            (∀ (address : Nat),
                              (∀ (a : Nat),
                                  @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                                @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                  (∀ (j : Nat),
                                      @LT.lt.{0} Nat instLTNat j N →
                                        @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.command_frame : ∀ (B R N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters cmd) Bool.true →
          (∀ (k : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))
                      (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                        (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))
                          (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                            (@List.nil.{0} Nat))))))
                  k →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k) →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.nat_register : ∀ (B R N k value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))) →
                DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g
                  { realReg := s.realReg,
                    natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
                    realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.real_register : ∀ (B R N k : Nat) (value : Real) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g
        { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg k value,
          natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.report_scan : ∀ (B R N l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) l))
        R →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost t →
        @Eq.{1} (Nat → Real) t.realMem s.realMem →
          DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreTape.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (DecrAlmostLinearSSSP.Decremental.CoreTape.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreTape.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreTape.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.values : ∀ (pointer a z w : Nat) (Q : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652)))) pointer →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502)))) Q →
        @Eq.{1} Nat (s.natMem pointer) a →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              z →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                w →
              And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                  a)
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                    z)
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))))
                      w)
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast w) Q))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CutModel.erase_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
            E e)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CutModel.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l)
      (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n l c)
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.initializeState b) l E) →
    @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.y b.input.n l c)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
      @Eq.{1} (Fin l → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.baseline b.input.n l c)
          (@OfNat.ofNat.{0} (Fin l → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin l → Real) (@Pi.instZero.{0, 0} (Fin l) (fun a => Real) fun i => Real.instZero))) →
        @DecrAlmostLinearSSSP.Decremental.CutModel b l E (DecrAlmostLinearSSSP.Decremental.initializeState b) c := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.insert_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c c1 : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
          (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e))
          g c1 →
        @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c1
          (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e)
            (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
            (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s) e)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.query : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (v : Fin b.input.n),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n l v) g t →
      And (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) t c)
        (@Eq.{1} Real (g.realReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@DecrAlmostLinearSSSP.Decremental.State.y b s v)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CutModel.ratio : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K K0 ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K0 ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio b.input.n l) g t →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
              (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
          @LE.le.{0} Real Real.instLE K0 K →
            And (@DecrAlmostLinearSSSP.Decremental.CutModel b l E s t)
              (And
                (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                  (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                      (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                  (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n l t)
                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l t)
                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastCut b.input.n l t))
                (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n l t) Bool.true)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CutModel.refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (c c1 c2 c3 : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l)
  (K ξ : Real) (g1 g2 g3 : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
            E e))
        g1 c1 →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c1
          (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e)
            (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
            (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s) e))
          g2 c2 →
        @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c2
            (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n l (DecrAlmostLinearSSSP.Decremental.head b e)
              (DecrAlmostLinearSSSP.Decremental.tail b e)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e)
                (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)))
            g3 c3 →
          @DecrAlmostLinearSSSP.Decremental.CutModel b l E (DecrAlmostLinearSSSP.Decremental.refresh b s e) c3 := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K K0 : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K0
          (@HPow.hPow.{0, 0, 0} Real Int Real
            (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          c
          (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c))))
          g t →
        (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
            Iff
              (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) reports e)
              (@DecrAlmostLinearSSSP.Decremental.Reported l g
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                  (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                    (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                    (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                  E e))) →
          @DecrAlmostLinearSSSP.Decremental.CutModel b l E
            (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s (@DecrAlmostLinearSSSP.Decremental.modelReply b l c)
              reports)
            t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.toggle_complete : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K K0 : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K0
          (@HPow.hPow.{0, 0, 0} Real Int Real
            (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          c
          (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c))))
          g t →
        (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
            Iff
              (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) reports e)
              (@DecrAlmostLinearSSSP.Decremental.Reported l g
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                  (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                    (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                    (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                  E e))) →
          DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s (@DecrAlmostLinearSSSP.Decremental.modelReply b l c)
            reports := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.toggle_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K : Real),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n l c) Bool.true →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
              (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
            @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c
              (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.eval_code : ∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
  @LE.le.{0} Nat instLENat n flagBase →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        listBase →
      (∀ (address : Nat),
          @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
            And (@LE.le.{0} Nat instLENat n address)
              (∀ (v : Fin n),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))))) →
        ∀ (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase xs s →
            @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 102) (instOfNatNat (nat_lit 102)))) listBase →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                            (∀ v ∉ xs,
                                And
                                  (@Eq.{1} Nat (s.natMem (@Fin.val n v))
                                    (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                  (@Eq.{1} Real (s.realMem (@Fin.val n v))
                                    (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) →
                              ∃ cost t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    DecrAlmostLinearSSSP.Decremental.DirtyCommit.code s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                          (@List.length.{0} (Fin n) xs))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase
                                        (@List.nil.{0} (Fin n)) t)
                                      (And (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)
                                        (And
                                          (∀ (v : Fin n),
                                            And
                                              (@Eq.{1} Nat (t.natMem (@Fin.val n v))
                                                (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                              (@Eq.{1} Real (t.realMem (@Fin.val n v))
                                                (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v)))
                                          (∀ (address : Nat),
                                            (∀ (v : Fin n),
                                                @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                    (@List.instMembership.{0} (Fin n)) xs v →
                                                  And (@Ne.{1} Nat address (@Fin.val n v))
                                                    (@Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        flagBase
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          (@Fin.val n v))))) →
                                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))) →
                      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                        DecrAlmostLinearSSSP.Decremental.DirtyCommit.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.eval_code : ∀ {n : Nat} (flagBase listBase : Nat) (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase xs s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            (∀ (u : Fin n),
                @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n u)))
                  listBase) →
              ∃ cost t ys,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.code s
                    cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (And
                      (@Eq.{1} (List.{0} (Fin n)) ys
                        (@ite.{1} (List.{0} (Fin n))
                          (@Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n)) (@List.instMembership.{0} (Fin n)) xs v)
                          (@List.instDecidableMemOfLawfulBEq.{0} (Fin n)
                            (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n))
                            (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin n)
                              (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n)) (instOrdFin n)
                              (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin n)
                                (@Preorder.toLE.{0} (Fin n)
                                  (@PartialOrder.toPreorder.{0} (Fin n)
                                    (@LinearOrder.toPartialOrder.{0} (Fin n) (@Fin.instLinearOrder n))))
                                (@Preorder.toLT.{0} (Fin n)
                                  (@PartialOrder.toPreorder.{0} (Fin n)
                                    (@LinearOrder.toPartialOrder.{0} (Fin n) (@Fin.instLinearOrder n))))
                                (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n))
                                (@Ord.compare.{0} (Fin n) (instOrdFin n))
                                (@instLawfulBCmpCompare_mathlib.{0} (Fin n) (@Fin.instLinearOrder n)))
                              (Fin.instLawfulEqOrd n))
                            v xs)
                          xs
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin n)) (List.{0} (Fin n)) (List.{0} (Fin n))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin n)) (@List.instAppend.{0} (Fin n))) xs
                            (@List.cons.{0} (Fin n) v (@List.nil.{0} (Fin n))))))
                      (And (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase ys t)
                        (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) ys) n)
                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                            (∀ (address : Nat),
                              @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))) →
                                @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) listBase
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@List.length.{0} (Fin n) xs))) →
                                  @Eq.{1} Nat (t.natMem address) (s.natMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.insert_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.insertCode s
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (DecrAlmostLinearSSSP.Decremental.DirtyMark.inserted s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Ends.work_mono : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d → @LE.le.{0} Nat instLENat c.work d.work := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (remaining upto : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto remaining) i.k →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop
              s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) remaining)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              t)
            (And (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i i.k t)
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                (∀ (a : Nat),
                  Or
                      (@LT.lt.{0} Nat instLTNat a
                        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            i.n i.k).heads)
                      (@LE.le.{0} Nat instLENat
                        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            i.n i.k).powers
                        a) →
                    @Eq.{1} Nat (t.natMem a) (s.natMem a)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.eval_code : ∀ (base length : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290)))) base →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 292) (instOfNatNat (nat_lit 292))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Clear.code s
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) length)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length))
                (And
                  (∀ (a : Nat),
                    @LE.le.{0} Nat instLENat base a →
                      @LT.lt.{0} Nat instLTNat a
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) →
                        @Eq.{1} Nat (t.natMem a) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                    (∀ (a : Nat),
                      Or (@LT.lt.{0} Nat instLTNat a base)
                          (@LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) a) →
                        @Eq.{1} Nat (t.natMem a) (s.natMem a))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed.ready : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i deleted c →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.ready : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.external : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    ∀ (index : Nat),
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) index,
          realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.run : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)},
  i.Valid →
    ∀ (q : DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State i deleted)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted q s →
        ∃ next t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.loop s
              cost t)
            (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted next t)
              (And
                (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i deleted next)
                  (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                      (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (∀ (v : Fin i.n),
                    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                      (i.dist deleted v))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.step : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)},
  i.Valid →
    ∀ (q : DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State i deleted)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted q s →
        (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
                (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                (@OfNat.ofNat.{0} Nat (nat_lit 348) (instOfNatNat (nat_lit 348)))).holds
            s →
          ∃ next t cost,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.body s
                cost t)
              (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted next t)
                (And
                  (@LT.lt.{0} Nat instLTNat
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted next)
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q))
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q)
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted next)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.initialize_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
          ∃ cost t q,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.initializeCode s cost t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i (@List.nil.{0} (Fin i.k)) q t)
                  (And
                    (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i (@List.nil.{0} (Fin i.k)) q)
                      (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))
                    (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i (@List.nil.{0} (Fin i.k)) t)
                      (And
                        (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n i.source))
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                        (And
                          (∀ (v : Fin i.n),
                            And
                              (@LE.le.{0} Nat instLENat (t.natMem (@Fin.val i.n v))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@Eq.{1} Nat (t.natMem (@Fin.val i.n v))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (t.realMem (@Fin.val i.n v))))
                          (∀ (v : Fin i.n),
                            And
                              (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                (i.dist (@List.nil.{0} (Fin i.k)) v))
                              (Iff
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                  (@Top.top.{0} ENNReal ENNReal.instTop))
                                (Not
                                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source
                                    v)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.online : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      ∃ cs last,
        And
          (DecrAlmostLinearSSSP.Decremental.OnlineRun DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram i ds
            cs)
          (And
            (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (And
              (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine last))
              (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i ds last)
                (And
                  (∀ (j : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                          DecrAlmostLinearSSSP.Decremental.Machine
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c) →
                      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i (@List.take.{0} (Fin i.k) j ds) c)
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) last.work
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@List.length.{0} (Fin i.k) ds)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_initialization : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∃ cost c,
      And
        (DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
          (DecrAlmostLinearSSSP.Decremental.initialMachine DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
            i)
          c)
        (And
          (@Eq.{1} Nat c.work
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i (@List.nil.{0} (Fin i.k))
                (DecrAlmostLinearSSSP.Decremental.Structured.data c))
              (∃ q,
                And
                  (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i (@List.nil.{0} (Fin i.k)) q
                    (DecrAlmostLinearSSSP.Decremental.Structured.data c))
                  (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i (@List.nil.{0} (Fin i.k)) q)
                    (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                        (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_update : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (deleted : List.{0} (Fin i.k)) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted
          (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
        ∀ (e : Fin i.k),
          ∃ cost d,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
                (DecrAlmostLinearSSSP.Decremental.deletionMachine
                  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram c (@Fin.val i.k e))
                d)
              (And
                (@Eq.{1} Nat d.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i
                      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                        (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                        (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                      (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                    (∃ q,
                      And
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                          q (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                        (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i
                            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                              (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                              (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                            q)
                          (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                              (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.count : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Layout.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 224) (instOfNatNat (nat_lit 224))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 226) (instOfNatNat (nat_lit 226))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 228) (instOfNatNat (nat_lit 228))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 230) (instOfNatNat (nat_lit 230))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 232) (instOfNatNat (nat_lit 232))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.values : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded.root : ∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      And (@LE.le.{0} Nat instLENat low (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@LT.lt.{0} Nat instLTNat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree) high) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.count : ∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234)))) base →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.code s
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (DecrAlmostLinearSSSP.Decremental.Exact.height
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
            t)
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W) base
              (DecrAlmostLinearSSSP.Decremental.Exact.height
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
              t)
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
              (∀ (address : Nat),
                Or (@LT.lt.{0} Nat instLTNat address base)
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                        (DecrAlmostLinearSSSP.Decremental.Exact.height
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
                      address) →
                  @Eq.{1} Nat (t.natMem address) (s.natMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.loop_eval : ∀ (bound base remaining done : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) done remaining)
      (DecrAlmostLinearSSSP.Decremental.Exact.height bound) →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base done s →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.loop s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) remaining)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              t)
            (And
              (DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
                (DecrAlmostLinearSSSP.Decremental.Exact.height bound) t)
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                (∀ (address : Nat),
                  Or
                      (@LT.lt.{0} Nat instLTNat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base done))
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                          (DecrAlmostLinearSSSP.Decremental.Exact.height bound))
                        address) →
                    @Eq.{1} Nat (t.natMem address) (s.natMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.stored : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
        (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h} {low : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.final h tree low s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ExtendedMax.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))) →
          (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ExtendedMax.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (And
                    (@LE.le.{0} Nat instLENat
                      (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (And
                      (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (t.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
                      (And
                        (@Eq.{1} ENNReal
                          (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (@Max.max.{0} ENNReal ENNReal.instMax
                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming s)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) →
                            And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                              (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Fill.eval_code : ∀ (n base stride value : Nat) (realValue : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) stride →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118)))) n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))) stride →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))) value →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116)))) realValue →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  ∃ t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Fill.code s
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        t)
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride n)))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (And
                            (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j n →
                                And
                                  (@Eq.{1} Nat
                                    (t.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    value)
                                  (@Eq.{1} Real
                                    (t.realMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    realValue))
                            (∀ (address : Nat),
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j n →
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Fill.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Fill.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Fill.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Fill.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.InputCapture.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Layout.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B n S reserve stride : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))) S →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n S) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))) reserve →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    (DecrAlmostLinearSSSP.Decremental.Layout.code stride) s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stride
                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                    t)
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Layout.Represents t
                      (DecrAlmostLinearSSSP.Decremental.Layout.addresses B n S reserve stride))
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Layout.real_frame : ∀ (stride k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.eval_code : ∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rows) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex rows →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                        (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows))
                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                      (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress rows))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory.source_frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {a : DecrAlmostLinearSSSP.Decremental.AdapterState i}
  {xs : List.{0} (Fin i.n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @LE.le.{0} Nat instLENat i.n B →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (B j cache : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (b : Fin i.n → ENNReal) (v : Fin i.n)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s g.natMem g.realMem →
        DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache b s →
          (∀ (u : Fin i.n),
              And
                (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n u))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat (g.natMem (@Fin.val i.n u)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (g.realMem (@Fin.val i.n u)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                    (@Fin.val i.n v) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                      (DecrAlmostLinearSSSP.Decremental.bankAddress B j (@Fin.val i.n v)) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                        (DecrAlmostLinearSSSP.Decremental.bankFactor j) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))) cache →
                        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                            (DecrAlmostLinearSSSP.Decremental.delta i j) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache
                                    (@Function.update.{1, 1} (Fin i.n) (fun a => ENNReal) (instDecidableEqFin i.n) b v
                                      (@Max.max.{0} ENNReal ENNReal.instMax (b v)
                                        (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))))
                                    t)
                                  (∀ (address : Nat),
                                    @Ne.{1} Nat address
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@Fin.val i.n v))) →
                                      And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                        (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ControlFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.ControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.DirtyMark.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.DirtyMark.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {g : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve g b ptr s →
    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n i.source))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.NormalRunState.work_bound : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
  {coefficient : Nat} {initial : DecrAlmostLinearSSSP.Decremental.Machine}
  (st :
    DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
      (Fin.last (@List.length.{0} (Fin i.k) ds))),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.Native.NormalRunState.machine i p C a ds guides coefficient initial
          (Fin.last (@List.length.{0} (Fin i.k) ds)) st).work
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@List.length.{0} (Fin i.k) ds)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initial.work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size)
          (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
            (Fin.last (@List.length.{0} (Fin i.k) ds)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) i.n)
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (start : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    @LE.le.{0} Nat instLENat recordBase cacheBase →
      @LE.le.{0} Nat instLENat start (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        @Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointerBase
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
            (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride start) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val i.n v) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96)))) pointerBase →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (DecrAlmostLinearSSSP.Decremental.advance i b v
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) start)
                                  start)
                                start))
                            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                        (And
                          (@Eq.{1} (Nat → Nat) t.natMem
                            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointerBase
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))
                              (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride
                                (DecrAlmostLinearSSSP.Decremental.advance i b v
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) start)
                                  start))))
                          (@Eq.{1} (Nat → Real) t.realMem s.realMem))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code
        k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.RecordImage.source_frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B record cache next N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    (∃ r,
        @Eq.{1} Nat record
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      (∀ (address : Nat),
          (∀ (a : Nat),
              @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
              (∀ (r : Nat),
                  @LT.lt.{0} Nat instLTNat r N →
                    @Ne.{1} Nat address
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                  (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue.head : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine)
          (reports : List.{0} Nat),
          (∀ (address : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports address →
                ∃ logical,
                  @Eq.{1} Nat address
                    (DecrAlmostLinearSSSP.Decremental.bankAddress B
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)) →
            (∀ (z : Fin i.n),
                And
                  (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (g.realMem (@Fin.val i.n z)))) →
              ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
                (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
                  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                      s →
                    (∀ (z : Fin i.n),
                        DecrAlmostLinearSSSP.Decremental.PointerValid i
                          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s g.natMem g.realMem →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                (DecrAlmostLinearSSSP.Decremental.delta i
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
                                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
                                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).reports →
                                    DecrAlmostLinearSSSP.Decremental.ReportLog
                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).reports
                                        reports s →
                                      @LE.le.{0} Nat instLENat (@List.length.{0} Nat reports) reserve →
                                        ∃ cost t ys,
                                          And
                                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code s cost t)
                                            (And
                                              (@LE.le.{0} Nat instLENat cost
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 16)
                                                                (instOfNatNat (nat_lit 16)))
                                                              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 32)
                                                              (instOfNatNat (nat_lit 32)))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@List.length.{0} Nat reports)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                      (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents
                                                          i B j g reports))))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                                  (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B
                                                      j g reports))
                                                  ys t)
                                                (And
                                                  (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                                  (And
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i
                                                      B reserve N j g t)
                                                    (And
                                                      (@Eq.{1} Nat
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 214)
                                                            (instOfNatNat (nat_lit 214))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s
                                                        t)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.loop_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine),
          (∀ (z : Fin i.n),
              And
                (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat (g.natMem (@Fin.val i.n z)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (g.realMem (@Fin.val i.n z)))) →
            ∀ (reports : List.{0} Nat),
              (∀ (address : Nat),
                  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports address →
                    ∃ logical,
                      @Eq.{1} Nat address
                        (DecrAlmostLinearSSSP.Decremental.bankAddress B
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)) →
                ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
                  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (offset : Nat),
                  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
                    DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
                      (∀ (z : Fin i.n),
                          DecrAlmostLinearSSSP.Decremental.PointerValid i
                            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                            (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                        DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset reports s →
                          ∃ cost t ys,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.loop s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                        (@List.length.{0} Nat reports))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                        (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                          (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g
                                            reports))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                    (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g reports))
                                    ys t)
                                  (And
                                    (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j
                                        g t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                            (@List.length.{0} Nat reports))
                                          (@List.nil.{0} Nat) t)
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j q : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q s g.natMem g.realMem →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q t g.natMem g.realMem := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (F e N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78)))) e →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast e)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                N) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                  And
                    (@Eq.{1} Nat
                      (s.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natReg j)))
                    (@Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (g.realReg j))) →
              (∀ (j : Nat),
                  @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                    @LT.lt.{0} Nat instLTNat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                      (And
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                            And
                              (@Eq.{1} Nat
                                (t.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                  ((DecrAlmostLinearSSSP.Decremental.deletionMachine p g e).natReg j)))
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                ((DecrAlmostLinearSSSP.Decremental.deletionMachine p g e).realReg j)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                            (∀ (a : Nat),
                                @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.2.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.host : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j address : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    (∃ r,
        @Eq.{1} Nat address
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @LT.lt.{0} Nat instLTNat address
          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).reports →
        @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N j)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
          (∀ (r : Nat),
              @LT.lt.{0} Nat instLTNat r N →
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N j)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
    (DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary.correct : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct (DecrAlmostLinearSSSP.Decremental.Normalize.input i)
            (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
              (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds)
            g →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct i ds c := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant.step : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.stored : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (v : Fin i.n),
      @LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i
            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant.step : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.maintains : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i) →
              DecrAlmostLinearSSSP.Decremental.Maintains (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)))
                    C)
                  (@OfNat.ofNat.{0} Real (nat_lit 200)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))))))
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead a)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false i := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.online : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program)
        {sourceDs : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)}
        {sourceCs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
        DecrAlmostLinearSSSP.Decremental.OnlineRun p (DecrAlmostLinearSSSP.Decremental.Normalize.input i) sourceDs
            sourceCs →
          ∀ (ds : List.{0} (Fin i.k)),
            @Eq.{1} (List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)) sourceDs
                (@List.map.{0, 0} (Fin i.k)
                  (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
                  (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds) →
              ∃ cs c g,
                And
                  (DecrAlmostLinearSSSP.Decremental.OnlineRun
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) i ds cs)
                  (And
                    (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine sourceCs))
                    (And
                      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
                      (And
                        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                          (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine sourceCs)
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine g))
                        (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g)
                          (And
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                  (@List.length.{0} (Fin i.k) ds)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                      (@List.length.{0} (Fin i.k) ds))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size)))
                            (∀ (j : Nat) (c' g' : DecrAlmostLinearSSSP.Decremental.Machine),
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                                    DecrAlmostLinearSSSP.Decremental.Machine
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c') →
                                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                      Nat DecrAlmostLinearSSSP.Decremental.Machine
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                      sourceCs j)
                                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine g') →
                                  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c' g')))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_initialization : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine),
        DecrAlmostLinearSSSP.Decremental.Ends p
            (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)) g →
          ∃ c,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
                (DecrAlmostLinearSSSP.Decremental.initialMachine
                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) i)
                c)
              (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g)
                (@LE.le.{0} Nat instLENat c.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p) g.work)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_update : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c g g' : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
    DecrAlmostLinearSSSP.Decremental.Ends p (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e) g' →
      ∃ d,
        And
          (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
            (DecrAlmostLinearSSSP.Decremental.deletionMachine
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) c e)
            d)
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i d g')
            (@LE.le.{0} Nat instLENat d.work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g'.work g.work)))
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.eval_code : ∀ (N entry B bank start : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          DecrAlmostLinearSSSP.Decremental.Ends p g final →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                              DecrAlmostLinearSSSP.Decremental.ReportLog start (@List.nil.{0} Nat) s →
                                (∃ r,
                                    @Eq.{1} Nat start
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  ∃ cost steps t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) s cost t)
                                      (And
                                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                          (DecrAlmostLinearSSSP.Decremental.execute p g steps) final)
                                        (And
                                          (@Eq.{1} Nat steps
                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                              g.work))
                                          (And
                                            (@LE.le.{0} Nat instLENat cost
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge p.code)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                      final.work g.work))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                                  (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p g
                                                    steps)
                                                  t)
                                                (∀ (address : Nat),
                                                  (∀ (a : Nat),
                                                      @Ne.{1} Nat address
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          B
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                a)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))))) →
                                                    (∀ (j : Nat),
                                                        @LE.le.{0} Nat instLENat j
                                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                              (@instHSub.{0} Nat instSubNat) final.work g.work) →
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) start
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                j))) →
                                                      And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                                        (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Physical.Valid.erase : ∀ {n k m exponent : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k),
  @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k h m exponent →
    ∀ (e : Fin k),
      (∀ (x : Fin n → Real),
          @Eq.{1} Real
              (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k
                (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h
                  (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
                x)
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (v w : Fin n), @Eq.{1} Real (x v) (x w)) →
        @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k
          (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
          m exponent := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.PointerRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.PointerRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@ite.{1} Nat
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
            (And
              (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                (@ite.{1} Real
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (s.realMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Prepass.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
      ∀ (coefficient stride : Nat),
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) s cost t)
            (And
              (DecrAlmostLinearSSSP.Decremental.Layout.Represents t
                (DecrAlmostLinearSSSP.Decremental.Layout.addresses
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  stride))
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                              coefficient)
                            stride)
                          (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))
                      (∀ (address : Nat),
                        (∀ (a : Nat),
                            @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Prepass.nat_frame : ∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
      @Even.{0} Nat instAddNat k →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Prepass.real_frame : ∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReadoutCertificate.correct : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s →
    And
      (@Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s b.input.source)
        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
      (∀ (v : Fin b.input.n),
        And
          (@LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
              (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (b.input.weight e))
              b.input.source v)
            (@DecrAlmostLinearSSSP.Decremental.State.output b s v))
          (And
            (@LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (ENNReal.ofReal
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (b.input.weight e))
                  b.input.source v)))
            (Iff
              (@Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
                (@Top.top.{0} ENNReal ENNReal.instTop))
              (Not
                (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b s) b.input.source v))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.RecordHeader.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.RecordHeader.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 216) (instOfNatNat (nat_lit 216))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))))))
                (And
                  (@Eq.{1} Real
                    ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 128)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 128)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B bank a N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast a)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    N) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ReportDecode.code
                      s cost t)
                    (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) a)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                        (∀ (address : Nat),
                          (∀ (r : Nat),
                              @Ne.{1} Nat address
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                              (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.ReportDecode.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 206) (instOfNatNat (nat_lit 206))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.initializeState b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.refresh b s e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.refresh_validity : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b), DecrAlmostLinearSSSP.Decremental.RefreshValidity b s e := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.stop : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
      (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
        (@DecrAlmostLinearSSSP.Decremental.State.y b s) (@DecrAlmostLinearSSSP.Decremental.State.cache b s)
        (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
        (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
        (@DecrAlmostLinearSSSP.Decremental.State.pending b s) Bool.true
        (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) (@DecrAlmostLinearSSSP.Decremental.State.history b s)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
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
                    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.gradient_nonzero : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.refresh b s e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle_count_near_linear : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 1040)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 1040) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1039) (instOfNatNat (nat_lit 1039)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1038) (instOfNatNat (nat_lit 1038)))))))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.size))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b.input.accuracy) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep.completed : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.State b},
      DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
        DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
          @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b t) Bool.true →
            DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep.decreases : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.State b},
      DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
        DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
          @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K t)
            (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep.drained : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.State b},
  DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b t) Bool.true →
      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b t)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.size →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                (@Fin.val i.n i.source) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                    (DecrAlmostLinearSSSP.Decremental.bankFactor
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                        (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88)))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                  i.n))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                    i.k))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (DecrAlmostLinearSSSP.Decremental.bankFactor
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                        (@Fin.val i.n i.source)))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor
                                            (s.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                          (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                      (∀ (address : Nat),
                                        (∀ (a : Nat),
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledReadout.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @LE.le.{0} Nat instLENat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F flag) →
              @Eq.{1} Real (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))) r →
                (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.ScaledReadout.code s cost t)
                      (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) flag)
                          (And
                            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta r))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                              (And
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
                                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                    (@instHMul.{0} ENNReal
                                      (@Distrib.toMul.{0} ENNReal
                                        (@instDistribOfSemiring.{0} ENNReal
                                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                    (ENNReal.ofReal delta)
                                    (@ite.{1} ENNReal
                                      (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (instDecidableEqNat flag
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@Top.top.{0} ENNReal ENNReal.instTop) (ENNReal.ofReal r))))
                                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                  (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
          (And
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
              (DecrAlmostLinearSSSP.Decremental.SelectedRead.value s))
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.nat_register : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (DecrAlmostLinearSSSP.Decremental.shadowReg a)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F x),
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := g.pc, realReg := g.realReg,
          natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg a x, realMem := g.realMem,
          natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.real_register : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a : Nat) (x : Real),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc,
          realReg :=
            @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realReg
              (DecrAlmostLinearSSSP.Decremental.shadowReg a) x,
          natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
          work := c.work }
        { pc := g.pc, realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg a x,
          natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault,
          work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.eval_code : ∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              t)
            (And
              (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j N →
                  And
                    (@Eq.{1} Nat
                      (t.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@Eq.{1} Real
                      (t.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
              (∀ (address : Nat),
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N)
              k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.real_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SourceCall.eval_code : ∀ (N entry B bank : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          DecrAlmostLinearSSSP.Decremental.Ends p g final →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                              (∃ r,
                                  @Eq.{1} Nat
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                final.work g.work))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                            final.work)
                                          (And
                                            (∀ (j : Nat),
                                              @LT.lt.{0} Nat instLTNat j N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                      (final.natReg j)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (final.realReg j)))
                                            (∀ (address : Nat),
                                              (∀ (a : Nat),
                                                  @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            a)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))))) →
                                                @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                          (instOfNatNat (nat_lit 106))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                                  (∀ (j : Nat),
                                                      @LT.lt.{0} Nat instLTNat j N →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (s.natReg
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                (instOfNatNat (nat_lit 50))))
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j))) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.SourceSetup.eval_code : ∀ (N entry B F : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          ∃ t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry) s
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N))
                                t)
                              (And (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)
                                (And
                                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    B)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
                                      (And
                                        (@Eq.{1} Real
                                          (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                          (@Nat.cast.{0} Real Real.instNatCast F))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                            (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.eval_code : ∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          t)
        (And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (And
            (∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j N →
                And
                  (@Eq.{1} Nat
                    (t.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                    (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
                  (@Eq.{1} Real
                    (t.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                    (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))))
            (∀ (address : Nat),
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.nat_frame : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k → @Eq.{1} Nat (t.natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.real_frame : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k → @Eq.{1} Real (t.realReg k) (s.realReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.command_ends : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
          (DecrAlmostLinearSSSP.Decremental.Structured.compile cmd start) →
        @Eq.{1} Nat c.pc start →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data (DecrAlmostLinearSSSP.Decremental.Structured.data c)
              s →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Bool c.fault Bool.false →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize cmd)))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      DecrAlmostLinearSSSP.Decremental.Instruction.halt) →
                  ∃ d,
                    And (DecrAlmostLinearSSSP.Decremental.Ends p c d)
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
                          (DecrAlmostLinearSSSP.Decremental.Structured.data d) t)
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_add : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.add d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.loop_wellFounded_credit : ∀ {σ : Type} (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (repr : σ → DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop) (rel : σ → σ → Prop),
  @WellFounded.{1} σ rel →
    ∀ (credit : σ → Nat),
      (∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          repr q s →
            test.holds s →
              ∃ q' t cost,
                And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
                  (And (repr q' t)
                    (And (rel q' q)
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (credit q))
                        (credit q'))))) →
        ∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          repr q s →
            ∃ q' t cost,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
                (And (repr q' t)
                  (And (Not (test.holds t))
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost (credit q))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (credit q')
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_init : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile init
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_init_halt : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_update : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile update
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_update_halt : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize update)))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b → DecrAlmostLinearSSSP.Decremental.TailFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame b →
      DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable b → DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (count N B bank tail origin logical high : Nat)
  (delta cutoff : Real) (raw natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff s →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))) origin →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
            (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))) count →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))
                B →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  delta →
                (∀ (address : Nat), @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j count →
                        @LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast
                            (raw
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            N)) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j count →
                          @LE.le.{0} Real Real.instLE
                            (@Nat.cast.{0} Real Real.instNatCast
                              (raw
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              N)) →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j count →
                            @LE.le.{0} Real Real.instLE
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (raw
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                cutoff →
                              @LE.le.{0} Real Real.instLE
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@Nat.cast.{0} Real Real.instNatCast
                                    (raw
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                  delta)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  N)) →
                        ∃ cost t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.TapeCopy.code s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                                  (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count
                                    natural origin logical)
                                  real)
                                (And (DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff t)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count)))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                        (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (And
                                          (∀ (address : Nat),
                                            @LE.le.{0} Nat instLENat address B →
                                              @Eq.{1} Nat (t.natMem address) (raw address))
                                          (∀ (address : Nat),
                                            (∀ (j : Nat),
                                                @LT.lt.{0} Nat instLTNat j
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                      count) →
                                                  @Ne.{1} Nat address
                                                    (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        logical j))) →
                                              (∀ (a : Nat),
                                                  @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 48)
                                                            (instOfNatNat (nat_lit 48))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          a))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.ends_of_bound : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine} {N : Nat},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      DecrAlmostLinearSSSP.Decremental.Ends p c d → DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N d := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.cache_total_upper : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @LE.le.{0} Real Real.instLE (∑ e, @DecrAlmostLinearSSSP.Decremental.State.cache b s e)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.A b))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Nat.cast.{0} Real Real.instNatCast b.input.size)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (DecrAlmostLinearSSSP.Decremental.kappa b)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.computableCutQuality_ge_32 : ∀ (N m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N →
    @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.1.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead_subpolynomial : ∀ (h Γ a : Nat → Real) (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial h →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial Γ →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.core_A_near_linear : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.A b)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 65)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 65) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))))))
        (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size))
      b.input.accuracy) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.core_cache_total_capacityBound : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.A b))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast b.input.size)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (@HPow.hPow.{0, 0, 0} Real Int Real
      (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
      (DecrAlmostLinearSSSP.Decremental.kappa b)
      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.core_capacityBound_range : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
    (@LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Max.max.{0} Real Real.instMax
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.cutInitial_zero_tail : ∀ {n k N : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (h : DecrAlmostLinearSSSP.Decremental.Physical n k)
  (m : Nat) (ξ cap : Real),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N (@DecrAlmostLinearSSSP.Decremental.cutInitial n k p h m ξ cap) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.cutRequest_zero_tail : ∀ {n k N : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (op : DecrAlmostLinearSSSP.Decremental.CutOp n k),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p c op) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.exists_computable_cut_quality_envelope : ∀ (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∃ N,
      And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N)
        (∀ (m : Nat),
          @LE.le.{0} Real Real.instLE
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 5)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 6)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (Real.log
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          m)))))))
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.logicalCount_le : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.logicalCount b)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.reportVolume_append : ∀ (cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine) (current final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
      (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine current) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.reportVolume
        (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Machine))
          cs
          (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine final
            (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.reportVolume cs) (DecrAlmostLinearSSSP.Decremental.reportCount final)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.runtime_indexed_physical_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    ∀ {l : Nat} (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)),
      @LE.le.{0} Nat instLENat l
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) →
        @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n l
          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.1.1.2
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore
open DecrAlmostLinearSSSP.Decremental
open Structured
structure CutSession (impl : CutImplementation) (n k m exponent : ℕ) [NeZero n] (first : Machine)
    (K ξ h Γ init : ℝ) : Prop where
  total : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    ∀ c, cs.getLast? = some c → ∀ op, CutOp.Valid (impl.view n k c) op →
      (applyPhysical (impl.view n k c).physical op).Valid m exponent →
      ∃ d, Ends impl.program (cutRequest impl.program c op) d ∧
        CutTransition K ξ (impl.view n k c) op d (impl.view n k d)
  transition : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    ∀ (j : ℕ) c d op, cs[j]? = some c → cs[j+1]? = some d → ops[j]? = some op →
      CutTransition K ξ (impl.view n k c) op d (impl.view n k d)
  reports : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    (reportVolume cs : ℝ) ≤ Γ*(toggleVolume ops)/ξ
  work : ∀ ops cs, CutRun impl n k m exponent first ops cs →
    ∀ last, cs.getLast? = some last →
      (last.work+6*ops.length : ℕ) ≤ init+h*((ops.length : ℝ)+reportVolume cs)
end DecrAlmostLinearSSSP.Decremental.NonemptyCore
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
structure Context (b : Core) (B N m exponent : ℕ) (impl : CutImplementation)
    (K0 ξ h Γ init : ℝ) (s : Data) where
  first : Machine
  current : Machine
  ops : List (CutOp b.input.n (logicalCount b))
  machines : List Machine
  session : CutSession impl b.input.n (logicalCount b) m exponent first K0 ξ h Γ init
  run : CutRun impl b.input.n (logicalCount b) m exponent first ops machines
  last : machines.getLast? = some current
  zeroTail : ZeroRegisterTail N current
  image : CoreSource.Image B (CoreMemory.sourceRecord b B) N current s
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def Context.of_image {b : Core} {B N m exponent : ℕ} {K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {s t : Data} (ctx : Context b B N m exponent impl K0 ξ h Γ init s)
    (ht : CoreSource.Image B (CoreMemory.sourceRecord b B) N ctx.current t) :
    Context b B N m exponent impl K0 ξ h Γ init t :=
  ⟨ctx.first,ctx.current,ctx.ops,ctx.machines,ctx.session,ctx.run,ctx.last,ctx.zeroTail,ht⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
structure Repr (b : Core) (B N offset : ℕ) (K K0 h Γ init : ℝ)
    (impl : CutImplementation) (first : Machine) (active : Finset (Fin b.input.k)) (q : Snapshot b) (s : Data) : Prop where
  bounds : RuntimeBounds b K q.state
  host : CoreHost.Image b B K q.state s
  model : CutModel b (logicalIndexEquiv b) q.state (impl.view b.input.n (logicalCount b) q.current)
  run : CutRun impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68) first q.ops q.machines
  last : q.machines.getLast? = some q.current
  zeroTail : ZeroRegisterTail N q.current
  image : CoreSource.Image B (CoreMemory.sourceRecord b B) N q.current s
  running : s.natReg 650 = (if q.state.stopped then 0 else 1)
  threshold : s.realReg 520 = -1/(4*K)
  debt : CoreRepair.OperationDebt b q.state q.ops.length (reportVolume q.machines) offset
  toggleCount : toggleVolume q.ops = q.state.toggles
  complete : q.state.stopped = true → ReadoutCertificate b q.state
  active_eq : q.state.active = active
  drained : q.state.stopped = true → q.state.pending = []
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def Repr.context {b : Core} {B N offset : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {first : Machine} {active : Finset (Fin b.input.k)} {q : Snapshot b} {s : Data}
    (hSession : CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68) first K0 (K^(-2 : ℤ)) h Γ init)
    (hq : Repr b B N offset K K0 h Γ init impl first active q s) :
    Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s :=
  ⟨first,q.current,q.ops,q.machines,hSession,hq.run,hq.last,hq.zeroTail,hq.image⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
structure Ready (b : Core) (B N : ℕ) (K K0 h Γ init : ℝ) (impl : CutImplementation)
    (deleted : List (Fin b.input.k)) (s : Data) where
  state : State b
  context : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s
  host : CoreHost.Image b B K state s
  bounds : RuntimeBounds b K state
  model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) context.current)
  stopped : state.stopped = true
  certificate : ReadoutCertificate b state
  pending : state.pending = []
  active : state.active = live deleted
  debt : CoreRepair.OperationDebt b state context.ops.length (reportVolume context.machines) (6*deleted.length)
  toggles : toggleVolume context.ops = state.toggles
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
def Ready.credit {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {deleted : List (Fin b.input.k)} {s : Data} (r : Ready b B N K K0 h Γ init impl deleted s) : ℕ :=
  CoreNativeCut.credit b N impl.program r.state r.context.current r.context.ops r.context.machines
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
noncomputable def Ready.external {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {deleted : List (Fin b.input.k)} {s : Data} (r : Ready b B N K K0 h Γ init impl deleted s)
    (hB : b.input.n ≤ B) (value : ℕ) :
    Ready b B N K K0 h Γ init impl deleted {s with natReg := Function.update s.natReg 5 value} :=
  let ctx := r.context.of_image (CoreDeletion.source_input b B N r.context.current s value r.context.image)
  ⟨r.state,ctx,CoreDeletion.host_input b B K r.state s value r.host hB,r.bounds,r.model,r.stopped,r.certificate,r.pending,r.active,r.debt,r.toggles⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
noncomputable def Completed (b : Core) (qualityPower : ℕ) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (deleted : List (Fin b.input.k)) (c : Machine) : Prop :=
  ∃ ready : Ready b (b.input.n+3*b.input.k+2) (CoreInitialize.sourceRegisters impl.program)
      (computableCutQuality qualityPower (2*b.input.size)) K0 h Γ init impl deleted (Structured.data c),
    ((c.work+6*deleted.length : ℕ) : ℝ) ≤ initialBudget b qualityPower impl.program init+(ready.credit : ℝ)
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore
open DecrAlmostLinearSSSP.Decremental
open Structured
lemma ImplementsCut.initialize_session {impl : CutImplementation} {m exponent : ℕ} {K h Γ init ξ : ℝ}
    (himpl : ImplementsCut impl m exponent K h Γ init ξ)
    {n k : ℕ} [NeZero n] (graph : Physical n k) (capacityBound : ℝ) (hv : graph.Valid m exponent)
    (hcap : 0 < capacityBound) (hcapbound : capacityBound ≤ (max 2 m : ℝ)^exponent)
    (hu : ∀ e ∈ graph.active, graph.u e ≤ capacityBound) :
    ∃ first, Ends impl.program (cutInitial impl.program graph m ξ capacityBound) first ∧
      (impl.view n k first).physical = graph ∧ (impl.view n k first).y = 0 ∧
      (impl.view n k first).baseline = 0 ∧ (impl.view n k first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧ CutSession impl n k m exponent first K ξ h Γ init := by
  obtain ⟨first,he,hp,hy,hb,hh,hw,hr⟩ := himpl n k graph capacityBound hv hcap hcapbound hu
  refine ⟨first,he,hp,hy,hb,hh,hw,⟨?_,?_,?_,?_⟩⟩
  · intro ops cs hc
    exact (hr ops cs hc).1
  · intro ops cs hc
    exact (hr ops cs hc).2.1
  · intro ops cs hc
    have ha := (hr ops cs hc).2.2.1
    dsimp only [reportVolume,toggleVolume]
    convert ha using 1
    congr 5
  · intro ops cs hc last hl
    exact (hr ops cs hc).2.2.2 last hl
end DecrAlmostLinearSSSP.Decremental.NonemptyCore
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma call {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ} {state : State b}
    {impl : CutImplementation} {first current : Machine} {ops : List (CutOp b.input.n (logicalCount b))}
    {cs : List Machine} (hSession : CutSession impl b.input.n (logicalCount b) m exponent first K0 ξ h Γ init)
    (hRun : CutRun impl b.input.n (logicalCount b) m exponent first ops cs)
    (hLast : cs.getLast? = some current) (op : CutOp b.input.n (logicalCount b))
    (hValid : CutOp.Valid (impl.view b.input.n (logicalCount b) current) op)
    (hBounds : (applyPhysical (impl.view b.input.n (logicalCount b) current).physical op).Valid m exponent)
    (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hZero : ZeroRegisterTail N current) (s : Data) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (setup : Cmd) (setupCost : ℕ)
    (hPreserves : CoreHost.Preserves b B K state setup)
    (hSetup : ∃ u, Eval setup s setupCost u ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N (cutRequest impl.program current op) u) :
    ∃ cost t final,
      Eval (.seq setup (SourceCall.code N impl.program.update impl.program)) s cost t ∧
      cost ≤ setupCost+(dispatchCharge impl.program.code+2)*(final.work-current.work)+8*N+15 ∧
      CoreHost.Image b B K state t ∧ CoreSource.Image B (CoreMemory.sourceRecord b B) N final t ∧
      ShadowDataRep B 2 t final ∧ ZeroRegisterTail N final ∧
      Ends impl.program (cutRequest impl.program current op) final ∧
      CutTransition K0 ξ (impl.view b.input.n (logicalCount b) current) op final
        (impl.view b.input.n (logicalCount b) final) ∧
      CutRun impl b.input.n (logicalCount b) m exponent first (ops++[op]) (cs++[final]) := by
  obtain ⟨final,hEnd,hTransition⟩ := hSession.total ops cs hRun current hLast op hValid hBounds
  obtain ⟨u,hu,hus⟩ := hSetup
  have hum := hPreserves s setupCost u host hu
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hz := cutRequest_zero_tail impl.program current op hN hZero
  have hpc : (cutRequest impl.program current op).pc = impl.program.update := by cases op <;> rfl
  have hhalt : (cutRequest impl.program current op).halted = false := by cases op <;> rfl
  have hfault : (cutRequest impl.program current op).fault = false := by cases op <;> rfl
  have hw : (cutRequest impl.program current op).work = current.work := by cases op <;> rfl
  obtain ⟨cc,t,ht,hcc,hts,htrep,htframe⟩ := hus.call B (CoreMemory.sourceRecord b B) N impl.program.update
    impl.program (cutRequest impl.program current op) final u hBound hodd hpc hhalt hfault hz hEnd
  have htm := CoreHost.source_frame b B N impl.program.update K state impl.program u t cc hum hB ht htframe
  refine ⟨setupCost+cc,t,final,Eval.seq hu ht,by rw [hw] at hcc;omega,
    htm,hts,htrep,hz.ends_of_bound hBound hEnd,hEnd,hTransition,?_⟩
  exact CutRun.next hRun hLast op hValid hBounds hEnd
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.advance {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (op : CutOp b.input.n (logicalCount b))
    (hv : CutOp.Valid (impl.view b.input.n (logicalCount b) ctx.current) op)
    (hb : (applyPhysical (impl.view b.input.n (logicalCount b) ctx.current).physical op).Valid m exponent)
    (setup : Cmd) (setupCost : ℕ) (hp : CoreHost.Preserves b B K state setup)
    (hs : ∃ u, Eval setup s setupCost u ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N (cutRequest impl.program ctx.current op) u) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (.seq setup (SourceCall.code N impl.program.update impl.program)) s cost t ∧
      cost ≤ setupCost+(dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+15 ∧
      CoreHost.Image b B K state t ∧
      ShadowDataRep B 2 t next.current ∧
      CutTransition K0 ξ (impl.view b.input.n (logicalCount b) ctx.current) op next.current
        (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[op] ∧ next.machines = ctx.machines++[next.current] ∧ ctx.current.work ≤ next.current.work := by
  obtain ⟨cost,t,final,he,hcost,htm,hts,htrep,htzero,hEnd,hTransition,hRun⟩ :=
    call ctx.session ctx.run ctx.last op hv hb hN hBound ctx.zeroTail s host hB setup setupCost hp hs
  let next : Context b B N m exponent impl K0 ξ h Γ init t :=
    ⟨ctx.first,final,ctx.ops++[op],ctx.machines++[final],ctx.session,hRun,by simp,htzero,hts⟩
  have hmono : ctx.current.work ≤ final.work := by
    have hw : (cutRequest impl.program ctx.current op).work = ctx.current.work := by cases op <;> rfl
    simpa only [hw] using hEnd.work_mono
  exact ⟨cost,t,next,he,hcost,htm,htrep,hTransition,rfl,rfl,rfl,hmono⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.report_bound {b : Core} {B N m exponent : ℕ} {K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {s : Data} (ctx : Context b B N m exponent impl K0 ξ h Γ init s) :
    (reportVolume ctx.machines : ℝ) ≤ Γ*toggleVolume ctx.ops/ξ :=
  ctx.session.reports ctx.ops ctx.machines ctx.run
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.work_bound {b : Core} {B N m exponent : ℕ} {K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {s : Data} (ctx : Context b B N m exponent impl K0 ξ h Γ init s) :
    (ctx.current.work+6*ctx.ops.length : ℕ) ≤ init+h*((ctx.ops.length : ℝ)+reportVolume ctx.machines) :=
  ctx.session.work ctx.ops ctx.machines ctx.run ctx.current ctx.last
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.query {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (source : ℕ) (h630 : source ≠ 630) (h632 : source ≠ 632)
    (v : Fin b.input.n) (hv : s.natReg source = 2*v.val) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (queryCode N source impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+22 ∧
      CoreHost.Image b B K state t ∧
      impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current ∧
      t.realReg 29 = (impl.view b.input.n (logicalCount b) ctx.current).y v ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.queryY v] ∧ next.machines = ctx.machines++[next.current] ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hsetup := CoreRequest.query_eval (k := logicalCount b) B (CoreMemory.sourceRecord b B) N source impl.program ctx.current s v
    ctx.image hodd h630 h632 hv
  obtain ⟨cost,t,next,he,hcost,htm,hrep,htrans,hfirst,hops,hcs,hmono⟩ := ctx.advance host hB hN hBound (.queryY v)
    trivial hb (CoreRequest.queryCode source) 7 (CoreHost.preserves_query b B K state hB source h630) hsetup
  have hteq : impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current := htrans.2.1
  have hvalue : next.current.realReg 10 = (impl.view b.input.n (logicalCount b) ctx.current).y v := htrans.2.2.1
  have hnative : t.realReg 29 = next.current.realReg 10 := by
    simpa only [shadowReg,Data.machine] using hrep.realReg 10
  have hR : reportVolume next.machines = reportVolume ctx.machines := by
    rw [hcs,reportVolume_append ctx.machines ctx.current next.current ctx.last,htrans.2.2.2,Nat.add_zero]
  exact ⟨cost,t,next,he,by omega,htm,hteq,hnative.trans hvalue,hfirst,hops,hcs,hmono,hR⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.capture_query {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (source dest : ℕ) (h630 : source ≠ 630) (h632 : source ≠ 632)
    (hdest : 535 ≤ dest) (heven : dest%2 = 0)
    (v : Fin b.input.n) (hv : s.natReg source = 2*v.val) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (captureQueryCode N source dest impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+23 ∧
      CoreHost.Image b B K state t ∧
      impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current ∧
      t.realReg dest = (impl.view b.input.n (logicalCount b) ctx.current).y v ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.queryY v] ∧ next.machines = ctx.machines++[next.current] ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  obtain ⟨cq,q,qctx,hq,hcq,hqm,hview,hvalue,hfirst,hops,hcs,hmono,hR⟩ := ctx.query host hB hN hBound hb source h630 h632 v hv
  let t : Data := {q with realReg := Function.update q.realReg dest (q.realReg 29+q.realReg 56)}
  have ht : Eval (add dest 29 56) q 1 t := eval_add q dest 29 56
  have htm : CoreHost.Image b B K state t := hqm.command_frame b B K state hB ht
    (by simp [NoMemory,NoStore,add])
    (by intro k hk;simp [NatFrame,add,writesNat])
    (by intro k hk;simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
        simp [RealFrame,add,writesReal];omega)
  have hts : CoreSource.Image B (CoreMemory.sourceRecord b B) N qctx.current t :=
    qctx.image.real_register B _ N dest _ qctx.current q heven
  let next := qctx.of_image hts
  refine ⟨cq+1,t,next,Eval.seq hq ht,by dsimp [next,Context.of_image];omega,htm,hview,?_,hfirst,hops,hcs,hmono,hR⟩
  change Function.update q.realReg dest (q.realReg 29+q.realReg 56) dest = _
  rw [Function.update_self,hqm.captured.zeroR,add_zero,hvalue]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.labels {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (a z : Fin b.input.n) (ha : s.natReg 636 = 2*a.val) (hz : s.natReg 638 = 2*z.val) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (labelsCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+16*N+46 ∧
      CoreHost.Image b B K state t ∧
      CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) next.current) ∧
      t.realReg 608 = state.y a ∧ t.realReg 610 = state.y z ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.queryY a,.queryY z] ∧
      (∃ middle : Machine, next.machines = ctx.machines++[middle,next.current]) ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  obtain ⟨ca,u,uctx,hu,hca,hum,huview,huvalue,hufirst,huops,hucs,humono,huR⟩ :=
    ctx.capture_query host hB hN hBound hb 636 608 (by omega) (by omega) (by omega) (by decide) a ha
  have huz : u.natReg 638 = 2*z.val :=
    (hu.nat_frame (capture_nat_frame N 636 608 impl.program 638 (by omega) (by decide)
      (by omega) (by omega) (by omega) (by omega))).trans hz
  have hub : (impl.view b.input.n (logicalCount b) uctx.current).physical.Valid m exponent := by rw [huview];exact hb
  obtain ⟨cz,t,next,ht,hcz,htm,htview,htvalue,htfirst,htops,htcs,htmono,htR⟩ :=
    uctx.capture_query hum hB hN hBound hub 638 610 (by omega) (by omega) (by omega) (by decide) z huz
  have hview : impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current := htview.trans huview
  have hsum : next.current.work-ctx.current.work =
      (uctx.current.work-ctx.current.work)+(next.current.work-uctx.current.work) := by omega
  have hcost : ca+cz ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+16*N+46 := by
    rw [hsum,Nat.mul_add]
    omega
  have ht608 : t.realReg 608 = state.y a := by
    rw [ht.real_frame (capture_real_frame N 638 610 impl.program 608 (by omega) (by decide) (by omega)),huvalue,model.y]
  have ht610 : t.realReg 610 = state.y z := by rw [htvalue,huview,model.y]
  have hnextops : next.ops = ctx.ops++[.queryY a,.queryY z] := by rw [htops,huops];simp [List.append_assoc]
  have hnextcs : next.machines = ctx.machines++[uctx.current,next.current] := by rw [htcs,hucs];simp [List.append_assoc]
  refine ⟨ca+cz,t,next,Eval.seq hu ht,hcost,htm,by rw [hview];exact model,
    ht608,ht610,htfirst.trans hufirst,hnextops,?_,humono.trans htmono,htR.trans huR⟩
  exact ⟨uctx.current,hnextcs⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.physical_refresh_validated {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (validity : RefreshValidity b state e) (he : s.natReg 560 = CoreMemory.encodedEdge b e)
    (ha : s.natReg 626 = (tail b e).val) (hz : s.natReg 628 = (head b e).val)
    (hf : s.realReg 612 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e)
    (hd : s.realReg 614 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (physicalRefreshCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+24*N+85 ∧
      CoreHost.Image b B K state t ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧
      next.ops = ctx.ops++[.erase (logicalIndexEquiv b e),
        .insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e),
        .paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)] ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hpvalid := validity
  have hEraseValid := model.erase_valid b (logicalIndexEquiv b) state _ e
  have hEraseBounds : (applyPhysical (impl.view b.input.n (logicalCount b) ctx.current).physical
      (.erase (logicalIndexEquiv b e))).Valid (2*b.input.size) (4*b.weightExponent+68) := by
    rw [model.physical];exact hpvalid.1
  have hsetup1 := CoreRequest.erase_eval (n := b.input.n) B (CoreMemory.sourceRecord b B) N impl.program ctx.current s
    (logicalIndexEquiv b e) ctx.image hodd he
  obtain ⟨c1,u,uctx,hu,hc1,hum,hrep1,ht1,hfirst1,hops1,hcs1,hmono1⟩ :=
    ctx.advance host hB hN hBound _ hEraseValid hEraseBounds CoreRequest.eraseCode 7
      (CoreHost.preserves_erase b B K state hB) hsetup1
  have hua : u.natReg 626 = (tail b e).val :=
    (hu.nat_frame (erase_nat_frame N impl.program 626 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))).trans ha
  have huz : u.natReg 628 = (head b e).val :=
    (hu.nat_frame (erase_nat_frame N impl.program 628 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))).trans hz
  have hue : u.natReg 560 = CoreMemory.encodedEdge b e :=
    (hu.nat_frame (erase_nat_frame N impl.program 560 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))).trans he
  have huf : u.realReg 612 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e :=
    (hu.real_frame (erase_real_frame N impl.program 612 (by omega) (by decide))).trans hf
  have hInsertValid := model.insert_valid b (logicalIndexEquiv b) state _ _ K0 ξ uctx.current e ht1
  have hInsertBounds : (applyPhysical (impl.view b.input.n (logicalCount b) uctx.current).physical
      (.insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e))).Valid
      (2*b.input.size) (4*b.weightExponent+68) := by
    rw [ht1.1,model.physical];exact hpvalid.2.1
  have hsetup2 := CoreRequest.insert_eval B (CoreMemory.sourceRecord b B) N impl.program uctx.current u
    (logicalIndexEquiv b e) (tail b e) (head b e) _ uctx.image hodd hue hua huz huf
  obtain ⟨c2,v,vctx,hv,hc2,hvm,hrep2,ht2,hfirst2,hops2,hcs2,hmono2⟩ :=
    uctx.advance hum hB hN hBound _ hInsertValid hInsertBounds CoreRequest.insertCode 18
      (CoreHost.preserves_insert b B K state hB) hsetup2
  have hva : v.natReg 626 = (tail b e).val :=
    (hv.nat_frame (insert_nat_frame N impl.program 626 (by omega) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))).trans hua
  have hvz : v.natReg 628 = (head b e).val :=
    (hv.nat_frame (insert_nat_frame N impl.program 628 (by omega) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))).trans huz
  have hvd : v.realReg 614 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e :=
    (hv.real_frame (insert_real_frame N impl.program 614 (by omega) (by decide))).trans
      ((hu.real_frame (erase_real_frame N impl.program 614 (by omega) (by decide))).trans hd)
  have hPairedBounds : (applyPhysical (impl.view b.input.n (logicalCount b) vctx.current).physical
      (.paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e))).Valid
      (2*b.input.size) (4*b.weightExponent+68) := by
    rw [ht2.1,ht1.1,model.physical];exact hpvalid.2.2.2
  have hsetup3 := CoreRequest.paired_eval (k := logicalCount b) B (CoreMemory.sourceRecord b B) N impl.program vctx.current v
    (head b e) (tail b e) _ vctx.image hodd hvz hva hvd
  obtain ⟨c3,t,next,ht,hc3,htm,hrep3,ht3,hfirst3,hops3,hcs3,hmono3⟩ :=
    vctx.advance hvm hB hN hBound (.paired (head b e) (tail b e)
      (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)) trivial hPairedBounds CoreRequest.pairedCode 15
      (CoreHost.preserves_paired b B K state hB) hsetup3
  have hmodel := model.refresh b (logicalIndexEquiv b) state e _ _ _ _ K0 ξ
    uctx.current vctx.current next.current ht1 ht2 ht3
  have hsum : next.current.work-ctx.current.work = (uctx.current.work-ctx.current.work)+
      ((vctx.current.work-uctx.current.work)+(next.current.work-vctx.current.work)) := by omega
  have hcost : c1+(c2+c3) ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+24*N+85 := by
    rw [hsum,Nat.mul_add,Nat.mul_add]
    omega
  have hR1 : reportVolume uctx.machines = reportVolume ctx.machines := by
    rw [hcs1,reportVolume_append ctx.machines ctx.current uctx.current ctx.last,ht1.2.2.1,Nat.add_zero]
  have hR2 : reportVolume vctx.machines = reportVolume uctx.machines := by
    rw [hcs2,reportVolume_append uctx.machines uctx.current vctx.current uctx.last,ht2.2.2.1,Nat.add_zero]
  have hR3 : reportVolume next.machines = reportVolume vctx.machines := by
    rw [hcs3,reportVolume_append vctx.machines vctx.current next.current vctx.last,ht3.2.2.1,Nat.add_zero]
  refine ⟨c1+(c2+c3),t,next,Eval.seq hu (Eval.seq hv ht),hcost,htm,hmodel,
    hfirst3.trans (hfirst2.trans hfirst1),?_,hmono1.trans (hmono2.trans hmono3),hR3.trans (hR2.trans hR1)⟩
  rw [hops3,hops2,hops1]
  simp [List.append_assoc]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.physical_refresh {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 0 < K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (he : s.natReg 560 = CoreMemory.encodedEdge b e)
    (ha : s.natReg 626 = (tail b e).val) (hz : s.natReg 628 = (head b e).val)
    (hf : s.realReg 612 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e)
    (hd : s.realReg 614 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (physicalRefreshCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+24*N+85 ∧
      CoreHost.Image b B K state t ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧
      next.ops = ctx.ops++[.erase (logicalIndexEquiv b e),
        .insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e),
        .paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)] ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  exact ctx.physical_refresh_validated host hB hN hBound model e
    (bounds.refresh_validity b K hK state e) he ha hz hf hd
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.refresh_head_validated {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (xs : List (Edge b)) (hpend : state.pending = e::xs)
    (beforeValid : (indexedPhysical b state (logicalIndexEquiv b)).Valid (2*b.input.size) (4*b.weightExponent+68))
    (refreshValid : RefreshValidity b state e) (afterBounds : RuntimeBounds b K (refresh b state e))
    (he : s.natReg 560 = CoreMemory.encodedEdge b e) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (refreshCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 ∧
      CoreHost.Image b B K (refresh b state e) t ∧ RuntimeBounds b K (refresh b state e) ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧
      next.ops = ctx.ops++[.queryY (tail b e),.queryY (head b e),.erase (logicalIndexEquiv b e),
        .insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e),
        .paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)] ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  let r := CoreRefreshRead.result s
  have hr : Eval CoreRefreshRead.code s 19 r := CoreRefreshRead.eval_code s
  obtain ⟨hrm,hrload,hraddr,hrtail,hrhead⟩ := CoreRefreshRead.correct b B K state e s host hB he
  have hrs := CoreRefreshRead.source_frame b B N ctx.current s ctx.image
  let rctx := ctx.of_image hrs
  have hrmodel : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) rctx.current) := model
  have hrvalid : (impl.view b.input.n (logicalCount b) rctx.current).physical.Valid (2*b.input.size) (4*b.weightExponent+68) := by
    rw [hrmodel.physical]
    exact beforeValid
  obtain ⟨cl,l,lctx,hl,hcl,hlm,hlmodel,hltail,hlhead,hlfirst,hlops,hlcs,hlmono,hlR⟩ :=
    rctx.labels hrm hB hN hBound hrvalid hrmodel (tail b e) (head b e) hrtail hrhead
  have hlload := labels_loaded hl hrload
  have hladdr := labels_addresses hl hraddr
  let c := CoreRefresh.result l
  have hc : Eval CoreRefresh.code l 7 c := CoreRefresh.eval_code l hlm.captured.zeroR
  obtain ⟨hcm,hcs,hcf,hcd,hcsample⟩ := CoreRefresh.computed b B N K state e lctx.current l hlm lctx.image hB hlload hltail hlhead
  let cctx := lctx.of_image hcs
  have hce : c.natReg 560 = CoreMemory.encodedEdge b e := by
    rw [hc.nat_frame (CoreRefresh.nat_frame 560),hl.nat_frame (labels_nat_frame N impl.program 560
      (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)),hr.nat_frame (CoreRefreshRead.nat_frame 560 (Or.inl (by omega)))]
    exact he
  have hca : c.natReg 626 = (tail b e).val := (hc.nat_frame (CoreRefresh.nat_frame 626)).trans hlload.tail
  have hcz : c.natReg 628 = (head b e).val := (hc.nat_frame (CoreRefresh.nat_frame 628)).trans hlload.head
  obtain ⟨cp,p,pctx,hp,hcp,hpm,hpmodel,hpfirst,hpops,hpmono,hpR⟩ :=
    cctx.physical_refresh_validated hcm hB hN hBound hlmodel e refreshValid hce hca hcz hcf hcd
  have hpn (k : ℕ) (hk : k ∈ ([568,578,626,648] : List ℕ)) : p.natReg k = l.natReg k := by
    have hframe : NatFrame (physicalRefreshCode N impl.program) k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl
      all_goals exact physical_refresh_nat_frame N impl.program _ (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact (hp.nat_frame hframe).trans (hc.nat_frame (CoreRefresh.nat_frame k))
  have hpr (k : ℕ) (hk : k ∈ ([612,614,616] : List ℕ)) : p.realReg k = c.realReg k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl
    all_goals exact hp.real_frame (physical_refresh_real_frame N impl.program _ (by omega) (by decide))
  have hpptr : p.natReg 568 = CoreMemory.field b B e 0 := (hpn 568 (by simp)).trans hladdr.root
  have hpa : p.natReg 626 = (tail b e).val := (hpn 626 (by simp)).trans hlload.tail
  have hpz : p.natReg 628 = (head b e).val :=
    (hp.nat_frame (physical_refresh_nat_frame N impl.program 628 (by omega) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))).trans hcz
  have hpflag : p.natReg 648 = CoreGeometry.returnBit b e := (hpn 648 (by simp)).trans hlload.returnFlag
  have hpaddr : p.natReg 578 = CoreMemory.field b B e 3 := by
    rw [hpn 578 (by simp),hladdr.head]
    dsimp [CoreMemory.field]
  have hpf : p.realReg 612 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e := (hpr 612 (by simp)).trans hcf
  have hpd : p.realReg 614 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e := (hpr 614 (by simp)).trans hcd
  have hpsample : ∀ v : ReturnVertex b, e = .inr v → p.realReg 616 = DecrAlmostLinearSSSP.Decremental.labels b state v.val :=
    fun v hv => (hpr 616 (by simp)).trans (hcsample v hv)
  obtain ⟨cc,t,ht,hcc,htm,hts⟩ := CoreCommit.head_eval b B N K state e xs pctx.current p hpm pctx.image hB hpend
    hpptr hpa hpz hpflag hpaddr hpf hpd hpsample
  let next := pctx.of_image hts
  have hmono1 : ctx.current.work ≤ lctx.current.work := hlmono
  have hmono2 : lctx.current.work ≤ pctx.current.work := hpmono
  have hsum : pctx.current.work-ctx.current.work = (lctx.current.work-ctx.current.work)+
      (pctx.current.work-lctx.current.work) := by omega
  change cl ≤ (dispatchCharge impl.program.code+2)*(lctx.current.work-ctx.current.work)+16*N+46 at hcl
  change cp ≤ (dispatchCharge impl.program.code+2)*(pctx.current.work-lctx.current.work)+24*N+85 at hcp
  have hcost : 19+(cl+(7+(cp+cc))) ≤ (dispatchCharge impl.program.code+2)*(pctx.current.work-ctx.current.work)+40*N+218 := by
    rw [hsum,Nat.mul_add]
    omega
  refine ⟨19+(cl+(7+(cp+cc))),t,next,Eval.seq hr (Eval.seq hl (Eval.seq hc (Eval.seq hp ht))),hcost,
    htm,afterBounds,hpmodel,hpfirst.trans hlfirst,?_,hmono1.trans hmono2,hpR.trans hlR⟩
  change pctx.ops = ctx.ops++_
  rw [hpops]
  change lctx.ops++_ = ctx.ops++_
  rw [hlops]
  simp only [rctx,Context.of_image,List.append_assoc,List.cons_append,List.nil_append]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.refresh_head {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 0 < K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (xs : List (Edge b)) (hpend : state.pending = e::xs)
    (he : s.natReg 560 = CoreMemory.encodedEdge b e) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (refreshCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 ∧
      CoreHost.Image b B K (refresh b state e) t ∧ RuntimeBounds b K (refresh b state e) ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧
      next.ops = ctx.ops++[.queryY (tail b e),.queryY (head b e),.erase (logicalIndexEquiv b e),
        .insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e),
        .paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)] ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  exact ctx.refresh_head_validated host hB hN hBound model e xs hpend
    (runtime_indexed_physical_valid b K state bounds (logicalIndexEquiv b) (logicalCount_le b))
    (bounds.refresh_validity b K hK state e) (bounds.refresh b K hK state e) he
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.drain_one {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 0 < K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (xs : List (Edge b)) (hpend : state.pending = e::xs) (hrunning : state.stopped = false) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (drainOneCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+219 ∧
      CoreHost.Image b B K (refresh b state e) t ∧ RuntimeBounds b K (refresh b state e) ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state (refresh b state e) ∧
      next.first = ctx.first ∧ next.ops.length = ctx.ops.length+5 ∧
      toggleVolume next.ops = toggleVolume ctx.ops ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  let u := CoreHeadSelect.result s
  have hu : Eval CoreHeadSelect.code s 1 u := CoreHeadSelect.eval_code s
  obtain ⟨hum,hus,hue⟩ := CoreHeadSelect.correct b B N K state e xs ctx.current s host ctx.image hB hpend
  let uctx := ctx.of_image hus
  obtain ⟨cost,t,next,he,hcost,htm,htbounds,htmodel,htfirst,htops,htmono,htR⟩ :=
    uctx.refresh_head hum hB hN hBound hK bounds model e xs hpend hue
  have hl : next.ops.length = ctx.ops.length+5 := by
    rw [htops]
    simp only [uctx,Context.of_image,List.length_append,List.length_cons,List.length_nil]
  have hvol : toggleVolume next.ops = toggleVolume ctx.ops := by
    rw [htops]
    simp [toggleVolume,List.filter_append,uctx,Context.of_image]
  exact ⟨1+cost,t,next,Eval.seq hu he,by change cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 at hcost;omega,
    htm,htbounds,htmodel,RuntimeRepairStep.refresh state e xs hrunning hpend,htfirst,hl,hvol,htmono,htR⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.ratio {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hn : state.cachedGradient ≠ 0) (hK0 : 0 < K0) (hKK : K0 ≤ K) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (ratioCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+19 ∧
      CoreHost.Image b B K state t ∧
      CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) next.current) ∧
      RatioGuarantee (cachedPhysical b state) K
        (impl.view b.input.n (logicalCount b) next.current).lastG
        (impl.view b.input.n (logicalCount b) next.current).lastU
        (impl.view b.input.n (logicalCount b) next.current).lastCut ∧
      (impl.view b.input.n (logicalCount b) next.current).hasCut = true ∧
      t.realReg 29 = (impl.view b.input.n (logicalCount b) next.current).lastG ∧
      t.realReg 31 = (impl.view b.input.n (logicalCount b) next.current).lastU ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.ratio] ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hs := CoreRequest.ratio_eval (n := b.input.n) (k := logicalCount b) B (CoreMemory.sourceRecord b B) N impl.program ctx.current s ctx.image hodd
  obtain ⟨cost,t,next,he,hcost,htm,hrep,htrans,hfirst,hops,hcs,hmono⟩ := ctx.advance host hB hN hBound .ratio
    trivial hb CoreRequest.ratioCode 4 (CoreHost.preserves_ratio b B K state hB) hs
  obtain ⟨htmodel,htqual,hthas⟩ := model.ratio b (logicalIndexEquiv b) state _ _ K K0 ξ next.current htrans hn hK0 hKK
  have htn : (impl.view b.input.n (logicalCount b) next.current).physical.gamma ≠ 0 := by
    simpa only [htmodel.physical,indexedPhysical] using hn
  obtain ⟨hq,hhas,hG,hU⟩ := htrans.2.2.2.2 htn
  have hnG : t.realReg 29 = (impl.view b.input.n (logicalCount b) next.current).lastG := by
    have hh : t.realReg 29 = next.current.realReg 10 := by simpa only [shadowReg,Data.machine] using hrep.realReg 10
    exact hh.trans hG.symm
  have hnU : t.realReg 31 = (impl.view b.input.n (logicalCount b) next.current).lastU := by
    have hh : t.realReg 31 = next.current.realReg 11 := by simpa only [shadowReg,Data.machine] using hrep.realReg 11
    exact hh.trans hU.symm
  have hR : reportVolume next.machines = reportVolume ctx.machines := by
    rw [hcs,reportVolume_append ctx.machines ctx.current next.current ctx.last,htrans.2.2.1,Nat.add_zero]
  exact ⟨cost,t,next,he,by omega,htm,htmodel,htqual,hthas,hnG,hnU,hfirst,hops,hmono,hR⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.toggle {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 32 ≤ K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hrunning : state.stopped = false) (hdrained : state.pending = []) (hn : state.cachedGradient ≠ 0)
    (hhas : (impl.view b.input.n (logicalCount b) ctx.current).hasCut = true)
    (hq : RatioGuarantee (cachedPhysical b state) K
      (impl.view b.input.n (logicalCount b) ctx.current).lastG
      (impl.view b.input.n (logicalCount b) ctx.current).lastU
      (impl.view b.input.n (logicalCount b) ctx.current).lastCut)
    (hfailed : (impl.view b.input.n (logicalCount b) ctx.current).lastG/
      (impl.view b.input.n (logicalCount b) ctx.current).lastU < -1/(4*K))
    (hNativeU : s.realReg 31 = (impl.view b.input.n (logicalCount b) ctx.current).lastU) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
    ∃ reports : List (Edge b),
      Eval (toggleCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+27+18*reportCount next.current ∧
      CoreHost.Image b B K (reportedToggle b K state
        (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports) t ∧
      RuntimeBounds b K (reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports) ∧
      CutModel b (logicalIndexEquiv b)
        (reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports)
        (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state
        (reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports) ∧
      next.first = ctx.first ∧ next.ops.length = ctx.ops.length+1 ∧
      toggleVolume next.ops = toggleVolume ctx.ops+1 ∧ ctx.current.work ≤ next.current.work ∧
      reportVolume next.machines = reportVolume ctx.machines+reportCount next.current ∧
      reports.length ≤ reportCount next.current := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  let c := impl.view b.input.n (logicalCount b) ctx.current
  let tau := 1/(K^2*c.lastU)
  have htau : s.realReg 510/s.realReg 31 = tau := by
    rw [host.parameters.threshold,hNativeU]
    dsimp only [tau,c]
    simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv,one_div,mul_inv_rev]
    ring
  have hv := model.toggle_valid b (logicalIndexEquiv b) state _ K hhas hn hq.2.1 (by linarith)
  have hb : (applyPhysical c.physical (.toggle tau)).Valid (2*b.input.size) (4*b.weightExponent+68) := by
    change c.physical.Valid _ _
    rw [model.physical]
    exact runtime_indexed_physical_valid b K state bounds (logicalIndexEquiv b) (logicalCount_le b)
  have hs := CoreRequest.toggle_eval (n := b.input.n) (k := logicalCount b) B (CoreMemory.sourceRecord b B) N
    impl.program ctx.current s tau ctx.image hodd htau
  obtain ⟨cu,u,uctx,hu,hcu,hum,hrep,htrans,hfirst,hops,hcs,hmono⟩ :=
    ctx.advance host hB hN hBound (.toggle tau) hv hb CoreRequest.toggleCode 8
      (CoreHost.preserves_toggle b B K state hB) hs
  have hupending : CorePending.View B ([] : List (Fin (logicalCount b))) u := by
    simpa only [hdrained,List.map_nil] using hum.pending
  obtain ⟨cr,t,ht,hcr,htview,htenv,htr,htguest,htmembership,htmemory⟩ :=
    CoreReports.eval_code B (logicalCount b) uctx.current [] u
      (CoreHost.reports_environment b B K state u hum) hupending hum.captured.zeroN hrep
  let ys := CoreReports.consume (logicalCount b) [] (CoreReports.reportList uctx.current)
  let reports := ys.map (logicalIndexEquiv b).symm
  have hMember : ∀ e, e ∈ reports ↔ Reported uctx.current (logicalIndexEquiv b e) := by
    apply CoreReports.logical_membership b uctx.current ys
    intro d
    simpa only [List.not_mem_nil,false_or] using htmembership d
  have hComplete := model.toggle_complete b (logicalIndexEquiv b) state _ _ K K0 uctx.current reports hdrained htrans hMember
  have htmodel := model.toggle b (logicalIndexEquiv b) state _ _ K K0 uctx.current reports hdrained htrans hMember
  have htm0 := CoreHost.reports_image b B K state ys u t cr hum hB ht htview htr htmemory
  have htm : CoreHost.Image b B K (reportedToggle b K state (modelReply b c) reports) t :=
    htm0.state_congr b B K rfl rfl rfl rfl rfl rfl
  have hts := uctx.image.report_scan B (CoreMemory.sourceRecord b B) N (logicalCount b) uctx.current u t cr
    (by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega) ht htr htmemory
  let next := uctx.of_image hts
  have hBounds := bounds.toggle b K hK state hdrained (modelReply b c) hq hfailed reports hComplete
  have hStep := RuntimeRepairStep.toggle state (modelReply b c) reports hrunning hdrained hq hfailed hComplete
  have hlength : next.ops.length = ctx.ops.length+1 := by change uctx.ops.length = _;rw [hops];simp
  have hvol : toggleVolume next.ops = toggleVolume ctx.ops+1 := by
    change toggleVolume uctx.ops = _
    rw [hops]
    simp [toggleVolume,List.filter_append]
  have hR : reportVolume next.machines = reportVolume ctx.machines+reportCount next.current := by
    change reportVolume uctx.machines = reportVolume ctx.machines+reportCount uctx.current
    rw [hcs,reportVolume_append ctx.machines ctx.current uctx.current ctx.last]
  have hlen : reports.length ≤ reportCount next.current := by
    change (ys.map (logicalIndexEquiv b).symm).length ≤ reportCount uctx.current
    rw [List.length_map]
    exact CoreReports.initial_reports_length (logicalCount b) uctx.current
  exact ⟨cu+cr,t,next,reports,Eval.seq hu ht,by change cu+cr ≤ (dispatchCharge impl.program.code+2)*(uctx.current.work-ctx.current.work)+8*N+27+18*reportCount uctx.current;omega,
    htm,hBounds,htmodel,hStep,hfirst,hlength,hvol,hmono,hR,hlen⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.stop {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hrunning : state.stopped = false) (hdrained : state.pending = [])
    (htest : state.nonzeroEntries = 0 ∨ ∃ r : CutReply b,
      RatioGuarantee (cachedPhysical b state) K r.G r.U r.cut ∧ -1/(4*K) ≤ r.G/r.U) :
    ∃ next : Context b B N m exponent impl K0 ξ h Γ init (stoppedData s),
      CoreHost.Image b B K {state with stopped := true} (stoppedData s) ∧
      RuntimeBounds b K {state with stopped := true} ∧
      CutModel b (logicalIndexEquiv b) {state with stopped := true}
        (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state {state with stopped := true} ∧
      (stoppedData s).natReg 650 = 0 ∧ next.first = ctx.first ∧ next.current = ctx.current ∧ next.ops = ctx.ops ∧ next.machines = ctx.machines := by
  have hsm := ctx.image.nat_register B _ N 650 0 ctx.current s
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
  let next := ctx.of_image hsm
  have hhm := host.temp_nat b B K state s hB 650 0 (by omega)
  have hhfinal : CoreHost.Image b B K {state with stopped := true} (stoppedData s) :=
    hhm.state_congr b B K rfl rfl rfl rfl rfl rfl
  refine ⟨next,hhfinal,bounds.stop b K state,⟨model.physical,model.y,model.baseline⟩,
    RuntimeRepairStep.stop state hrunning hdrained htest,by simp [stoppedData],rfl,rfl,rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.ratio_decision {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 32 ≤ K) (hK0 : 0 < K0) (hKK : K0 ≤ K)
    (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hrunning : state.stopped = false) (hdrained : state.pending = []) (hn : state.cachedGradient ≠ 0)
    (hflag : s.natReg 650 = 1) (hthreshold : s.realReg 520 = -1/(4*K)) :
    ∃ cost t, ∃ after : State b,
    ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (ratioDecisionCode N impl.program) s cost t ∧
      CoreHost.Image b B K after t ∧ RuntimeBounds b K after ∧
      CutModel b (logicalIndexEquiv b) after (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state after ∧ t.natReg 650 = (if after.stopped then 0 else 1) ∧
      t.realReg 520 = -1/(4*K) ∧ next.first = ctx.first ∧ ctx.current.work ≤ next.current.work ∧
      CoreRepair.RatioShape b K state after N (dispatchCharge impl.program.code+2)
        ctx.current.work next.current.work ctx.ops.length next.ops.length
        (reportVolume ctx.machines) (reportVolume next.machines)
        (toggleVolume ctx.ops) (toggleVolume next.ops) cost := by
  have hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid (2*b.input.size) (4*b.weightExponent+68) := by
    rw [model.physical]
    exact runtime_indexed_physical_valid b K state bounds (logicalIndexEquiv b) (logicalCount_le b)
  obtain ⟨cq,q,qctx,hq,hcq,hqm,hqmodel,hqual,hhas,hG,hU,hfirst,hops,hmono,hR⟩ :=
    ctx.ratio host hB hN hBound hb model hn hK0 hKK
  have hqflag : q.natReg 650 = 1 := (hq.nat_frame (ratio_running_frame N impl.program)).trans hflag
  have hqthreshold : q.realReg 520 = -1/(4*K) := (hq.real_frame (ratio_threshold_frame N impl.program)).trans hthreshold
  let p := CoreRatioGuard.result q
  have hp : Eval CoreRatioGuard.code q 1 p := CoreRatioGuard.eval_code q
  have hpm := CoreRatioGuard.host_image b B K state q hqm hB
  have hps := CoreRatioGuard.source_image b B N qctx.current q qctx.image
  let pctx := qctx.of_image hps
  have hpf : p.natReg 650 = 1 := (hp.nat_frame (CoreRatioGuard.nat_frame 650)).trans hqflag
  have hpt : p.realReg 520 = -1/(4*K) := (hp.real_frame (CoreRatioGuard.real_frame 520 (by omega))).trans hqthreshold
  have hpU : p.realReg 31 = (impl.view b.input.n (logicalCount b) pctx.current).lastU :=
    (hp.real_frame (CoreRatioGuard.real_frame 31 (by omega))).trans hU
  have htest := CoreRatioGuard.holds_iff K _ _ q hG hU hqthreshold
  have hqLength : qctx.ops.length = ctx.ops.length+1 := by rw [hops];simp
  have hqT : toggleVolume qctx.ops = toggleVolume ctx.ops := by rw [hops];simp [toggleVolume,List.filter_append]
  by_cases hfail : (Test.realLess 700 520).holds p
  · have hfailed := htest.mp hfail
    obtain ⟨ct,t,next,reports,ht,hct,htm,htbounds,htmodel,htstep,htfirst,htlength,htT,htmono,htR,htlen⟩ :=
      pctx.toggle hpm hB hN hBound hK bounds hqmodel hrunning hdrained hn hhas hqual hfailed hpU
    let after := reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) qctx.current)) reports
    have hafter : after.stopped = false := hrunning
    have hnativeFlag : t.natReg 650 = (if after.stopped then 0 else 1) := by
      rw [ht.nat_frame (toggle_running_frame N impl.program),hpf,hafter]
      rfl
    have hnativeThreshold : t.realReg 520 = -1/(4*K) := (ht.real_frame (toggle_threshold_frame N impl.program)).trans hpt
    have hlength : next.ops.length = ctx.ops.length+2 := by change next.ops.length = qctx.ops.length+1 at htlength;omega
    have hreports : reportVolume next.machines = reportVolume ctx.machines+reportCount next.current := by
      change reportVolume next.machines = reportVolume qctx.machines+reportCount next.current at htR
      rw [hR] at htR
      exact htR
    have htoggle : toggleVolume next.ops = toggleVolume ctx.ops+1 := by
      change toggleVolume next.ops = toggleVolume qctx.ops+1 at htT
      rw [hqT] at htT
      exact htT
    have hqMono : qctx.current.work ≤ next.current.work := htmono
    have hm : ctx.current.work ≤ next.current.work := hmono.trans hqMono
    have hsum : next.current.work-ctx.current.work = (qctx.current.work-ctx.current.work)+
        (next.current.work-qctx.current.work) := by omega
    change ct ≤ (dispatchCharge impl.program.code+2)*(next.current.work-qctx.current.work)+8*N+27+18*reportCount next.current at hct
    have hcost : cq+(1+(ct+1)) ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+16*N+48+18*reportCount next.current := by
      rw [hsum,Nat.mul_add]
      omega
    refine ⟨cq+(1+(ct+1)),t,after,next,Eval.seq hq (Eval.seq hp (Eval.branchYes hfail ht)),
      htm,htbounds,htmodel,htstep,hnativeFlag,hnativeThreshold,htfirst.trans hfirst,hm,?_⟩
    exact Or.inl ⟨modelReply b (impl.view b.input.n (logicalCount b) qctx.current),reports,reportCount next.current,
      rfl,hlength,hreports,htlen,htoggle,hcost⟩
  · have hpassed : -1/(4*K) ≤ (impl.view b.input.n (logicalCount b) pctx.current).lastG/
        (impl.view b.input.n (logicalCount b) pctx.current).lastU := le_of_not_gt (htest.not.mp hfail)
    obtain ⟨next,htm,htbounds,htmodel,htstep,htflag,htfirst,htcurrent,htops,htmachines⟩ :=
      pctx.stop hpm hB bounds hqmodel hrunning hdrained
        (Or.inr ⟨modelReply b (impl.view b.input.n (logicalCount b) pctx.current),hqual,hpassed⟩)
    let after : State b := {state with stopped := true}
    have ht : Eval stopCode p 1 (stoppedData p) := stop_eval p
    have hnativeFlag : (stoppedData p).natReg 650 = (if after.stopped then 0 else 1) := by exact htflag
    have hnativeThreshold : (stoppedData p).realReg 520 = -1/(4*K) := (ht.real_frame stop_threshold_frame).trans hpt
    have hm : ctx.current.work ≤ next.current.work := by rw [htcurrent];exact hmono
    have hlength : next.ops.length = ctx.ops.length+1 := by rw [htops];exact hqLength
    have hreports : reportVolume next.machines = reportVolume ctx.machines := by rw [htmachines];exact hR
    have htoggle : toggleVolume next.ops = toggleVolume ctx.ops := by rw [htops];exact hqT
    have hcost : cq+(1+(1+2)) ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+23 := by
      rw [htcurrent]
      change cq+(1+(1+2)) ≤ (dispatchCharge impl.program.code+2)*(qctx.current.work-ctx.current.work)+8*N+23
      omega
    refine ⟨cq+(1+(1+2)),stoppedData p,after,next,Eval.seq hq (Eval.seq hp (Eval.branchNo hfail ht)),
      htm,htbounds,htmodel,htstep,hnativeFlag,hnativeThreshold,htfirst.trans hfirst,hm,?_⟩
    exact Or.inr ⟨rfl,hlength,hreports,htoggle,hcost⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.repair_body {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 32 ≤ K) (hK0 : 0 < K0) (hKK : K0 ≤ K)
    (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hrunning : state.stopped = false) (hflag : s.natReg 650 = 1) (hthreshold : s.realReg 520 = -1/(4*K))
    (offset : ℕ) (hdebt : CoreRepair.OperationDebt b state ctx.ops.length (reportVolume ctx.machines) offset)
    (hToggle : toggleVolume ctx.ops = state.toggles) :
    ∃ cost t, ∃ after : State b,
    ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (bodyCode N impl.program) s cost t ∧
      CoreHost.Image b B K after t ∧ RuntimeBounds b K after ∧
      CutModel b (logicalIndexEquiv b) after (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state after ∧ t.natReg 650 = (if after.stopped then 0 else 1) ∧
      t.realReg 520 = -1/(4*K) ∧ next.first = ctx.first ∧ ctx.current.work ≤ next.current.work ∧
      CoreRepair.OperationDebt b after next.ops.length (reportVolume next.machines) offset ∧
      toggleVolume next.ops = after.toggles ∧
      cost+2+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
        credit b N impl.program after next.current next.ops next.machines ∧
      (after.stopped = true → ReadoutCertificate b after) ∧ (after.stopped = true → after.pending = []) := by
  have hcounter : s.natReg 550 = state.nonzeroEntries := host.gradient.count.trans bounds.invariant.counter.symm
  cases hpend : state.pending with
  | cons e xs =>
    have htest : (Test.natLess 56 546).holds s := by
      rw [Test.holds,host.captured.zeroN,host.pending.head,hpend,List.map_cons]
      simp only [CorePending.token]
      omega
    obtain ⟨cost,t,next,he,hcost,htm,htbounds,htmodel,htstep,htfirst,htcalls,htT,htmono,htR⟩ :=
      ctx.drain_one host hB hN hBound (by linarith) bounds model e xs hpend hrunning
    have hafterRun : (refresh b state e).stopped = false := hrunning
    have htflag : t.natReg 650 = (if (refresh b state e).stopped then 0 else 1) := by
      rw [he.nat_frame (drain_running_frame N impl.program),hflag,hafterRun]
      rfl
    have htthreshold := (he.real_frame (drain_threshold_frame N impl.program)).trans hthreshold
    have htdebt : CoreRepair.OperationDebt b (refresh b state e) next.ops.length (reportVolume next.machines) offset := by
      rw [htcalls,htR]
      exact CoreRepair.debt_refresh b state e xs _ _ offset hdebt hpend
    have httoggle : toggleVolume next.ops = (refresh b state e).toggles := htT.trans hToggle
    have hbit : CoreRepair.stoppedBit state = 0 := by simp [CoreRepair.stoppedBit,hrunning]
    have hafterBit : CoreRepair.stoppedBit (refresh b state e) = 0 := hbit
    have hcredit : (cost+1)+2+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
        credit b N impl.program (refresh b state e) next.current next.ops next.machines := by
      unfold credit
      rw [hbit,hafterBit,htcalls,htR]
      have hh := CoreRepair.credit_drain N (dispatchCharge impl.program.code+2) ctx.current.work next.current.work
        ctx.ops.length (reportVolume ctx.machines) cost htmono hcost
      omega
    exact ⟨cost+1,t,refresh b state e,next,Eval.branchYes htest he,htm,htbounds,htmodel,htstep,
      htflag,htthreshold,htfirst,htmono,htdebt,httoggle,hcredit,
      fun hst => htstep.completed b K hK bounds.invariant hst,fun hst => htstep.drained b K hst⟩
  | nil =>
    have htest : ¬(Test.natLess 56 546).holds s := by
      simp only [Test.holds,host.captured.zeroN,host.pending.head,hpend,List.map_nil,CorePending.token,lt_self_iff_false,not_false_eq_true]
    by_cases hnonzero : state.nonzeroEntries = 0
    · have hcounterTest : ¬(Test.natLess 56 550).holds s := by
        simp only [Test.holds,host.captured.zeroN,hcounter,hnonzero,lt_self_iff_false,not_false_eq_true]
      obtain ⟨next,htm,htbounds,htmodel,htstep,htflag,htfirst,htcurrent,htops,htmachines⟩ :=
        ctx.stop host hB bounds model hrunning hpend (Or.inl hnonzero)
      let after : State b := {state with stopped := true}
      have he : Eval stopCode s 1 (stoppedData s) := stop_eval s
      have htthreshold := (he.real_frame stop_threshold_frame).trans hthreshold
      have htdebt : CoreRepair.OperationDebt b after next.ops.length (reportVolume next.machines) offset := by
        rw [htops,htmachines]
        exact CoreRepair.debt_stop b state _ _ _ offset hdebt hrunning (by omega)
      have httoggle : toggleVolume next.ops = after.toggles := by rw [htops];exact hToggle
      have hmono : ctx.current.work ≤ next.current.work := by rw [htcurrent]
      have hbit : CoreRepair.stoppedBit state = 0 := by simp [CoreRepair.stoppedBit,hrunning]
      have hafterBit : CoreRepair.stoppedBit after = 1 := by simp [CoreRepair.stoppedBit,after]
      have hcredit : 5+2+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
          credit b N impl.program after next.current next.ops next.machines := by
        unfold credit
        rw [hbit,hafterBit,htcurrent,htops,htmachines]
        exact CoreRepair.credit_zero_stop N _ _ _ _
      exact ⟨5,stoppedData s,after,next,Eval.branchNo htest (Eval.branchNo hcounterTest he),htm,htbounds,htmodel,htstep,
        htflag,htthreshold,htfirst,hmono,htdebt,httoggle,hcredit,
        fun hst => htstep.completed b K hK bounds.invariant hst,fun hst => htstep.drained b K hst⟩
    · have hcounterTest : (Test.natLess 56 550).holds s := by
        rw [Test.holds,host.captured.zeroN,hcounter]
        omega
      have hn := bounds.invariant.gradient_nonzero b K state hnonzero
      obtain ⟨cost,t,after,next,he,htm,htbounds,htmodel,htstep,htflag,htthreshold,htfirst,htmono,htshape⟩ :=
        ctx.ratio_decision host hB hN hBound hK hK0 hKK bounds model hrunning hpend hn hflag hthreshold
      obtain ⟨htdebt,httoggle,hcredit⟩ := CoreRepair.ratio_accounting b K state after N (dispatchCharge impl.program.code+2)
        ctx.current.work next.current.work ctx.ops.length next.ops.length (reportVolume ctx.machines) (reportVolume next.machines)
        (toggleVolume ctx.ops) (toggleVolume next.ops) cost offset htshape htmono hrunning hpend hdebt hToggle
      have hcost : ((cost+1)+2)+2+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
          credit b N impl.program after next.current next.ops next.machines := by
        unfold credit
        omega
      exact ⟨(cost+1)+2,t,after,next,Eval.branchNo htest (Eval.branchYes hcounterTest he),htm,htbounds,htmodel,htstep,
        htflag,htthreshold,htfirst,htmono,htdebt,httoggle,hcost,
        fun hst => htstep.completed b K hK bounds.invariant hst,fun hst => htstep.drained b K hst⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma step {b : Core} {B N offset : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation} {first : Machine} {active : Finset (Fin b.input.k)}
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hK : 32 ≤ K) (hK0 : 0 < K0) (hKK : K0 ≤ K)
    (hSession : CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68) first K0 (K^(-2 : ℤ)) h Γ init) :
    ∀ q s, Repr b B N offset K K0 h Γ init impl first active q s → (Test.natLess 56 650).holds s →
      ∃ q' t cost, Eval (bodyCode N impl.program) s cost t ∧
        Repr b B N offset K K0 h Γ init impl first active q' t ∧ relation b K q' q ∧
        cost+2+credit b N impl.program q ≤ credit b N impl.program q' := by
  intro q s hq htest
  have hrunning : q.state.stopped = false := by
    cases hs : q.state.stopped with
    | false => rfl
    | true =>
      have hzero : s.natReg 650 = 0 := by simpa [hs] using hq.running
      change s.natReg 56 < s.natReg 650 at htest
      rw [hq.host.captured.zeroN,hzero] at htest
      omega
  have hflag : s.natReg 650 = 1 := by simpa [hrunning] using hq.running
  let ctx := hq.context hSession
  obtain ⟨cost,t,after,next,he,htm,htbounds,htmodel,htstep,htflag,htthreshold,htfirst,htmono,htdebt,htToggle,htcredit,htcomplete,htdrained⟩ :=
    ctx.repair_body hq.host hB hN hBound hK hK0 hKK hq.bounds hq.model hrunning hflag hq.threshold offset hq.debt hq.toggleCount
  let q' : Snapshot b := ⟨after,next.current,next.ops,next.machines⟩
  have hfirst : next.first = first := htfirst
  have hactive : after.active = q.state.active := by cases htstep <;> rfl
  have hrepr : Repr b B N offset K K0 h Γ init impl first active q' t := by
    refine ⟨htbounds,htm,htmodel,?_,next.last,next.zeroTail,next.image,htflag,htthreshold,htdebt,htToggle,htcomplete,hactive.trans hq.active_eq,htdrained⟩
    simpa only [hfirst] using next.run
  have hrel : relation b K q' q := htstep.decreases b K (by linarith) hq.bounds.invariant
  exact ⟨q',t,cost,he,hrepr,hrel,htcredit⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Repr.stopped {b : Core} {B N offset : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation} {first : Machine} {active : Finset (Fin b.input.k)}
    {q : Snapshot b} {s : Data} (hq : Repr b B N offset K K0 h Γ init impl first active q s)
    (ht : ¬(Test.natLess 56 650).holds s) : q.state.stopped = true := by
  cases hs : q.state.stopped with
  | false =>
    have hflag : s.natReg 650 = 1 := by simpa [hs] using hq.running
    exact False.elim (ht (by simpa only [Test.holds,hq.host.captured.zeroN,hflag] using (by decide : (0:ℕ) < 1)))
  | true => rfl
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma loop_eval {b : Core} {B N offset : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation} {first : Machine} {active : Finset (Fin b.input.k)}
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hK : 32 ≤ K) (hK0 : 0 < K0) (hKK : K0 ≤ K)
    (hSession : CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68) first K0 (K^(-2 : ℤ)) h Γ init)
    (q : Snapshot b) (s : Data) (hq : Repr b B N offset K K0 h Γ init impl first active q s) :
    ∃ q' t cost, Eval (loopCode N impl.program) s cost t ∧
      Repr b B N offset K K0 h Γ init impl first active q' t ∧ q'.state.stopped = true ∧
      ReadoutCertificate b q'.state ∧ cost+credit b N impl.program q ≤ credit b N impl.program q'+2 := by
  obtain ⟨q',t,cost,he,hr,ht,hcost⟩ := loop_wellFounded_credit (.natLess 56 650) (bodyCode N impl.program)
    (Repr b B N offset K K0 h Γ init impl first active) (relation b K) (relation_wellFounded b K)
    (credit b N impl.program) (step hB hN hBound hK hK0 hKK hSession) q s hq
  have hstop := hr.stopped ht
  exact ⟨q',t,cost,he,hr,hstop,hr.complete hstop,hcost⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut.Repair
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.repair {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 32 ≤ K) (hK0 : 0 < K0) (hKK : K0 ≤ K)
    (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hrunning : state.stopped = false) (offset : ℕ)
    (hdebt : CoreRepair.OperationDebt b state ctx.ops.length (reportVolume ctx.machines) offset)
    (hToggle : toggleVolume ctx.ops = state.toggles) :
    ∃ cost t, ∃ after : State b,
    ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (repairCode N impl.program) s cost t ∧
      CoreHost.Image b B K after t ∧ RuntimeBounds b K after ∧
      CutModel b (logicalIndexEquiv b) after (impl.view b.input.n (logicalCount b) next.current) ∧
      after.stopped = true ∧ ReadoutCertificate b after ∧
      next.first = ctx.first ∧ CoreRepair.OperationDebt b after next.ops.length (reportVolume next.machines) offset ∧
      toggleVolume next.ops = after.toggles ∧ after.active = state.active ∧ after.pending = [] ∧
      cost+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
        credit b N impl.program after next.current next.ops next.machines+7 := by
  let u := CoreRepairControl.result s
  have hu : Eval CoreRepairControl.code s 5 u := CoreRepairControl.eval_code s
  have hum := CoreRepairControl.host_image b B K state s host hB
  have hus := CoreRepairControl.source_image b B N ctx.current s ctx.image
  have huv := CoreRepairControl.values K s host.parameters.quality
  let q : Repair.Snapshot b := ⟨state,ctx.current,ctx.ops,ctx.machines⟩
  have hq : Repair.Repr b B N offset K K0 h Γ init impl ctx.first state.active q u := by
    refine ⟨bounds,hum,model,ctx.run,ctx.last,ctx.zeroTail,hus,?_,huv.2,hdebt,hToggle,?_,rfl,?_⟩
    · simpa only [q,hrunning,Bool.false_eq_true,if_false] using huv.1
    · intro ht
      change state.stopped = true at ht
      rw [hrunning] at ht
      cases ht
    · intro ht
      change state.stopped = true at ht
      rw [hrunning] at ht
      cases ht
  obtain ⟨q',t,cl,he,hr,hstop,hcert,hcredit⟩ := Repair.loop_eval hB hN hBound hK hK0 hKK ctx.session q u hq
  let next := hr.context ctx.session
  refine ⟨5+cl,t,q'.state,next,Eval.seq hu he,hr.host,hr.bounds,hr.model,hstop,hcert,rfl,hr.debt,hr.toggleCount,hr.active_eq,hr.drained hstop,?_⟩
  change cl+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
    credit b N impl.program q'.state q'.current q'.ops q'.machines+2 at hcredit
  change 5+cl+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
    credit b N impl.program q'.state q'.current q'.ops q'.machines+7
  omega
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.forced_deletion {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 0 < K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Fin b.input.k) (hp : state.pending = []) (he : s.natReg 5 = e.val)
    (offset : ℕ) (hdebt : CoreRepair.OperationDebt b state ctx.ops.length (reportVolume ctx.machines) offset)
    (hToggle : toggleVolume ctx.ops = state.toggles) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (forcedDeletionCode N impl.program) s cost t ∧
      CoreHost.Image b B K (deleteState b state e) t ∧ RuntimeBounds b K (deleteState b state e) ∧
      CutModel b (logicalIndexEquiv b) (deleteState b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧ CoreRepair.OperationDebt b (deleteState b state e)
        next.ops.length (reportVolume next.machines) (offset+6) ∧
      toggleVolume next.ops = (deleteState b state e).toggles ∧
      cost+20+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
        credit b N impl.program (deleteState b state e) next.current next.ops next.machines := by
  obtain ⟨cp,p,hpEval,hcp,hpm,hps,hpe⟩ := CoreDeletion.prepare_eval b B N K state e ctx.current s host ctx.image hB hp he
  let pctx := ctx.of_image hps
  have hpmodel := CoreDeletion.pending_model b (logicalIndexEquiv b) state e _ model hp
  obtain ⟨cr,t,next,ht,hcr,htm,htbounds,htmodel,htfirst,htops,htmono,htR⟩ :=
    pctx.refresh_head_validated hpm hB hN hBound hpmodel (.inl e) [] rfl
      (CoreDeletion.before_valid b K state e bounds) (CoreDeletion.refresh_validity b K hK state e bounds hp)
      (CoreDeletion.after_bounds b K hK state e bounds hp) hpe
  have hstate := CoreDeletion.refreshed_eq b state e hp
  rw [hstate] at htm htbounds htmodel
  have hlength : next.ops.length = ctx.ops.length+5 := by rw [htops];simp [pctx,Context.of_image]
  have hT : toggleVolume next.ops = toggleVolume ctx.ops := by rw [htops];simp [toggleVolume,List.filter_append,pctx,Context.of_image]
  have hR : reportVolume next.machines = reportVolume ctx.machines := htR
  have hmono : ctx.current.work ≤ next.current.work := htmono
  have hdebt' : CoreRepair.OperationDebt b (deleteState b state e) next.ops.length (reportVolume next.machines) (offset+6) := by
    rw [hlength,hR]
    exact CoreRepair.debt_deletion b state e _ _ offset hdebt hp
  have htoggle : toggleVolume next.ops = (deleteState b state e).toggles := hT.trans hToggle
  have hcost : cp+cr ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+240 := by
    change cr ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 at hcr
    omega
  have hcredit : cp+cr+20+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
      credit b N impl.program (deleteState b state e) next.current next.ops next.machines := by
    unfold credit
    rw [hlength,hR]
    have hbit : CoreRepair.stoppedBit state ≤ 1 := by unfold CoreRepair.stoppedBit;split <;> omega
    have hnewbit : CoreRepair.stoppedBit (deleteState b state e) = 0 := rfl
    rw [hnewbit]
    exact CoreRepair.credit_deletion N (dispatchCharge impl.program.code+2) ctx.current.work next.current.work
      ctx.ops.length (reportVolume ctx.machines) (CoreRepair.stoppedBit state) (cp+cr) hmono hbit hcost
  exact ⟨cp+cr,t,next,Eval.seq hpEval ht,htm,htbounds,htmodel,htfirst,hdebt',htoggle,hcredit⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.update {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 32 ≤ K) (hK0 : 0 < K0) (hKK : K0 ≤ K)
    (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Fin b.input.k) (hp : state.pending = []) (he : s.natReg 5 = e.val)
    (offset : ℕ) (hdebt : CoreRepair.OperationDebt b state ctx.ops.length (reportVolume ctx.machines) offset)
    (hToggle : toggleVolume ctx.ops = state.toggles) :
    ∃ cost t, ∃ after : State b,
    ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (updateCode N impl.program) s cost t ∧
      CoreHost.Image b B K after t ∧ RuntimeBounds b K after ∧
      CutModel b (logicalIndexEquiv b) after (impl.view b.input.n (logicalCount b) next.current) ∧
      after.stopped = true ∧ ReadoutCertificate b after ∧ after.pending = [] ∧ after.active = state.active.erase e ∧
      next.first = ctx.first ∧ CoreRepair.OperationDebt b after next.ops.length (reportVolume next.machines) (offset+6) ∧
      toggleVolume next.ops = after.toggles ∧
      cost+7+credit b N impl.program state ctx.current ctx.ops ctx.machines ≤
        credit b N impl.program after next.current next.ops next.machines := by
  obtain ⟨cp,p,pctx,hpEval,hpm,hpbounds,hpmodel,hpfirst,hpdebt,hpToggle,hpcost⟩ :=
    ctx.forced_deletion host hB hN hBound (by linarith) bounds model e hp he offset hdebt hToggle
  obtain ⟨cr,t,after,next,ht,htm,htbounds,htmodel,htstop,htcert,htfirst,htdebt,htToggle,htactive,htpending,htcost⟩ :=
    pctx.repair hpm hB hN hBound hK hK0 hKK hpbounds hpmodel rfl (offset+6) hpdebt hpToggle
  refine ⟨cp+cr,t,after,next,Eval.seq hpEval ht,htm,htbounds,htmodel,htstop,htcert,htpending,htactive,
    htfirst.trans hpfirst,htdebt,htToggle,?_⟩
  omega
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore
open DecrAlmostLinearSSSP.Decremental
open Structured
lemma core_cut_start (b : Core) (K K0 h Γ init : ℝ) (hK : 0 < K)
    (impl : CutImplementation)
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init (K^(-2 : ℤ))) :
    ∃ first,
      Ends impl.program (cutInitial impl.program
        (indexedPhysical b (initializeState b) (logicalIndexEquiv b)) (2*b.input.size)
        (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))) first ∧
      CutModel b (logicalIndexEquiv b) (initializeState b)
        (impl.view b.input.n (logicalCount b) first) ∧
      (impl.view b.input.n (logicalCount b) first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧
      CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68)
        first K0 (K^(-2 : ℤ)) h Γ init := by
  have hs := RuntimeBounds.initial b K hK
  have hv := runtime_indexed_physical_valid b K (initializeState b) hs
    (logicalIndexEquiv b) (logicalCount_le b)
  have hcap : 0 < (kappa b)^(-2 : ℤ) := zpow_pos (core_kappa_bounds b).1 _
  obtain ⟨first,he,hp,hy,hb,hh,hw,hr⟩ := himpl.initialize_session
    (indexedPhysical b (initializeState b) (logicalIndexEquiv b)) ((kappa b)^(-2 : ℤ))
    hv hcap (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (core_capacityBound_range b).2) (by
      intro e he
      change (initializeState b).cache ((logicalIndexEquiv b).symm e) ≤ _
      have hf0 : ∀ d, 0 ≤ (initializeState b).cache d := fun d => (by norm_num : (0:ℝ) ≤ 1).trans (hs.lower d)
      exact (Finset.single_le_sum (fun d _ => hf0 d) (Finset.mem_univ _)).trans
        ((cache_total_upper b K _ hs.invariant.cache).trans (core_cache_total_capacityBound b)))
  exact ⟨first,he,CutModel.initial b (logicalIndexEquiv b) _ hp hy hb,hh,hw,hr⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreInitialize
open DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
lemma boot_cut_eval (b : Core) (N : ℕ) (p : Program) (impl : CutImplementation)
    (K0 h Γ init : ℝ)
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality N (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality N (2*b.input.size)
    let registers := sourceRegisters impl.program
    ∃ cost t first, Eval (bootCutCode N impl.program) (data (initialMachine p b.input)) cost t ∧
      (cost : ℝ) ≤ ((80000*(N+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init ∧
      CoreHost.Image b B K (initializeState b) t ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) registers first t ∧
      CutModel b (logicalIndexEquiv b) (initializeState b) (impl.view b.input.n (logicalCount b) first) ∧
      (impl.view b.input.n (logicalCount b) first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧
      Ends impl.program (cutInitial impl.program (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
        (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))) first ∧
      CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68)
        first K0 (K^(-2 : ℤ)) h Γ init := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality N (2*b.input.size)
  let registers := sourceRegisters impl.program
  have hreg : 10 ≤ registers := by dsimp [registers,sourceRegisters];omega
  have hbound : registerBound impl.program.code ≤ registers := by dsimp [registers,sourceRegisters];omega
  have hK : 0 < K := by exact pow_pos (by norm_num) _
  obtain ⟨first,hfirst,hmodel,hhas,hwork,hsession⟩ := core_cut_start b K K0 h Γ init hK impl himpl
  obtain ⟨cu,u,hu,hcu,hum,hus⟩ := boot_cut_input_eval b N registers p impl.program hreg
  let g := cutInitial impl.program (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
    (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  obtain ⟨cc,t,ht,hcc,hts,htrep,htframe⟩ := hus.call B (CoreMemory.sourceRecord b B) registers impl.program.initPC
    impl.program g first u hbound hodd rfl rfl rfl
    (cutInitial_zero_tail impl.program _ _ _ _ (by omega)) hfirst
  have htm := CoreHost.source_frame b B registers impl.program.initPC K (initializeState b) impl.program
    u t cc hum (by dsimp [B];omega) ht htframe
  refine ⟨cu+cc,t,first,Eval.seq hu ht,?_,htm,hts,hmodel,hhas,hwork,hfirst,hsession⟩
  have hcc' : cc ≤ (dispatchCharge impl.program.code+2)*first.work+8*registers+15 := by
    simpa only [g,cutInitial,Nat.sub_zero] using hcc
  have hsum : cu+cc ≤ (80000*(N+1)+265)*b.input.size+
      4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120+
      (dispatchCharge impl.program.code+2)*first.work := by omega
  have hr : (cu+cc : ℝ) ≤ ((80000*(N+1)+265)*b.input.size+
      4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
      (dispatchCharge impl.program.code+2)*first.work := by exact_mod_cast hsum
  have hmul : ((dispatchCharge impl.program.code : ℝ)+2)*first.work ≤
      ((dispatchCharge impl.program.code : ℝ)+2)*init := mul_le_mul_of_nonneg_left hwork (by positivity)
  dsimp only [registers] at hr
  push_cast at hr ⊢
  linarith only [hr,hmul]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreInitialize
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreInitialize
open DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
lemma boot_context_eval (b : Core) (N : ℕ) (p : Program) (impl : CutImplementation)
    (K0 h Γ init : ℝ)
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality N (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality N (2*b.input.size)
    let registers := sourceRegisters impl.program
    ∃ cost t, ∃ ctx : CoreNativeCut.Context b B registers (2*b.input.size) (4*b.weightExponent+68)
        impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (bootCutCode N impl.program) (data (initialMachine p b.input)) cost t ∧
      (cost : ℝ) ≤ ((80000*(N+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init ∧
      CoreHost.Image b B K (initializeState b) t ∧
      CutModel b (logicalIndexEquiv b) (initializeState b) (impl.view b.input.n (logicalCount b) ctx.current) ∧
      (impl.view b.input.n (logicalCount b) ctx.current).hasCut = false ∧
      ctx.ops = [] ∧ ctx.machines = [ctx.current] ∧ ctx.first = ctx.current := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality N (2*b.input.size)
  let registers := sourceRegisters impl.program
  obtain ⟨cost,t,first,he,hcost,htm,hts,hmodel,hhas,hwork,hEnd,hsession⟩ := boot_cut_eval b N p impl K0 h Γ init himpl
  have hbound : registerBound impl.program.code ≤ registers := by dsimp [registers,sourceRegisters];omega
  have hzero : ZeroRegisterTail registers first :=
    (cutInitial_zero_tail impl.program (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
      (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ)) (by dsimp [registers,sourceRegisters];omega)).ends_of_bound hbound hEnd
  let ctx : CoreNativeCut.Context b B registers (2*b.input.size) (4*b.weightExponent+68)
      impl K0 (K^(-2 : ℤ)) h Γ init t :=
    ⟨first,first,[],[first],hsession,CutRun.start,by rfl,hzero,hts⟩
  exact ⟨cost,t,ctx,he,hcost,htm,hmodel,hhas,rfl,rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreInitialize
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma initialize_eval (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (p : Program) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0)
    (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality qualityPower (2*b.input.size)
    let registers := CoreInitialize.sourceRegisters impl.program
    ∃ cost t, ∃ after : State b,
    ∃ next : Context b B registers (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (initCode qualityPower impl.program) (data (initialMachine p b.input)) cost t ∧
      CoreHost.Image b B K after t ∧ RuntimeBounds b K after ∧
      CutModel b (logicalIndexEquiv b) after (impl.view b.input.n (logicalCount b) next.current) ∧
      after.stopped = true ∧ ReadoutCertificate b after ∧ after.active = Finset.univ ∧ after.pending = [] ∧
      CoreRepair.OperationDebt b after next.ops.length (reportVolume next.machines) 0 ∧
      toggleVolume next.ops = after.toggles ∧
      (cost : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init+
        (credit b registers impl.program after next.current next.ops next.machines : ℕ)+7 := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality qualityPower (2*b.input.size)
  let registers := CoreInitialize.sourceRegisters impl.program
  have hK : 32 ≤ K := computableCutQuality_ge_32 qualityPower (2*b.input.size) hpower
  have hB : b.input.n ≤ B := by dsimp [B];omega
  have hN : 10 ≤ registers := by dsimp [registers,CoreInitialize.sourceRegisters];omega
  have hBound : registerBound impl.program.code ≤ registers := by dsimp [registers,CoreInitialize.sourceRegisters];omega
  obtain ⟨cu,u,ctx,hu,hcu,hum,humodel,huhas,huops,humachines,hufirst⟩ :=
    CoreInitialize.boot_context_eval b qualityPower p impl K0 h Γ init himpl
  have hdebt : CoreRepair.OperationDebt b (initializeState b) ctx.ops.length (reportVolume ctx.machines) 0 := by
    simp [CoreRepair.OperationDebt,CoreRepair.stoppedBit,initializeState,huops,humachines,reportVolume]
  have hToggle : toggleVolume ctx.ops = (initializeState b).toggles := by rw [huops];simp [toggleVolume,initializeState]
  obtain ⟨cr,t,after,next,ht,htm,htbounds,htmodel,htstop,htcert,htfirst,htdebt,htToggle,htactive,htpending,htcost⟩ :=
    ctx.repair hum hB hN hBound hK hK0 hKK (RuntimeBounds.initial b K (by linarith)) humodel rfl 0 hdebt hToggle
  have hactive : after.active = Finset.univ := htactive
  change cr+credit b registers impl.program (initializeState b) ctx.current ctx.ops ctx.machines ≤
    credit b registers impl.program after next.current next.ops next.machines+7 at htcost
  have hcr : cr ≤ credit b registers impl.program after next.current next.ops next.machines+7 := by omega
  have hcrReal : (cr : ℝ) ≤ (credit b registers impl.program after next.current next.ops next.machines : ℕ)+7 := by exact_mod_cast hcr
  refine ⟨cu+cr,t,after,next,Eval.seq hu ht,htm,htbounds,htmodel,htstop,htcert,hactive,htpending,htdebt,htToggle,?_⟩
  dsimp only [registers] at hcrReal
  push_cast at hcu hcrReal ⊢
  linarith only [hcu,hcrReal]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma program_initialization (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0)
    (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality qualityPower (2*b.input.size)
    let registers := CoreInitialize.sourceRegisters impl.program
    ∃ cost c, Ends (coreProgram qualityPower impl.program)
      (initialMachine (coreProgram qualityPower impl.program) b.input) c ∧ c.work = cost+1 ∧
    ∃ ready : Ready b B registers K K0 h Γ init impl [] (data c),
      (c.work : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init+(ready.credit : ℝ)+8 := by
  dsimp only
  let p := coreProgram qualityPower impl.program
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality qualityPower (2*b.input.size)
  let registers := CoreInitialize.sourceRegisters impl.program
  obtain ⟨cost,t,after,ctx,he,htm,htbounds,htmodel,htstop,htcert,htactive,htpending,htdebt,htToggle,hcost⟩ :=
    initialize_eval b qualityPower hpower p impl K0 h Γ init hK0 hKK himpl
  obtain ⟨c,hend,hdata,hwork⟩ := command_ends he p 0 (initialMachine p b.input)
    (program_init _ _) rfl rfl rfl rfl (by simpa only [p,coreProgram,Nat.zero_add] using program_init_halt (initCode qualityPower impl.program) (updateCode registers impl.program))
  subst t
  have hcwork : c.work = cost+1 := by simpa only [initialMachine,Nat.zero_add] using hwork
  let ready : Ready b B registers K K0 h Γ init impl [] (data c) :=
    ⟨after,ctx,htm,htbounds,htmodel,htstop,htcert,htpending,by simpa [live] using htactive,htdebt,htToggle⟩
  refine ⟨cost,c,hend,hcwork,ready,?_⟩
  rw [hcwork]
  change ((cost+1 : ℕ) : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
    4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
    (dispatchCharge impl.program.code+2)*init+(credit b registers impl.program after ctx.current ctx.ops ctx.machines : ℝ)+8
  change (cost : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
    4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
    (dispatchCharge impl.program.code+2)*init+(credit b registers impl.program after ctx.current ctx.ops ctx.machines : ℝ)+7 at hcost
  push_cast at hcost ⊢
  linarith only [hcost]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Ready.external_credit {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {deleted : List (Fin b.input.k)} {s : Data} (r : Ready b B N K K0 h Γ init impl deleted s)
    (hB : b.input.n ≤ B) (value : ℕ) : (r.external hB value).credit = r.credit := rfl
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma program_update (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0) (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (deleted : List (Fin b.input.k)) (c : Machine)
    (ready : Ready b (b.input.n+3*b.input.k+2) (CoreInitialize.sourceRegisters impl.program)
      (computableCutQuality qualityPower (2*b.input.size)) K0 h Γ init impl deleted (data c)) (e : Fin b.input.k) :
    ∃ cost d, Ends (coreProgram qualityPower impl.program) (deletionMachine (coreProgram qualityPower impl.program) c e.val) d ∧
      d.work = c.work+cost+1 ∧
    ∃ next : Ready b (b.input.n+3*b.input.k+2) (CoreInitialize.sourceRegisters impl.program)
      (computableCutQuality qualityPower (2*b.input.size)) K0 h Γ init impl (deleted++[e]) (data d),
      d.work+6+ready.credit ≤ c.work+next.credit := by
  let p := coreProgram qualityPower impl.program
  let B := b.input.n+3*b.input.k+2
  let N := CoreInitialize.sourceRegisters impl.program
  let K := computableCutQuality qualityPower (2*b.input.size)
  let start := deletionMachine p c e.val
  have hB : b.input.n ≤ B := by dsimp [B];omega
  have hN : 10 ≤ N := by dsimp [N,CoreInitialize.sourceRegisters];omega
  have hBound : registerBound impl.program.code ≤ N := by dsimp [N,CoreInitialize.sourceRegisters];omega
  have hK : 32 ≤ K := computableCutQuality_ge_32 qualityPower (2*b.input.size) hpower
  let hs : Ready b B N K K0 h Γ init impl deleted (data start) := by
    change Ready b B N K K0 h Γ init impl deleted {data c with natReg := Function.update (data c).natReg 5 e.val}
    exact ready.external hB e.val
  obtain ⟨cost,t,after,ctx,he,htm,htbounds,htmodel,htstop,htcert,htpending,htactive,htfirst,htdebt,htToggle,htcost⟩ :=
    hs.context.update hs.host hB hN hBound hK hK0 hKK hs.bounds hs.model e hs.pending rfl (6*deleted.length) hs.debt hs.toggles
  obtain ⟨d,hend,hdata,hwork⟩ := command_ends he p p.update start (Structured.program_update _ _) rfl rfl rfl rfl
    (program_update_halt _ _)
  subst t
  have hdwork : d.work = c.work+cost+1 := hwork
  have hactive : after.active = live (deleted++[e]) := by rw [htactive,hs.active,live_append_singleton]
  have hdebt : CoreRepair.OperationDebt b after ctx.ops.length (reportVolume ctx.machines) (6*(deleted++[e]).length) := by
    simpa [List.length_append,Nat.mul_add] using htdebt
  let next : Ready b B N K K0 h Γ init impl (deleted++[e]) (data d) :=
    ⟨after,ctx,htm,htbounds,htmodel,htstop,htcert,htpending,hactive,hdebt,htToggle⟩
  have hbudget : cost+7+ready.credit ≤ next.credit := htcost
  exact ⟨cost,d,hend,hdwork,next,by omega⟩
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma online (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0) (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) (ds : List (Fin b.input.k)) :
    ∃ (cs : List Machine) (last : Machine), OnlineRun (coreProgram qualityPower impl.program) b.input ds cs ∧
      cs.length = ds.length+1 ∧ cs.getLast? = some last ∧ Completed b qualityPower impl K0 h Γ init ds last ∧
      ∀ j c, cs[j]? = some c → Completed b qualityPower impl K0 h Γ init (ds.take j) c := by
  classical
  induction ds using List.reverseRecOn with
  | nil =>
    obtain ⟨cost,c,he,hw,ready,hwork⟩ := program_initialization b qualityPower hpower impl K0 h Γ init hK0 hKK himpl
    have hcompleted : Completed b qualityPower impl K0 h Γ init [] c := by
      refine ⟨ready,?_⟩
      simpa only [initialBudget,List.length_nil,Nat.mul_zero,Nat.add_zero,add_assoc,add_comm,add_left_comm] using hwork
    refine ⟨[c],c,OnlineRun.init he,rfl,rfl,hcompleted,?_⟩
    intro j d hd
    cases j with
    | zero =>
      have hdc : c = d := Option.some.inj hd
      subst d
      exact hcompleted
    | succ j => simp at hd
  | append_singleton ds e ih =>
    obtain ⟨cs,c,hr,hlen,hlast,hcompleted,hprefix⟩ := ih
    obtain ⟨ready,hwork⟩ := hcompleted
    obtain ⟨cost,d,he,hdwork,next,hcharge⟩ := program_update b qualityPower hpower impl K0 h Γ init hK0 hKK ds c ready e
    have hdCompleted : Completed b qualityPower impl K0 h Γ init (ds++[e]) d := by
      refine ⟨next,?_⟩
      have hchargeR : (d.work : ℝ)+6+(ready.credit : ℝ) ≤ (c.work : ℝ)+(next.credit : ℝ) := by exact_mod_cast hcharge
      push_cast at hwork ⊢
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
      linarith only [hwork,hchargeR]
    refine ⟨cs++[d],d,OnlineRun.next hr hlast e he,?_,by simp,hdCompleted,?_⟩
    · simp only [List.length_append,List.length_singleton,hlen]
    · intro j z hz
      by_cases hj : j < cs.length
      · have hget : cs[j]? = some z := by rwa [List.getElem?_append_left hj] at hz
        have hjds : j ≤ ds.length := by omega
        have htake : (ds++[e]).take j = ds.take j := by
          rw [List.take_append]
          simp only [Nat.sub_eq_zero_of_le hjds,List.take_zero,List.append_nil]
        rw [htake]
        exact hprefix j z hget
      · have hjlen : j < (cs++[d]).length := by
          by_contra hn
          have hnone : (cs++[d])[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
          rw [hnone] at hz
          contradiction
        have hjeq : j = cs.length := by simp only [List.length_append,List.length_singleton] at hjlen;omega
        subst j
        rw [List.getElem?_append_right le_rfl,Nat.sub_self] at hz
        have hdz : d = z := Option.some.inj hz
        subst z
        have htake : (ds++[e]).take cs.length = ds++[e] := by
          apply List.take_of_length_le
          simp only [List.length_append,List.length_singleton,hlen]
          exact le_rfl
        rw [htake]
        exact hdCompleted
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Completed.correct {b : Core} {qualityPower : ℕ} {impl : CutImplementation}
    {K0 h Γ init : ℝ} {deleted : List (Fin b.input.k)} {c : Machine}
    (hc : Completed b qualityPower impl K0 h Γ init deleted c) :
    stored c b.input.source.val = 0 ∧
      (∀ v : Fin b.input.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
      ∀ v : Fin b.input.n, b.input.dist deleted v ≤ stored c v.val ∧
        stored c v.val ≤ ENNReal.ofReal (1+b.input.accuracy)*b.input.dist deleted v ∧
        (stored c v.val = ⊤ ↔ ¬Reachable b.input.graph (live deleted) b.input.source v) := by
  obtain ⟨ready,_⟩ := hc
  have hcorrect := ready.host.certified b _ _ ready.state (Structured.data c) ready.certificate
  rw [ready.active] at hcorrect
  exact hcorrect
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.credit_bound {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {s : Structured.Data} (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (state : State b) (offset : ℕ) (T : ℝ) (hh : 0 ≤ h) (hΓ : 0 ≤ Γ)
    (hT : (state.toggles : ℝ) ≤ T)
    (hdebt : CoreRepair.OperationDebt b state ctx.ops.length (reportVolume ctx.machines) offset)
    (hToggle : toggleVolume ctx.ops = state.toggles) :
    (credit b N impl.program state ctx.current ctx.ops ctx.machines : ℝ) ≤
      (dispatchCharge impl.program.code+2 : ℕ)*init+
      ((dispatchCharge impl.program.code+2 : ℕ)*h+100*(N+1 : ℕ))*
        (5*(Γ*K^2*T)+2*T+offset+1)+
      ((dispatchCharge impl.program.code+2 : ℕ)*h+20)*(Γ*K^2*T)+10 := by
  let D : ℝ := (dispatchCharge impl.program.code+2 : ℕ)
  let C : ℝ := 100*((N+1 : ℕ) : ℝ)
  let R : ℝ := (reportVolume ctx.machines : ℕ)
  let L : ℝ := (ctx.ops.length : ℕ)
  let W : ℝ := (ctx.current.work : ℕ)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hR : R ≤ Γ*K^2*T := by
    have hr := ctx.report_bound
    rw [hToggle] at hr
    have hr' : R ≤ Γ*(state.toggles : ℝ)*K^2 := by
      simpa only [R,div_eq_mul_inv,zpow_neg,zpow_ofNat,inv_inv] using hr
    calc
      R ≤ Γ*(state.toggles : ℝ)*K^2 := hr'
      _ = (Γ*K^2)*(state.toggles : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (mul_nonneg hΓ (sq_nonneg K))
  have hLNat : ctx.ops.length ≤ 5*reportVolume ctx.machines+2*state.toggles+offset+1 := by
    have hb := CoreRepair.stoppedBit_le_one state
    unfold CoreRepair.OperationDebt at hdebt
    omega
  have hLRaw : L ≤ 5*R+2*(state.toggles : ℝ)+offset+1 := by
    change (ctx.ops.length : ℝ) ≤ 5*(reportVolume ctx.machines : ℝ)+2*(state.toggles : ℝ)+(offset : ℝ)+1
    exact_mod_cast hLNat
  have hL : L ≤ 5*(Γ*K^2*T)+2*T+offset+1 := by linarith only [hLRaw,hR,hT]
  have hW : W ≤ init+h*(L+R) := by
    have hw := ctx.work_bound
    push_cast at hw
    change W+6*L ≤ init+h*(L+R) at hw
    linarith only [hw,hL0]
  have hbit : (CoreRepair.stoppedBit state : ℝ) ≤ 1 := by exact_mod_cast CoreRepair.stoppedBit_le_one state
  have hCredit : (credit b N impl.program state ctx.current ctx.ops ctx.machines : ℝ) =
      D*W+C*L+20*R+10*(CoreRepair.stoppedBit state : ℝ) := by
    simp [credit,CoreRepair.nativeCredit,D,C,W,L,R]
  rw [hCredit]
  change D*W+C*L+20*R+10*(CoreRepair.stoppedBit state : ℝ) ≤
    D*init+(D*h+C)*(5*(Γ*K^2*T)+2*T+offset+1)+(D*h+20)*(Γ*K^2*T)+10
  calc
    _ ≤ D*(init+h*(L+R))+C*L+20*R+10 := by
      have hw := mul_le_mul_of_nonneg_left hW hD
      have hb := mul_le_mul_of_nonneg_left hbit (by norm_num : (0:ℝ) ≤ 10)
      linarith only [hw,hb]
    _ = D*init+(D*h+C)*L+(D*h+20)*R+10 := by ring
    _ ≤ _ := by
      have hl := mul_le_mul_of_nonneg_left hL (add_nonneg (mul_nonneg hD hh) hC)
      have hr := mul_le_mul_of_nonneg_left hR (add_nonneg (mul_nonneg hD hh) (by norm_num : (0:ℝ) ≤ 20))
      linarith only [hl,hr]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Completed.work_bound {b : Core} {qualityPower : ℕ} (hpower : 5 ≤ qualityPower)
    {impl : CutImplementation} (K0 C : ℝ) (h Γ a : ℕ → ℝ) (hC : 0 ≤ C)
    (hh : 0 ≤ h (2*b.input.size)) (hΓ : 0 ≤ Γ (2*b.input.size)) (ha : 0 ≤ a (2*b.input.size))
    {ds : List (Fin b.input.k)} {c : Machine} (hlegal : Legal ds)
    (hc : Completed b qualityPower impl K0 (h (2*b.input.size)) (Γ (2*b.input.size))
      (C*(2*b.input.size)*a (2*b.input.size)) ds c) :
    ((c.work+6*ds.length : ℕ) : ℝ) ≤ coreConstant b.weightExponent qualityPower impl.program C*
      b.input.size*coreRuntimeOverhead h Γ a qualityPower b.input.size/b.input.accuracy := by
  obtain ⟨ready,hwork⟩ := hc
  let m : ℝ := b.input.size
  let M := m/b.input.accuracy
  let O := coreRuntimeOverhead h Γ a qualityPower b.input.size
  let K := computableCutQuality qualityPower (2*b.input.size)
  let L := coreLogOverhead b.input.size
  let N := CoreInitialize.sourceRegisters impl.program
  let D : ℝ := (dispatchCharge impl.program.code+2 : ℕ)
  let d : ℝ := (b.weightExponent+8 : ℕ)
  let T := 1040*d*K^3*L^2*M
  obtain ⟨hM,hmM,hL,hO,haO,hFO,hLM⟩ := scale_bounds b qualityPower h Γ a hh hΓ ha
  change 1 ≤ M at hM
  change m ≤ M at hmM
  change 1 ≤ L at hL
  change 1 ≤ O at hO
  change a (2*b.input.size) ≤ O at haO
  change (1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5*L^2 ≤ O at hFO
  change L/b.input.accuracy ≤ O*M at hLM
  have hD : 0 ≤ D := by positivity
  have hd : 1 ≤ d := by dsimp [d];exact_mod_cast (show 1 ≤ b.weightExponent+8 by omega)
  have hK32 : 32 ≤ K := computableCutQuality_ge_32 qualityPower (2*b.input.size) hpower
  have hK : 1 ≤ K := by linarith
  have ht : (ready.state.toggles : ℝ) ≤ T := by
    have ht := ready.bounds.invariant.toggle_count_near_linear b K (by linarith) ready.state
    convert ht using 1 <;> dsimp [T,d,M,m,L] <;> ring
  have hlen : ds.length ≤ b.input.size := by
    have hk := List.Nodup.length_le_card hlegal
    simp only [Fintype.card_fin] at hk
    exact hk.trans b.valid.2.1
  have hoff : (6*ds.length : ℕ) ≤ (6:ℝ)*M := by
    have hn : (ds.length : ℝ) ≤ m := by dsimp [m];exact_mod_cast hlen
    push_cast
    linarith only [hn,hmM]
  have hcBound := ready.context.credit_bound ready.state (6*ds.length) T hh hΓ ht ready.debt ready.toggles
  change (ready.credit : ℝ) ≤ D*(C*(2*b.input.size)*a (2*b.input.size))+
    (D*h (2*b.input.size)+100*(N+1 : ℕ))*(5*(Γ (2*b.input.size)*K^2*T)+2*T+(6*ds.length : ℕ)+1)+
    (D*h (2*b.input.size)+20)*(Γ (2*b.input.size)*K^2*T)+10 at hcBound
  have harith := dynamic_budget_arithmetic D (100*((N+1 : ℕ) : ℝ)) d
    (h (2*b.input.size)) (Γ (2*b.input.size)) K L M hD (by exact_mod_cast (show 20 ≤ 100*(N+1) by omega)) hd hh hΓ hK hL hM
    ((6*ds.length : ℕ) : ℝ) (Nat.cast_nonneg _) hoff
  change _ ≤ 10000*d*(D+100*((N+1 : ℕ) : ℝ))*(1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5*L^2*M+10 at harith
  have hdyn : (ready.credit : ℝ) ≤ D*(C*(2*b.input.size)*a (2*b.input.size))+
      10000*d*(D+100*((N+1 : ℕ) : ℝ))*O*M+10 := by
    have hp := mul_le_mul_of_nonneg_left hFO (show 0 ≤ 10000*d*(D+100*((N+1 : ℕ) : ℝ)) by positivity)
    have hpM := mul_le_mul_of_nonneg_right hp (show 0 ≤ M by linarith)
    nlinarith only [hcBound,harith,hpM]
  have hA : (⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊ : ℝ) ≤ 65*L/b.input.accuracy := core_A_near_linear b
  have hAO : (⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊ : ℝ) ≤ 65*(O*M) := by
    calc
      _ ≤ 65*L/b.input.accuracy := hA
      _ = 65*(L/b.input.accuracy) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLM (by norm_num)
  have hOM : 1 ≤ O*M := by nlinarith only [hO,hM,mul_nonneg (sub_nonneg.mpr hO) (sub_nonneg.mpr hM)]
  have hmOM : m ≤ O*M := by
    have hp := mul_le_mul_of_nonneg_right hO (show 0 ≤ M by linarith)
    nlinarith only [hmM,hp]
  have hi : 2*D*(C*(2*b.input.size)*a (2*b.input.size)) ≤ 4*D*C*(O*M) := by
    have hma := mul_le_mul hmM haO ha (show 0 ≤ M by linarith)
    have hp := mul_le_mul_of_nonneg_left hma (show 0 ≤ 4*D*C by positivity)
    dsimp [m] at hp
    push_cast at hp ⊢
    nlinarith only [hp]
  have hboot : (initialBudget b qualityPower impl.program (C*(2*b.input.size)*a (2*b.input.size)))+10 ≤
      (80000*(qualityPower+1)+265+14*N+400 : ℕ)*(O*M)+D*(C*(2*b.input.size)*a (2*b.input.size)) := by
    unfold initialBudget
    have hDval : (dispatchCharge impl.program.code : ℝ)+2 = D := by simp [D]
    rw [hDval]
    change ((80000*(qualityPower+1)+265)*b.input.size+4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*N+120 : ℕ)+
      D*(C*(2*b.input.size)*a (2*b.input.size))+8+10 ≤ _
    push_cast
    have hp := mul_le_mul_of_nonneg_left hmOM (show 0 ≤ ((80000*(qualityPower+1)+265 : ℕ) : ℝ) by positivity)
    have hn := mul_le_mul_of_nonneg_left hOM (show (0:ℝ) ≤ 14*(N:ℝ)+140 by exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num))
    push_cast at hp
    dsimp [m] at hp
    nlinarith only [hAO,hp,hn,hOM]
  have hsum := add_le_add hwork (show (10:ℝ) ≤ 10 by rfl)
  dsimp [coreConstant]
  change _ ≤ (((80000*(qualityPower+1)+265+14*N+400 : ℕ) : ℝ)+4*D*C+
    10000*d*(D+100*((N+1 : ℕ) : ℝ)))*m*O/b.input.accuracy
  have hid : (((80000*(qualityPower+1)+265+14*N+400 : ℕ) : ℝ)+4*D*C+
    10000*d*(D+100*((N+1 : ℕ) : ℝ)))*m*O/b.input.accuracy =
    (((80000*(qualityPower+1)+265+14*N+400 : ℕ) : ℝ)+4*D*C+
    10000*d*(D+100*((N+1 : ℕ) : ℝ)))*(O*M) := by dsimp [M];ring
  rw [hid]
  nlinarith only [hwork,hdyn,hboot,hi]
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma maintains (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower)
    (impl : CutImplementation) (K0 C : ℝ) (h Γ a : ℕ → ℝ) (hC : 0 ≤ C)
    (hh : 0 ≤ h (2*b.input.size)) (hΓ : 0 ≤ Γ (2*b.input.size)) (ha : 0 ≤ a (2*b.input.size))
    (hK0 : 0 < K0) (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0
      (h (2*b.input.size)) (Γ (2*b.input.size)) (C*(2*b.input.size)*a (2*b.input.size))
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) :
    Maintains (coreProgram qualityPower impl.program) (coreConstant b.weightExponent qualityPower impl.program C)
      (coreRuntimeOverhead h Γ a qualityPower) 9 false b.input := by
  intro ds hlegal
  obtain ⟨cs,last,hr,hlen,hlast,hcompleted,hprefix⟩ :=
    online b qualityPower hpower impl K0 _ _ _ hK0 hKK himpl ds
  refine ⟨cs,hr,hlen,?_,?_,?_⟩
  · intro j c hc
    exact (hprefix j c hc).correct
  · intro c hc
    have heq : last = c := Option.some.inj (hlast.symm.trans hc)
    subst c
    simpa only [Bool.false_eq_true,if_false,mul_one] using
      hcompleted.work_bound hpower K0 C h Γ a hC hh hΓ ha hlegal
  · intro c hc v
    exact coreProgram_query qualityPower impl.program c v.val
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end
section
namespace DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
open DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma normalized_core_from_cut (d : ℕ)
    (hcut : ∃ (impl : CutImplementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → ImplementsCut impl m (4*d+68) (K m) (h m) (Γ m) (C*m*a m) ξ) :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ), 0 < C ∧ Subpolynomial a ∧
      ∀ b : Core, b.weightExponent = d → Maintains p C a 9 false b.input := by
  obtain ⟨impl,K,h,Γ,a,C,hC,hK,hh,hΓ,ha,hquality,himpl⟩ := hcut
  obtain ⟨N,hN,henv⟩ := exists_computable_cut_quality_envelope C hC.le
  refine ⟨coreProgram N impl.program,coreConstant d N impl.program C,coreRuntimeOverhead h Γ a N,
    coreConstant_positive d N impl.program C hC.le,coreRuntimeOverhead_subpolynomial h Γ a N hh hΓ ha,?_⟩
  intro b hd
  have hKK : K (2*b.input.size) ≤ computableCutQuality N (2*b.input.size) :=
    (hquality _).2.trans (henv _)
  have hxi : 0 < (computableCutQuality N (2*b.input.size))^(-2 : ℤ) := by
    have h32 := computableCutQuality_ge_32 N (2*b.input.size) hN
    positivity
  have hi := himpl (2*b.input.size) _ hxi
  rw [← hd] at hi
  have hm := maintains b N hN impl (K (2*b.input.size)) C h Γ a hC.le
    (hh.1 _).le (hΓ.1 _).le (ha.1 _).le (hK.1 _) hKK (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hi)
  rwa [hd] at hm
end DecrAlmostLinearSSSP.Decremental.NonemptyCore.CoreNativeCut
end

set_option autoImplicit false
open scoped ENNReal NNReal
open DecrAlmostLinearSSSP.Decremental

theorem solution :
    ∀ exponent : ℕ, ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ),
      0 < C ∧ 0 < queryBound ∧ Subpolynomial a ∧
      (∀ i : Input, i.Valid → 2 ≤ i.n → i.W ≤ i.size ^ exponent →
        1 / (i.size : ℝ) < i.accuracy → i.accuracy < 1 →
        Maintains p C a queryBound false i) ∧
      (∀ (b : Core) (K : ℝ), 32 ≤ K → ∀ choose : State b → CutReply b,
        CutQuality b K choose → ∀ s, Attained b K choose s →
        (s.toggles : ℝ) ≤ 16 * K ^ 3 * A b * b.input.size * Real.log (2 * Q b)) := by
  intro exponent
  apply (DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.2.2.2.2) exponent
  exact NonemptyCore.CoreNativeCut.normalized_core_from_cut (exponent+3)
    (NonemptyCut.dynamic_cut_interface (4*(exponent+3)+68))
