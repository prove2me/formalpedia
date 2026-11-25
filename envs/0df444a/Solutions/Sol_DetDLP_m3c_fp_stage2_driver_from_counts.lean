-- Prove2me | solution 1 for DetDLP.m3c_fp_stage2_driver_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T10:31:26.69681+00:00
-- url     : https://prove2.me/submissions/eec0c298-9542-4165-a1fe-54a970b6e817

import Definitions.Def_DetDLP_S8A_FpPrefixSpec
import Definitions.Def_DetDLP_W3C_FpBaseCert
import Definitions.Def_DetDLP_W3C_FpCutExec
import Definitions.Def_DetDLP_W5_M6TapeSimulator
import Theorems.Thm_DetDLP_stage1_complexity_dominance

section
set_option autoImplicit false

namespace DetDLP.W3C.FpCoordinateWidths
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem encodedCons {α : Type} (f : α → List Bool) (x : α) (xs : List α) :
    (Encoding.encodeList f (x :: xs)).length =
      2 * (f x).length + 2 + (Encoding.encodeList f xs).length := by
  simp only [Encoding.encodeList, List.length_cons, List.length_append, w3_frameLength]
  omega

theorem encodedNil {α : Type} (f : α → List Bool) :
    (Encoding.encodeList f []).length = 1 := rfl

def listCap (n width : ℕ) := n * (2*width+2) + 1

theorem encodedListLe {α : Type} (f : α → List Bool) (xs : List α) (width : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ width) :
    (Encoding.encodeList f xs).length ≤ listCap xs.length width := by
  induction xs with
  | nil => simp [listCap, encodedNil]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    simp only [encodedCons, List.length_cons, listCap, Nat.succ_mul] at *
    omega

theorem basisEntryLe {M N : ℕ} (hM : 0 < M) {B : Matrix (Fin N) (Fin N) ℤ}
    (h : IsModularLatticeBasis M B) (i j : Fin N) : (B i j).natAbs ≤ M := by
  classical
  let e (k : Fin N) : ℤ := if k = i then 1 else 0
  obtain ⟨t, ht⟩ := h.2.1 e
  have row (k : Fin N) (hz : ∀ l < k, t l = 0) :
      (B.mulVec t) k = B k k * t k := by
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_single k
    · intro l _ he
      change B k l * t l = 0
      rcases lt_or_gt_of_ne he with hl | hl
      · rw [hz l hl, mul_zero]
      · rw [h.1.1 k l hl, zero_mul]
    · simp
  have before : ∀ k < i, t k = 0 := by
    intro k
    induction k using WellFoundedLT.induction with
    | ind k ih =>
      intro hk
      have eqk := congrFun ht k
      rw [row k (fun l hl => ih l hl (hl.trans hk))] at eqk
      simp only [e, if_neg hk.ne, mul_zero] at eqk
      exact (mul_eq_zero.mp eqk.symm).resolve_left (h.1.2.1 k).ne'
  have diag : B i i ≤ (M : ℤ) := by
    apply Int.le_of_dvd (by exact_mod_cast hM)
    refine ⟨t i, ?_⟩
    have eqi := congrFun ht i
    rw [row i before] at eqi
    simpa [e] using eqi
  have bounds : 0 ≤ B i j ∧ B i j ≤ (M : ℤ) := by
    rcases lt_trichotomy j i with hj | he | hi
    · exact ⟨(h.1.2.2 i j hj).1, (h.1.2.2 i j hj).2.le.trans diag⟩
    · subst j
      exact ⟨(h.1.2.1 i).le, diag⟩
    · simp [h.1.1 i j hi]
  have hi := (Int.natAbs_of_nonneg bounds.1).le.trans bounds.2
  exact_mod_cast hi

def repCap (N b : ℕ) := 2 * (listCap N (b+1) + listCap (N*N) (b+2)) + 5

theorem representativeLe {M N : ℕ} [NeZero M] (r : w3_Rep M N)
    (hr : IsModularLatticeBasis M r.2) : (FpBaseCert.repWord r).length ≤ repCap N (bitLen M) := by
  let xs := List.ofFn fun i => (r.1 i).val
  let entries := (List.finRange N).flatMap fun i => (List.finRange N).map fun j => r.2 i j
  have hx : (encodeNatListBin xs).length ≤ listCap N (bitLen M+1) := by
    have hh := encodedListLe countWord xs (bitLen M+1) (fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact S8G.FpMoment.binaryLen (r.1 i).val_lt.le)
    simpa only [xs, encodeNatListBin, List.length_ofFn] using hh
  have hentries : entries.length = N*N := by simp [entries, List.length_flatMap]
  have he : (Encoding.encodeList encodeIntBin entries).length ≤ listCap (N*N) (bitLen M+2) := by
    rw [← hentries]
    apply encodedListLe
    intro x hx
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact Nat.succ_le_succ (S8G.FpMoment.binaryLen (basisEntryLe (NeZero.pos M) hr i j))
  change (Encoding.encodeList id [encodeNatListBin xs, Encoding.encodeList encodeIntBin entries]).length ≤ _
  simp only [encodedCons, encodedNil, id_eq, repCap]
  omega

end DetDLP.W3C.FpCoordinateWidths
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpCoordinateWidths
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpStep FpTraceStep FpBaseCert BlockLookup NineOracleLoop

def planCap (b m : ℕ) := 2 * (b+1 + m*2*b) + 6
def blocksCap (b m N : ℕ) := listCap m (listCap N (b+1))
def decompCap (b m : ℕ) := listCap (2*m) (b+1)
def rowCap (b N : ℕ) := 2 * (listCap N (b+1) + 1) + 5

theorem planLe {p : ℕ} [Fact p.Prime] (L : Plan p)
    (ok : m89_fp_plan_ok L) : (m89_fp_plan_word L).length ≤ planCap (bitLen p) (m p) := by
  rcases L with _ | ⟨t, seed⟩
  · change 1 ≤ 2 * _ + 6
    omega
  · obtain ⟨h64, hbig, ht, _⟩ := ok
    have hbound := m89_decode.threshold_le (show 2 ≤ m p from le_max_left ..) h64 hbig
    have hcw := S8G.FpMoment.binaryLen (ht.trans_le hbound)
    simp only [m89_fp_plan_word, List.length_cons, encodedCons, encodedNil, id_eq,
      List.length_ofFn, planCap]
    omega

private theorem listCap_mono {n k w : ℕ} (h : n ≤ k) : listCap n w ≤ listCap k w :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 1

theorem blocksLe {p : ℕ} [Fact p.Prime] (B : FpOracles.Blocks p) :
    (encodeFpFactorBlocks B).length ≤ blocksCap (bitLen p) (m p) (fb B).totalCoords := by
  have inner (i : Fin (m p)) : (B i).length ≤ (fb B).totalCoords := by
    have hs : (B i).length ≤ ∑ j : Fin (m p), (B j).length :=
      Finset.single_le_sum (f := fun j => (B j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    change _ ≤ (∑ j : Fin (m p), ((B j).map Additive.ofMul).length) + 2
    simpa only [List.length_map] using hs.trans (Nat.le_add_right _ 2)
  unfold encodeFpFactorBlocks blocksCap
  refine (le_of_le_of_eq ?_ (congrArg (fun k => listCap k (listCap (fb B).totalCoords (bitLen p+1)))
    (List.length_ofFn (f := B))))
  apply encodedListLe
  intro xs hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (encodedListLe (fun x : (ZMod p)ˣ => countWord (x : ZMod p).val) (B i) (bitLen p+1)
    (fun x _ => S8G.FpMoment.binaryLen (x : ZMod p).val_lt.le)).trans
    (listCap_mono (inner i))

theorem decompLe {p m : ℕ} [Fact p.Prime] (A B : Fin m → (ZMod p)ˣ) :
    (encodeFpDecomp A B).length ≤ decompCap (bitLen p) m := by
  let xs := (List.finRange m).flatMap fun i => [(A i : ZMod p).val, (B i : ZMod p).val]
  have hlen : xs.length = 2*m := by simp [xs, List.length_flatMap, Nat.mul_comm]
  unfold decompCap
  rw [← hlen]
  apply encodedListLe
  intro x hx
  obtain ⟨i, _, hm⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact S8G.FpMoment.binaryLen (ZMod.val_lt _).le

theorem rowPacketLe {M : ℕ} [NeZero M] (r : List ℤ) (rhs : ℕ) (hrhs : rhs ≤ 1) :
    (rowPkt M rhs r).length ≤ rowCap (bitLen M) r.length := by
  have hxs := encodedListLe countWord (r.map (residue M)) (bitLen M+1) (fun x hx => by
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    rw [residue_eq]
    exact S8G.FpMoment.binaryLen (ZMod.val_lt _).le)
  have hr : (countWord rhs).length ≤ 1 := by
    interval_cases rhs <;> decide
  simp only [List.length_map] at hxs
  simp only [rowPkt, rowCap, encodedCons, encodedNil, id_eq, encodeNatListBin]
  omega

theorem packedLe (s : FpState) (d : ℕ) (h : ∀ w ∈ fields s, w.length ≤ d) :
    (packState s).length ≤ listCap 12 d :=
  encodedListLe id (fields s) d h

theorem pairLength (s a : Word) : (pairWord s a).length = 2*s.length+1+a.length := by
  simp [pairWord, List.length_flatMap, Nat.mul_comm]
  omega

theorem tag3Length (u : Word) : (tag9 3 u).length = u.length+3 := by rfl
theorem tag8Length (u : Word) : (tag9 8 u).length = u.length+4 := by rfl

end DetDLP.W3C.FpCoordinateWidths
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpCoordinateWidths
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpStep FpTraceStep FpBaseCert FpBaseOne BlockLookup NineOracleLoop

def decompQueryCap (b m : ℕ) := 2*(listCap 2 (b+1) + planCap b m)+5
def updateQueryCap (b N : ℕ) := 2*((b+1)+(N+1)+repCap N b+listCap N (b+1)+1)+11
def fieldLimit (b bm m N input : ℕ) :=
  16+input+b+bm+N+planCap b m+blocksCap b m N+decompCap b m+
    rowCap bm N+repCap N bm+decompQueryCap b m+updateQueryCap bm N
def cycleCap (d : ℕ) := 2*listCap 12 d+d+5

def baseWords (s : FpState) := [countWord s.p, countWord s.g, countWord s.a,
  countWord s.T, countWord s.fuel, s.planWord, s.blocksWord]
def Header (d : ℕ) (s : FpState) := ∀ w ∈ baseWords s, w.length ≤ d
structure Stored (d : ℕ) (s : FpState) : Prop where
  header : Header d s
  rep : s.repWord.length ≤ d
  pkt : s.pktWord.length ≤ d
  pre : s.pre.length ≤ d

theorem packStored {s : FpState} {d : ℕ} (h : Stored d s)
    (hp : (countWord s.phase).length ≤ d) (hi : (countWord s.idx).length ≤ d) :
    (packState s).length ≤ listCap 12 d := by
  apply packedLe
  intro w hw
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact hp | exact hi | exact h.rep | exact h.pkt | exact h.pre | exact h.header _ (by simp [baseWords])

private theorem carry {s : FpState} {d : ℕ} (h : Header d s) (k i : ℕ) (hk : (k == 8) = false)
    (r w pre : Word) : Header d (nextState (packState s) k i s.blocksWord r w pre) := by
  simpa only [Header, baseWords, nextState, unpackState_packState, hk, Bool.cond_false] using h

theorem nativeHeader {p : ℕ} [Fact p.Prime] (L : Plan p) (B : FpOracles.Blocks p)
    (g a : (ZMod p)ˣ) (s : FpState) (hs : Ready B L g a s) (ok : m89_fp_plan_ok L)
    (hT : s.T ≤ p) (I : ℕ) (fuel : (countWord s.fuel).length ≤ I+1) :
    Header (fieldLimit (bitLen p) (bitLen (p-1)) (m p) (fb B).totalCoords I) s := by
  have hp := S8G.FpMoment.binaryLen (le_refl p)
  have hg := S8G.FpMoment.binaryLen (g : ZMod p).val_lt.le
  have ha := S8G.FpMoment.binaryLen (a : ZMod p).val_lt.le
  have ht := S8G.FpMoment.binaryLen hT
  have hl := planLe L ok
  have hb := blocksLe B
  intro w hw
  simp only [baseWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [hs.prime, hs.gen, hs.target, hs.plan, hs.blocks] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold fieldLimit <;> omega

theorem decompQueryLe {p : ℕ} [Fact p.Prime] (x : (ZMod p)ˣ) (L : Plan p)
    (ok : m89_fp_plan_ok L) :
    (Encoding.encodeList id [encodeNatListBin [p,(x : ZMod p).val], m89_fp_plan_word L]).length ≤
      decompQueryCap (bitLen p) (m p) := by
  have hp : (encodeNatListBin [p,(x : ZMod p).val]).length ≤ listCap 2 (bitLen p+1) := by
    apply encodedListLe
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact S8G.FpMoment.binaryLen (le_refl _)
    · exact S8G.FpMoment.binaryLen (x : ZMod p).val_lt.le
  have hl := planLe L ok
  simp only [encodedCons, encodedNil, id_eq, decompQueryCap]
  omega

theorem updateQueryLe {M N : ℕ} [NeZero M] (r : w3_Rep M N) (hr : IsModularLatticeBasis M r.2)
    (z : w3_Label M N) :
    (encodeCosetUpdateInput M (fun i => (r.1 i).val) r.2 (fun i => (z i).val) 0).length ≤
      updateQueryCap (bitLen M) N := by
  have hM := S8G.FpMoment.binaryLen (le_refl M)
  have hN := w3_queryIndexLength N
  have hrep := representativeLe r hr
  have hrow : (encodeNatListBin (List.ofFn fun i => (z i).val)).length ≤ listCap N (bitLen M+1) := by
    have h := encodedListLe countWord (List.ofFn fun i => (z i).val) (bitLen M+1) (fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact S8G.FpMoment.binaryLen (z i).val_lt.le)
    simpa only [encodeNatListBin, List.length_ofFn] using h
  change (encodeCosetRep (fun i => (r.1 i).val) r.2).length ≤ _ at hrep
  have zero : (countWord 0).length = 1 := rfl
  simp only [encodeCosetUpdateInput, encodedCons, encodedNil, id_eq, zero, updateQueryCap]
  omega

abbrev middle (s : FpState) (rep : Word) := nextState (packState s) 5 s.idx s.blocksWord rep [] []

def Six (s : FpState) (a u final : Word) (cap : ℕ) : Prop :=
  let mid := middle s a
  let v := updateState s a u
  (pairWord (packState s) a).length ≤ cap ∧
  (pairWord (packState mid) (tag9 3 (queryInput 3 mid))).length ≤ cap ∧
  u.length ≤ cap ∧ (pairWord (packState mid) u).length ≤ cap ∧
  (pairWord (packState v) (tag9 8 (queryInput 8 v))).length ≤ cap ∧ final.length ≤ cap

theorem sixWords {p N : ℕ} [Fact p.Prime] [NeZero (p-1)] (L : Plan p) (ok : m89_fp_plan_ok L)
    (x : (ZMod p)ˣ) (s : FpState) (I : ℕ)
    (r r' : w3_Rep (p-1) N) (basis : IsModularLatticeBasis (p-1) r.2)
    (basis' : IsModularLatticeBasis (p-1) r'.2) (z : w3_Label (p-1) N)
    (u : Word) (hu : u.length ≤ decompCap (bitLen p) (m p))
    (hp : s.p = p) (hphase : s.phase = 4) (hidx : s.idx < N)
    (hdim : (decodeBlocks s.blocksWord).flatten.length+2 = N)
    (hq3 : queryInput 3 (middle s (repWord r)) =
      Encoding.encodeList id [encodeNatListBin [p,(x : ZMod p).val], m89_fp_plan_word L])
    (hq8 : queryInput 8 (updateState s (repWord r) u) =
      encodeCosetUpdateInput (p-1) (fun i => (r.1 i).val) r.2 (fun i => (z i).val) 0)
    (hs : Stored (fieldLimit (bitLen p) (bitLen (p-1)) (m p) N I) s) :
    let d := fieldLimit (bitLen p) (bitLen (p-1)) (m p) N I
    Stored d (updateState s (repWord r) u) ∧
      Six s (repWord r) u (repWord r') (cycleCap d) := by
  intro d
  have rep := representativeLe r basis
  have rep' := representativeLe r' basis'
  have rd : (repWord r).length ≤ d := by dsimp only [d, fieldLimit]; omega
  have rd' : (repWord r').length ≤ d := by dsimp only [d, fieldLimit]; omega
  have ud : u.length ≤ d := by dsimp only [d, fieldLimit]; omega
  let raw := initRowCounts (decodeBlocks s.blocksWord) (decodeFrames u) s.idx
  have hraw : raw.length = N := by
    change ((List.range ([] :: [] :: (decodeBlocks s.blocksWord).flatten).length).map _).length = N
    simpa using hdim
  have row := rowPacketLe (M := p-1) raw 0 (by decide)
  rw [hraw] at row
  have rowd : (rowPkt (p-1) 0 raw).length ≤ d := by dsimp only [d, fieldLimit]; omega
  let mid := middle s (repWord r)
  let v := updateState s (repWord r) u
  have hm : Stored d mid :=
    ⟨carry hs.header 5 s.idx rfl _ _ _, by simpa [mid, middle, nextState] using rd,
      Nat.zero_le _, Nat.zero_le _⟩
  have hv : Stored d v :=
    ⟨carry hs.header 4 (s.idx+1) rfl _ _ _, by simpa [v, updateState, nextState] using rd,
      by simpa only [v, updateState, nextState, unpackState_packState, hp, raw] using rowd,
      Nat.zero_le _⟩
  have idx := w3_queryIndexLength s.idx
  have idx' := w3_queryIndexLength (s.idx+1)
  have hd : N+8 ≤ d := by dsimp only [d, fieldLimit]; omega
  have src := packStored hs (by rw [hphase]; exact (w3_queryIndexLength 4).trans (by omega))
    (idx.trans (by omega))
  change (packState s).length ≤ listCap 12 d at src
  have midSize := packStored hm
    (show (countWord 5).length ≤ d from (w3_queryIndexLength 5).trans (by omega))
    (show (countWord s.idx).length ≤ d from idx.trans (by omega))
  have dst := packStored hv
    (show (countWord 4).length ≤ d from (w3_queryIndexLength 4).trans (by omega))
    (show (countWord (s.idx+1)).length ≤ d from idx'.trans (by omega))
  have q3 : (queryInput 3 mid).length ≤ d := by
    rw [show queryInput 3 mid = _ from hq3]
    exact (decompQueryLe x L ok).trans (by dsimp only [d, fieldLimit]; omega)
  have q8 : (queryInput 8 v).length ≤ d := by
    rw [show queryInput 8 v = _ from hq8]
    exact (updateQueryLe r basis z).trans (by dsimp only [d, fieldLimit]; omega)
  refine ⟨hv, ?_⟩
  change (pairWord (packState s) (repWord r)).length ≤ cycleCap d ∧
    (pairWord (packState mid) (tag9 3 (queryInput 3 mid))).length ≤ cycleCap d ∧
    u.length ≤ cycleCap d ∧ (pairWord (packState mid) u).length ≤ cycleCap d ∧
    (pairWord (packState v) (tag9 8 (queryInput 8 v))).length ≤ cycleCap d ∧
    (repWord r').length ≤ cycleCap d
  simp only [pairLength, tag3Length, tag8Length, cycleCap]
  omega

end DetDLP.W3C.FpCoordinateWidths
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpCoordinateWidths

theorem nativeInputLe {p : ℕ} [Fact p.Prime] (g a : (ZMod p)ˣ) :
    (FpOracles.input g a).length ≤ listCap 3 (bitLen p+1) := by
  apply encodedListLe
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact S8G.FpMoment.binaryLen (le_refl _)
  · exact S8G.FpMoment.binaryLen (g : ZMod p).val_lt.le
  · exact S8G.FpMoment.binaryLen (a : ZMod p).val_lt.le

end DetDLP.W3C.FpCoordinateWidths
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpDriverAssembly
open FpCoordinateWidths

noncomputable def headSize (k b : ℕ) := ⌊mainSpaceBound k b⌋₊ + b + 16
noncomputable def headCap (k b : ℕ) :=
  16 * (cycleCap (fieldLimit b b (b+2) (headSize k b) (listCap 3 (b+1))) + 1)
noncomputable def headOracle (k b : ℕ) :=
  mainSpaceBound k b + polyBound k (headSize k b + b + 1)
noncomputable abbrev headRounds (k b : ℕ) := 2*headSize k b + 3

def kitCost {en de : FpOracles.Port} (kit : FpOracles.Kit en de) : ℕ :=
  kit.prepC+kit.enumC+kit.decC+kit.updateC

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpCoordinateWidths
open FpOracles FpStep FpTraceStep FpBaseOne FpBaseCert BlockLookup NineOracleLoop
open Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] (B : FpOracles.Blocks p) {en de : Port} (kit : Kit en de) (L : Plan p)
variable (large : w3_large p (p-1)) (ok : m89_fp_plan_ok L)
variable (hB : ∀ i, (B i).Nodup ∧ (B i).toFinset = m89_fp_plan_block L i)

include large ok hB in
private theorem tupleAnswerSized (x : (ZMod p)ˣ) : ∃ (U : (fb B).BlockTuple) (u : List Bool),
    (fb B).tupleVal U = Additive.ofMul x ∧ decodeFrames u = words (fb B) enc U ∧
    u.length ≤ decompCap (bitLen p) (m p) ∧
    run (kit.ports 3) (Encoding.encodeList id [encodeNatListBin [p,(x:ZMod p).val],m89_fp_plan_word L]) u
      (mainSpaceBound kit.decC (bitLen p)) (polyBound kit.decC (bitLen p)) := by
  classical
  obtain ⟨A,D,mem,prod,run⟩ := kit.decompose p L ok x (FpTraceBounds.planCover large L ok x)
  have idx (i : Fin (m p)) (v : (ZMod p)ˣ) (hv : v ∈ m89_fp_plan_block L i) :
      ∃ k : Fin ((fb B).blocks i).length, ((fb B).blocks i).get k = Additive.ofMul v := by
    apply List.mem_iff_get.mp
    change _ ∈ (B i).map Additive.ofMul
    exact List.mem_map.mpr ⟨v,List.mem_toFinset.mp ((hB i).2.symm ▸ hv),rfl⟩
  choose kA hkA using fun i => idx i (A i) (mem i).1
  choose kD hkD using fun i => idx i (D i) (mem i).2
  let U : (fb B).BlockTuple := fun i => ![kA i,kD i]
  refine ⟨U,encodeFpDecomp A D,?_,?_,decompLe A D,run⟩
  · simp only [IndexedFactorBase.tupleVal,U,Matrix.cons_val_zero,Matrix.cons_val_one,hkA,hkD,← ofMul_mul,← ofMul_prod]; exact congrArg Additive.ofMul prod
  · simp only [encodeFpDecomp,encodeNatListBin,decodeFrames_map,List.map_flatMap,List.map_cons,List.map_nil,BlockLookup.words,U,Matrix.cons_val_zero,Matrix.cons_val_one,hkA,hkD]; rfl

variable (g a : (ZMod p)ˣ)

include large ok hB in
theorem boundedChain [NeZero (p-1)] (z : w3_Label (p-1) (fb B).totalCoords)
    (consistent : ∀ (j : Fin (fb B).totalCoords) (T : (fb B).BlockTuple),
      (fb B).tupleVal T = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j →
      w3_holds ((fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt T i : ZMod (p-1))),0) z)
    (I : ℕ) (s : FpState) (hs : Ready B L g a s) (rep : w3_Rep (p-1) (fb B).totalCoords)
    (inv : Stage2Trace.Invariant z rep) (n : ℕ) (hn : s.idx + n = (fb B).totalCoords)
    (stored : Stored (fieldLimit (bitLen p) (bitLen (p-1)) (m p) (fb B).totalCoords I) s) :
    ∃ (endState : FpState) (r : w3_Rep (p-1) (fb B).totalCoords),
      Ready B L g a endState ∧ endState.idx = (fb B).totalCoords ∧ Stage2Trace.Invariant z r ∧
      endState.T = s.T ∧ w3_coset r ⊆ w3_coset rep ∧
      (∀ j : Fin (fb B).totalCoords, s.idx ≤ j.val → ∃ T : (fb B).BlockTuple,
        (fb B).tupleVal T = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j ∧
        ∀ y ∈ w3_coset r, w3_holds ((fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt T i : ZMod (p-1))),0) y) ∧
      Stored (fieldLimit (bitLen p) (bitLen (p-1)) (m p) (fb B).totalCoords I) endState ∧
      FpDecompLoop.Chain (R kit p (fb B).totalCoords)
        (cycleCap (fieldLimit (bitLen p) (bitLen (p-1)) (m p) (fb B).totalCoords I))
        n s (repWord rep) endState (repWord r) := by
  classical
  induction n generalizing s rep with
  | zero => exact ⟨s,rep,hs,by omega,inv,rfl,Set.Subset.rfl,fun j hj => by have := j.isLt; omega,stored,.done⟩
  | succ n ih =>
    let j : Fin (fb B).totalCoords := ⟨s.idx,by omega⟩
    let x := ((fb B).elem (Additive.ofMul g) (Additive.ofMul a) j).toMul
    obtain ⟨T,u,hT,hu,husize,hdec⟩ := tupleAnswerSized B kit L large ok hB x
    let mid := nextState (packState s) 5 s.idx s.blocksWord (repWord rep) [] []
    let v := updateState s (repWord rep) u
    have hv : Ready B L g a v := by
      obtain ⟨_,hp,hg,ha,hl,hb⟩ := hs
      simp only [v,updateState,nextState,unpackState_packState]; exact ⟨rfl,hp,hg,ha,hl,hb⟩
    have hvIdx : v.idx = s.idx+1 := by simp [v,updateState,nextState]
    have dim : (decodeBlocks s.blocksWord).flatten.length+2 = (fb B).totalCoords := by rw [hs.blocks,sizeBlocks]; rfl
    have dim' : (decodeBlocks v.blocksWord).flatten.length+2 = (fb B).totalCoords := by rw [hv.blocks,sizeBlocks]; rfl
    have hq : queryInput 3 mid = Encoding.encodeList id [encodeNatListBin [p,(x:ZMod p).val],m89_fp_plan_word L] := by
      simp only [queryInput,mid,nextState,unpackState_packState,hs.prime,hs.gen,hs.target,hs.plan,hs.blocks]
      rw [show ((decodeBlocks (encodeFpFactorBlocks B)).flatten ++ [countWord (g:ZMod p).val,countWord (a:ZMod p).val]).getD s.idx [] = enc (Additive.ofMul x) from coordinate B g a j]; simp [enc]
    have dc : R kit p (fb B).totalCoords (tag9 3 (queryInput 3 mid)) u := by
      rw [hq]; exact ⟨3,_,rfl,MachineComposition.runsWithin_mono hdec (le_max_right ..) (le_max_right ..)⟩
    let row : w3_Row (p-1) (fb B).totalCoords := (fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt T i : ZMod (p-1)),0)
    let raw := initRowCounts (decodeBlocks s.blocksWord) (decodeFrames u) s.idx
    have nd (i) : (((fb B).blocks i).map enc).Nodup := by
      change (((B i).map Additive.ofMul).map enc).Nodup
      rw [List.map_map]; apply (hB i).1.map; intro x y h; apply Units.ext; apply ZMod.val_injective
      exact (decode_count _).symm.trans ((congrArg PolyT.bval h).trans (decode_count _))
    have rawok : raw.map (fun t : ℤ => (t : ZMod (p-1))) = List.ofFn row.1 := by
      have h := congrArg Prod.fst (initRowCounts_correct (fb B) enc nd (p-1) (fun _ => T) j)
      simpa [raw,hs.blocks,wireBlocks,hu,row,w3_initRows,j] using h
    obtain ⟨r,upd,hi,_,hc⟩ := FpRowTrace.update_call kit (by have := large.2.1; omega : 2 ≤ p-1)
      (fb B).genCoord.pos v rep row z inv (consistent j T hT) raw (by rw [hv.prime]) dim' rawok
    have eqv : {v with repWord := repWord rep, pktWord := rowPkt (p-1) row.2.val raw} = v := by
      dsimp only [v,updateState,nextState]; simp only [unpackState_packState,hs.prime,row,ZMod.val_zero]; rfl
    change FpRowTrace.calls kit _ _ (tag9 8 (queryInput 8 {v with repWord := repWord rep, pktWord := rowPkt (p-1) row.2.val raw})) (repWord r) at hc
    rw [eqv] at hc
    obtain ⟨i,w,eq,hr⟩ := hc
    have uc : R kit p (fb B).totalCoords (tag9 8 (queryInput 8 v)) (repWord r) :=
      ⟨i,w,eq,MachineComposition.runsWithin_mono hr (le_max_left ..) (le_max_left ..)⟩
    have q8 := FpRowTrace.update_query_exact v (fun i => (rep.1 i).val) rep.2 row.1
      row.2.val raw (by rw [hv.prime]) dim' rawok
    rw [eqv] at q8
    rw [show row.2.val = 0 by simp [row]] at q8
    obtain ⟨storedNext, wordsBound⟩ := sixWords L ok x s I rep r inv.1 hi.1 row.1 u husize
      hs.prime hs.phase (by omega) dim hq q8 stored
    obtain ⟨b0,b1,b2,b3,b4,b5⟩ := wordsBound
    obtain ⟨e,last,he,hei,hil,hT',sub,rows,storedEnd,tail⟩ := ih v hv r hi (by omega) storedNext
    have vv : v.T = s.T := by simp [v,updateState,nextState]
    have stepSub : w3_coset r ⊆ w3_coset rep := by rw [upd.2]; exact Set.sep_subset ..
    refine ⟨e,last,he,hei,hil,hT'.trans vv,sub.trans stepSub,?_,storedEnd,?_⟩
    · intro i hj
      by_cases eqi : i = j
      · subst i; refine ⟨T,hT,fun y hy => ?_⟩; have mem := sub hy; rw [upd.2] at mem; exact mem.2
      · exact rows i (by have hne : i.val ≠ s.idx := fun h => eqi (Fin.ext h); omega)
    exact .step (cycle_of_answers hs.phase (by omega) dc uc b0 b1 b2 b3 b4 b5) tail

open FpLargeEntry

noncomputable abbrev firstCoordinateState {p : ℕ} [Fact p.Prime] (g a : (ZMod p)ˣ)
    (L : Plan p) (B : FpOracles.Blocks p) :=
  let v := next (g : ZMod p).val (a : ZMod p).val L
  let b := encodeFpFactorBlocks B
  let xs := FpTraceStep.coords (decodeBlocks b)
  let raw := xs.map fun j => if j = (decodeBlocks b).flatten.length then (1 : ℤ) else 0
  nextState (packState v) 4 0 b (fullRep xs) (rowPkt (v.p-1) 1 raw) []

include large ok in
theorem firstCoordinateStored [NeZero (p-1)] :
    Stored (fieldLimit (bitLen p) (bitLen (p-1)) (m p) (fb B).totalCoords
      (input g a).length) (firstCoordinateState g a L B) := by
  let I := (input g a).length
  let N := (fb B).totalCoords
  let d := fieldLimit (bitLen p) (bitLen (p-1)) (m p) N I
  let v := next (g : ZMod p).val (a : ZMod p).val L
  let b := encodeFpFactorBlocks B
  let xs := FpTraceStep.coords (decodeBlocks b)
  let raw := xs.map fun j => if j = (decodeBlocks b).flatten.length then (1 : ℤ) else 0
  let s := firstCoordinateState g a L B
  have hbase : v.p=p ∧ v.g=(g : ZMod p).val ∧ v.a=(a : ZMod p).val ∧
      v.planWord=m89_fp_plan_word L ∧ v.fuel=0 := by
    simp [v, prepared, FpLargeEntry.saved, start, prepAnswer, second, encodeFpDLPInput]
  have hT : v.T ≤ p := by
    cases L with
    | none =>
      have hbig : 4096 * m p ≤ p-1-1 := large.2.2
      exact False.elim (ok ⟨large.2.1, by omega⟩)
    | some plan =>
      obtain ⟨t, seed⟩ := plan
      obtain ⟨h64, hbig, ht, _⟩ := ok
      simpa [v, next, prepared, prepAnswer, second, m89_fp_plan_word] using
        ht.trans_le (m89_decode.threshold_le (show 2 ≤ m p from le_max_left ..) h64 hbig)
  have ready : Ready B L g a s := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩
    · simpa only [s, firstCoordinateState, nextState, unpackState_packState] using hbase.1
    · simpa only [s, firstCoordinateState, nextState, unpackState_packState] using hbase.2.1
    · simpa only [s, firstCoordinateState, nextState, unpackState_packState] using hbase.2.2.1
    · simpa only [s, firstCoordinateState, nextState, unpackState_packState] using hbase.2.2.2.1
  have hts : s.T ≤ p := by
    simpa only [s, firstCoordinateState, nextState, unpackState_packState] using hT
  have hfuel : s.fuel=0 := by
    simpa [s, firstCoordinateState, nextState] using hbase.2.2.2.2
  have hx : xs = List.range N := by
    apply congrArg List.range
    change (decodeBlocks (encodeFpFactorBlocks B)).flatten.length+2 = (fb B).totalCoords
    rw [sizeBlocks]
    rfl
  have hrep : (fullRep xs).length ≤ repCap N (bitLen (p-1)) := by
    rw [hx, fullRep_correct]
    simpa only [repWord, w3_full, Pi.zero_apply, ZMod.val_zero] using
      representativeLe (w3_full (p-1) N) (Stage2Trace.full (0 : w3_Label (p-1) N)).1
  have hraw : raw.length=N := by simp [raw,hx]
  have hrow := rowPacketLe (M := p-1) raw 1 le_rfl
  rw [hraw] at hrow
  change Stored d s
  refine ⟨nativeHeader L B g a s ready ok hts I (by rw [hfuel]; change 1 ≤ I+1; omega), ?_, ?_, Nat.zero_le _⟩
  · change (fullRep xs).length ≤ d
    dsimp only [d, fieldLimit]
    omega
  · change (rowPkt (v.p-1) 1 raw).length ≤ d
    rw [hbase.1]
    dsimp only [d, fieldLimit]
    omega

end DetDLP.W3C.FpCoordinateWidths
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpNativeQuery

open M89S1 DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem productIndex {m n : ℕ} (i : Fin m) (j : Fin n) {h} :
    finProdFinEquiv.symm (⟨i.val * n + j.val, h⟩ : Fin (m * n)) = (i, j) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change i.val * n + j.val = j.val + n * i.val
  ac_rfl

private theorem ofFnProduct {α : Type} {m n : ℕ} (f : Fin m → Fin n → α) :
    List.ofFn (fun k : Fin (m*n) => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) =
      (List.finRange m).flatMap fun i => List.ofFn (f i) := by
  rw [List.ofFn_mul]
  simp only [productIndex, List.ofFn_eq_map, List.flatMap_def]

private theorem seedBits {p m : ℕ} (seed : FpSeed p m) :
    List.ofFn (fpBits seed) =
    ((List.finRange m).flatMap fun i => [(seed i).1.val + 1, (seed i).2.val]).flatMap
      (digitWord (bitLen p)) := by
  let num (i : Fin (m*2)) := fpWords seed (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have nums : List.ofFn num =
      (List.finRange m).flatMap fun i => [(seed i).1.val+1, (seed i).2.val] := by
    rw [show List.ofFn num = _ from ofFnProduct (fpWords seed)]
    apply List.flatMap_congr
    intro i _
    simp [fpWords]
  rw [← nums, List.ofFn_eq_map (f := num), List.flatMap_map]
  exact ofFnProduct (fun i j => (num i).testBit (j : Fin (bitLen p)).rev.val)

private theorem filterRange (l t : ℕ) (ht : t ≤ l) :
    (List.range l).filter (fun i => decide (i < t)) = List.range t := by
  induction l, ht using Nat.le_induction with
  | base => apply List.filter_eq_self.mpr; intro i h; simpa using h
  | succ l hl ih => rw [List.range_succ, List.filter_append, ih]; simp [Nat.not_lt.mpr hl]

theorem seedReadback {p m : ℕ} [hp : Fact p.Prime] (seed : FpSeed p m) :
    FpStep.seedNatWord (bitLen p) (List.ofFn (fpBits seed)) =
      encodeNatListBin ((List.finRange m).flatMap fun i => [(seed i).1.val+1,(seed i).2.val]) := by
  have finish (b : ℕ) (w : List Bool) : FpStep.seedNatWord b w = m89_decode_step.fpFinish b w := by
    unfold FpStep.seedNatWord m89_decode_step.fpFinish m89_enum_words.indices m89_enum_words.coord
    rw [List.take_range, Nat.min_eq_left (Nat.div_le_self ..), filterRange _ _ (Nat.div_le_self ..)]
  rw [finish, seedBits]
  apply m89_decode_finish.finish_packed _ (Nat.clog_pos (by decide) hp.out.two_le)
  intro x hx
  obtain ⟨i, _, h⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · apply LT.lt.trans_le _ (Nat.le_pow_clog (by decide : 1 < 2) p)
    have h := (seed i).1.isLt
    omega
  · exact (seed i).2.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) p)

noncomputable abbrev threshold (p : ℕ) := hashThreshold p (p-1) (blockCount (bitLen p)) (p-1)

noncomputable def nativeQuery {p : ℕ} [Fact p.Prime] [NeZero (p-1)]
    (seed : FpSeed p (blockCount (bitLen p))) (B : FpOracles.Blocks p) (g : (ZMod p)ˣ)
    (y : w3_Label (p-1) (w3_fpFB B).totalCoords) (u : List Bool) : w3_Query :=
  { V := Additive (ZMod p)ˣ, M := p-1, nz := inferInstance, b := bitLen p,
    m := blockCount (bitLen p), k := Nat.clog 2 (2 * threshold p), FB := w3_fpFB B,
    P := Additive.ofMul g, y := y,
    code := w3_tupleWord (w3_fpFB B) (fun A => w3_bits (bitLen p) (A.toMul : ZMod p).val),
    pre := u,
    input := FpStep.fpQueryInput p (g : ZMod p).val (p-1) (threshold p)
      (encodeNatListBin ((List.finRange _).flatMap fun i => [(seed i).1.val+1,(seed i).2.val]))
      (encodeFpFactorBlocks B) (encodeNatListBin (List.ofFn fun j => (y j).val)) u,
    addr := fun i r => (((seed i).1.val+1) * (((w3_fpFB B).blocks i).get r).toMul.val.val +
      (seed i).2.val) % p }

theorem nativeQueryValid {p : ℕ} [hp : Fact p.Prime] [NeZero (p-1)]
    (large : w3_large p (p-1)) (seed : FpSeed p (blockCount (bitLen p)))
    (B : FpOracles.Blocks p) (g : (ZMod p)ˣ)
    (hB : ∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (threshold p) seed i)
    (s : FpStep.FpState) (sp : s.p = p) (sg : s.g = (g : ZMod p).val) (st : s.T = threshold p)
    (splan : s.planWord = m89_fp_plan_word (some (threshold p, seed)))
    (sblocks : s.blocksWord = encodeFpFactorBlocks B)
    (y : w3_Label (p-1) (w3_fpFB B).totalCoords) (pre : List Bool)
    (r : FpCutExec.Rep (nativeQuery seed B g y pre)) (u : List Bool) :
    w3_fpQueries (FpCutExec.probe (nativeQuery seed B g y pre) s r u) := by
  have hinput : FpStep.queryInput 6 (FpCutExec.st s 6 0 0 (FpCutExec.repWord r) [] u) =
      (nativeQuery seed B g r.1 u).input := by
    change FpStep.fpQueryInput s.p s.g (s.p-1) s.T
      (FpStep.seedNatWord (S8G.FpMoment.Code.width s.p) (second s.planWord.tail))
      s.blocksWord (first (FpCutExec.repWord r)) u = _
    rw [sp, sg, st, splan, sblocks, S8G.FpMoment.Code.width_eq]
    simp [m89_fp_plan_word, second, FpCutExec.repWord, encodeCosetRep, seedReadback, nativeQuery]
  have hM := large.2.1
  have hblocks := large.2.2
  refine ⟨p, hp, large.1, by omega, hM, by omega, seed, B, hB, g, r.1, u, ?_⟩
  change FpCutExec.probe (nativeQuery seed B g y pre) s r u = nativeQuery seed B g r.1 u
  unfold FpCutExec.probe
  rw [hinput]
  rfl

end DetDLP.W3C.FpNativeQuery
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpDriverAssembly
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpStep FpTraceStep FpBaseCert FpLargeEntry FpCoordinateWidths FpNativeQuery
open NineOracleLoop BlockLookup DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT.Computation

theorem outputSpace {A : PrimitiveMachine} {out : Fin A.tapeCount} {x y : Word} {t σ : ℝ}
    (run : RunsWithin A out x y t σ) : y.length ≤ ⌊σ⌋₊+8 := by
  obtain ⟨_,c,_,_,eq,tr⟩ := w5_EntryTapeCode.call A out x y t σ run (fun _ => false) (fun _ => none)
  have hb := tr.prefix le_rfl tr.trace (w5_EntryTapeCode.lane A out false true)
  rw [← eq]
  refine le_trans ?_ hb
  generalize c.stacks (w5_EntryTapeCode.lane A out false true) = tags
  generalize c.stacks (w5_EntryTapeCode.lane A out false false) = vals
  induction tags generalizing vals with
  | nil => rfl
  | cons a l ih => cases a <;> cases vals <;> simp [w5_EntryTapeCode.extract,ih]

theorem field_mono {b bm b' bm' m m' N N' I I' : ℕ}
    (hb : b ≤ b') (hm : bm ≤ bm') (hblocks : m ≤ m') (hN : N ≤ N') (hI : I ≤ I') :
    fieldLimit b bm m N I ≤ fieldLimit b' bm' m' N' I' := by
  unfold fieldLimit decompQueryCap updateQueryCap decompCap planCap blocksCap repCap rowCap listCap
  gcongr

theorem publicCap {p : ℕ} [Fact p.Prime] (k : ℕ) (g a : (ZMod p)ˣ) (N : ℕ)
    (hn : N ≤ headSize k (bitLen p)) :
    16*(cycleCap (fieldLimit (bitLen p) (bitLen (p-1)) (m p) N (input g a).length)+1) ≤
      headCap k (bitLen p) := by
  have h := field_mono (le_refl (bitLen p)) (show bitLen (p-1) ≤ bitLen p from
    Nat.clog_mono_right 2 (Nat.sub_le p 1)) (S8G.FpMoment.blockUpper (bitLen p)) hn (nativeInputLe g a)
  unfold headCap cycleCap listCap
  gcongr <;> exact h

theorem dimensionOfRun {en de : Port} (kit : Kit en de) {p : ℕ} [Fact p.Prime]
    (L : Plan p) (B : FpOracles.Blocks p) (hr : run (kit.ports 2)
      (Encoding.encodeList id [countWord p, m89_fp_plan_word L]) (encodeFpFactorBlocks B)
      (mainSpaceBound kit.enumC (bitLen p)) (mainSpaceBound kit.enumC (bitLen p))) :
    (fb B).totalCoords ≤ headSize (kitCost kit) (bitLen p) := by
  let enc := fun a : (ZMod p)ˣ => countWord (a : ZMod p).val
  have seq (xs : List (List (ZMod p)ˣ)) :
      (xs.map List.length).sum ≤ (Encoding.encodeList (Encoding.encodeList enc) xs).length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := w3_encodedCount enc x
      simp only [List.map_cons, List.sum_cons, encodedCons]
      omega
  have htotal : (fb B).totalBaseSize ≤ (encodeFpFactorBlocks B).length := by
    simpa [fb, w3_fpFB, IndexedFactorBase.totalBaseSize, encodeFpFactorBlocks,
      List.ofFn_eq_map, List.map_map, Function.comp_def, Fin.sum_univ_def, enc] using seq (List.ofFn B)
  have out := outputSpace hr
  have he := Nat.floor_mono (stage1_complexity_dominance.1 kit.enumC (kitCost kit) (bitLen p)
    (by unfold kitCost; omega)).1
  change (fb B).totalBaseSize+2 ≤ _
  unfold headSize
  omega

theorem polyMono {k j n m : ℕ} (hk : k ≤ j) (hn : n ≤ m) : polyBound k n ≤ polyBound j m := by
  apply (stage1_complexity_dominance.1 k j n hk).2.trans
  unfold polyBound
  gcongr

theorem oracleLe {en de : Port} (kit : Kit en de) {p N : ℕ}
    (hn : N ≤ headSize (kitCost kit) (bitLen p)) :
    let b := bitLen p
    let v := headOracle (kitCost kit) b
    mainSpaceBound kit.prepC b ≤ v ∧ polyBound kit.prepC b ≤ v ∧
    mainSpaceBound kit.enumC b ≤ v ∧ mainSpaceBound kit.decC b ≤ v ∧
    polyBound kit.decC b ≤ v ∧ polyBound kit.updateC (N+bitLen (p-1)) ≤ v := by
  intro b v
  let k := kitCost kit
  have h (j : ℕ) (hj : j ≤ k) : mainSpaceBound j b ≤ v :=
    ((stage1_complexity_dominance.1 j k b hj).1).trans (le_add_of_nonneg_right (by unfold polyBound; positivity))
  have hp (j n : ℕ) (hj : j ≤ k) (hsize : n ≤ headSize k b+b+1) : polyBound j n ≤ v :=
    (polyMono hj hsize).trans (le_add_of_nonneg_left (by unfold mainSpaceBound; positivity))
  have hm : bitLen (p-1) ≤ b := Nat.clog_mono_right 2 (Nat.sub_le p 1)
  change N ≤ headSize k b at hn
  refine ⟨h _ ?_, hp _ _ ?_ (by omega), h _ ?_, h _ ?_, hp _ _ ?_ (by omega), hp _ _ ?_ (by omega)⟩ <;>
    dsimp [k,kitCost] <;> omega

theorem preparedState {p : ℕ} [Fact p.Prime] (t : ℕ) (seed : FpSeed p (m p)) (g a : (ZMod p)ˣ) :
    next (g : ZMod p).val (a : ZMod p).val (some (t,seed)) =
      ⟨3,p,(g : ZMod p).val,(a : ZMod p).val,t,0,0,m89_fp_plan_word (some (t,seed)),[],[],[],[]⟩ := by
  simp [next, prepared, FpLargeEntry.saved, start, prepAnswer, second, m89_fp_plan_word, encodeFpDLPInput]

theorem startState {p : ℕ} [Fact p.Prime] (g a : (ZMod p)ˣ) :
    start 2 (input g a) = ⟨2,p,(g : ZMod p).val,(a : ZMod p).val,0,0,0,[],[],[],[],[]⟩ := by
  simp [start, input, encodeFpDLPInput]

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpDriverAssembly
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpStep FpTraceStep FpBaseCert FpLargeEntry FpCoordinateWidths FpNativeQuery
open NineOracleLoop BlockLookup DetDLP_W1_Queries

structure EntrySizes {p : ℕ} [Fact p.Prime] (g a : (ZMod p)ˣ) (L : Plan p)
    (B : FpOracles.Blocks p) (n : ℕ) : Prop where
  input : (pairWord (FpOracles.input g a) []).length ≤ n
  prepare : (pairWord (FpLargeEntry.saved p (g : ZMod p).val (a : ZMod p).val) (tag9 1 (countWord p))).length ≤ n
  plan : (prepAnswer L).length ≤ n
  prepared : (pairWord (FpLargeEntry.saved p (g : ZMod p).val (a : ZMod p).val) (prepAnswer L)).length ≤ n
  enumerate : (pairWord (packState (next (g : ZMod p).val (a : ZMod p).val L)) (tag9 2 (prepAnswer L))).length ≤ n
  blocks : (encodeFpFactorBlocks B).length ≤ n
  enumerated : (pairWord (packState (next (g : ZMod p).val (a : ZMod p).val L)) (encodeFpFactorBlocks B)).length ≤ n
  generator : let s := firstCoordinateState g a L B
    (pairWord (packState s) (tag9 8 (queryInput 8 s))).length ≤ n

private theorem storedPack {s : FpState} {d : ℕ} (h : Stored d s)
    (hk : (countWord s.phase).length ≤ d) (hi : (countWord s.idx).length ≤ d) :
    (packState s).length ≤ listCap 12 d := by
  have hh := h.header
  change ∀ u ∈ [countWord s.p,countWord s.g,countWord s.a,countWord s.T,countWord s.fuel,
    s.planWord,s.blocksWord], u.length ≤ d at hh
  apply packedLe
  intro w hw
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact hk | exact hi | exact h.rep | exact h.pkt | exact h.pre | exact hh _ (by simp)

private theorem updateWordFields (M N : ℕ) (x : Word) (row : List ℕ) (rhs : ℕ) :
    NewtonPoly.updateWord M N x row rhs =
      Encoding.encodeList id [countWord M,countWord N,x,encodeNatListBin row,countWord rhs] := by
  change true :: (frame _ ++ true :: (frame _ ++ true :: (frame _ ++ true :: (frame _ ++ true :: (frame _ ++ [false]))))) = _
  simp only [frame_correct, Encoding.encodeList, id_eq]

private theorem pairAt {d C : ℕ} {s a : Word} (hC : 16*(cycleCap d+1) ≤ C)
    (hs : s.length ≤ listCap 12 d) (ha : a.length ≤ 10*d+15) : (pairWord s a).length ≤ C := by
  rw [pairLength]
  unfold cycleCap at hC
  omega

set_option maxHeartbeats 400000 in
theorem entrySizes {p : ℕ} [Fact p.Prime] [NeZero (p-1)] (g a : (ZMod p)ˣ)
    (large : w3_large p (p-1)) (seed : FpSeed p (m p)) (B : FpOracles.Blocks p)
    (ok : m89_fp_plan_ok (some (threshold p,seed))) (k : ℕ)
    (hN : (fb B).totalCoords ≤ headSize k (bitLen p)) :
    EntrySizes g a (some (threshold p,seed)) B (headCap k (bitLen p)) := by
  let T := threshold p
  let L : Plan p := some (T,seed)
  let I := (FpOracles.input g a).length
  let N := (fb B).totalCoords
  let d := fieldLimit (bitLen p) (bitLen (p-1)) (m p) N I
  let w := FpOracles.input g a
  let v := next (g : ZMod p).val (a : ZMod p).val L
  let s := firstCoordinateState g a L B
  let b := encodeFpFactorBlocks B
  let xs := FpTraceStep.coords (decodeBlocks b)
  let raw := xs.map fun j => if j = (decodeBlocks b).flatten.length then (1 : ℤ) else 0
  have prov := preparedState T seed g a
  have hpp : v.p = p := congrArg FpState.p prov
  have hl := planLe L ok
  have hb := blocksLe B
  have cwp := S8G.FpMoment.binaryLen (le_refl p)
  have cwg := S8G.FpMoment.binaryLen (g : ZMod p).val_lt.le
  have cwa := S8G.FpMoment.binaryLen (a : ZMod p).val_lt.le
  have cwt := S8G.FpMoment.binaryLen (m89_decode.threshold_le (show 2 ≤ m p from le_max_left ..) ok.1 ok.2.1)
  change (countWord T).length ≤ bitLen p+1 at cwt
  have cp : (countWord p).length ≤ d := by dsimp only [d,fieldLimit]; omega
  have plan : (m89_fp_plan_word L).length ≤ d := by dsimp only [d,fieldLimit]; omega
  have blocks : b.length ≤ d := by change _ ≤ _ at hb; dsimp only [b,d,fieldLimit,N]; omega
  have input : w.length ≤ d := by dsimp only [d,fieldLimit,I,w]; omega
  have wide : N+8 ≤ d := by dsimp only [d,fieldLimit]; omega
  have hd : bitLen p+1 ≤ d := by dsimp only [d,fieldLimit]; omega
  have zero : (countWord 0).length ≤ d := (w3_queryIndexLength 0).trans (by omega)
  have two : (countWord 2).length ≤ d := (w3_queryIndexLength 2).trans (by omega)
  have three : (countWord 3).length ≤ d := (w3_queryIndexLength 3).trans (by omega)
  have readyLen : (packState v).length ≤ listCap 12 d := by
    apply packedLe
    intro u hu
    change u ∈ fields (next _ _ (some (T,seed))) at hu
    rw [prov] at hu
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact plan | exact cp | exact cwg.trans hd | exact cwa.trans hd | exact cwt.trans hd
            | exact three | exact zero | exact Nat.zero_le _
  have saveLen : (FpLargeEntry.saved p (g : ZMod p).val (a : ZMod p).val).length ≤ listCap 12 d := by
    apply packedLe
    intro u hu
    change u ∈ fields (start 2 (FpOracles.input g a)) at hu
    rw [startState] at hu
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact cp | exact cwg.trans hd | exact cwa.trans hd | exact two
            | exact zero | exact Nat.zero_le _
  have prep : (prepAnswer L).length ≤ 4*d+5 := by
    simp only [prepAnswer, encodedCons,encodedNil,id_eq]
    omega
  have H := firstCoordinateStored B L large ok g a
  change Stored d s at H
  have packed := storedPack H
    (show (countWord 4).length ≤ d from (w3_queryIndexLength 4).trans (by omega))
    (show (countWord 0).length ≤ d from (w3_queryIndexLength 0).trans (by omega))
  have sm : s.p = p := by simpa only [s,firstCoordinateState,nextState,unpackState_packState] using hpp
  have sb : s.blocksWord = b := rfl
  have sp : s.pktWord = rowPkt (p-1) 1 raw := by
    change rowPkt (v.p-1) 1 raw = _
    rw [hpp]
  have dim : (decodeBlocks b).flatten.length+2=N := by
    change (decodeBlocks (encodeFpFactorBlocks B)).flatten.length+2=(fb B).totalCoords
    rw [sizeBlocks]; rfl
  have q8 : queryInput 8 s = NewtonPoly.updateWord (p-1) N s.repWord (raw.map (residue (p-1))) 1 := by
    change NewtonPoly.updateWord (s.p-1)
      ((decodeBlocks s.blocksWord).flatten ++ [countWord s.g, countWord s.a]).length s.repWord
      (w5_M6Sort.decode (first s.pktWord)) (Groundwork.PolyT.bval (second s.pktWord)) = _
    rw [sm,sb,sp]
    have dim' : ((decodeBlocks b).map List.length).sum + 2 = N := by simpa using dim
    simp [rowPkt, second, dim']
  have rowlen : (encodeNatListBin (raw.map (residue (p-1)))).length ≤ d := by
    have hh := w3_encodedMemberLength (enc:=id) (xs:=[encodeNatListBin (raw.map (residue (p-1))),countWord 1]) List.mem_cons_self
    change (encodeNatListBin (raw.map (residue (p-1)))).length+1 ≤ (rowPkt (p-1) 1 raw).length at hh
    rw [← sp] at hh
    exact (Nat.le_add_right ..).trans (hh.trans H.pkt)
  have qm := S8G.FpMoment.binaryLen (Nat.sub_le p 1)
  have qn := w3_queryIndexLength N
  have h8 : (queryInput 8 s).length ≤ 10*d+11 := by
    rw [q8,updateWordFields]
    simp only [encodedCons,encodedNil,id_eq,show (countWord 1).length=1 from rfl]
    have hrep := H.rep
    have hm' : bitLen p+1 ≤ d := by dsimp only [d,fieldLimit]; omega
    omega
  have cap := publicCap k g a N hN
  change 16*(cycleCap d+1) ≤ headCap k (bitLen p) at cap
  have tag1 (x : Word) : (tag9 1 x).length=x.length+3 := rfl
  have tag2 (x : Word) : (tag9 2 x).length=x.length+3 := rfl
  have dd : d ≤ listCap 12 d := by unfold listCap; omega
  have single : 10*d+15 ≤ headCap k (bitLen p) := by unfold cycleCap at cap; omega
  refine ⟨pairAt cap (input.trans dd) (by change 0 ≤ _; omega),
    pairAt cap saveLen ?_, ?_, pairAt cap saveLen ?_, pairAt cap readyLen ?_, ?_,
    pairAt cap readyLen ?_, pairAt cap packed ?_⟩
  · rw [tag1]; omega
  · exact (show (prepAnswer L).length ≤ 10*d+15 by omega).trans single
  · change (prepAnswer L).length ≤ _; omega
  · change (tag9 2 (prepAnswer L)).length ≤ _
    rw [tag2]; omega
  · exact blocks.trans ((show d ≤ 10*d+15 by omega).trans single)
  · change b.length ≤ _; omega
  · change (tag9 8 (queryInput 8 s)).length ≤ _
    rw [tag8Length]; omega

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpDriverAssembly

open FpOracles FpBaseCert

section Labels
variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m) (M : ℕ) [NeZero M]

private theorem w3_sum_slots (X : FB.BlockTuple) (v : Fin FB.totalCoords → ℤ) :
    (∑ j, (FB.tupleCnt X j : ℤ) * v j) = ∑ i, ∑ k, v (FB.coordOf i (X i k)) := by
  classical
  simp only [IndexedFactorBase.tupleCnt, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
  simp [ite_mul]

private theorem w3_label_cast (y : w3_Label M FB.totalCoords) (X : FB.BlockTuple) :
    ((FB.tupleLabelSum M y X : ℤ) : ZMod M) = ∑ i, (FB.tupleCnt X i : ZMod M) * y i := by
  simp [IndexedFactorBase.tupleLabelSum]

private theorem w3_row_eq (y : w3_Label M FB.totalCoords) (X Y : FB.BlockTuple) :
    w3_holds (w3_shiftRow FB M X Y) y ↔ ((w3_delta FB M y X Y : ℤ) : ZMod M) = 1 := by
  simp only [w3_holds,w3_shiftRow,sub_mul,Finset.sum_sub_distrib,w3_delta,Int.cast_sub,w3_label_cast]

private theorem w3_flat_slot {n : ℕ} (F : Fin n → List G) (i : Fin n) (r : Fin (F i).length) :
    ((List.finRange n).flatMap F)[(∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (F j).length) + r.val]? = some ((F i).get r) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i r
    · intro s; simp [List.finRange_succ,List.flatMap_cons,List.getElem?_append,s.isLt]
    · intro s
      have hsum : (∑ t ∈ Finset.univ.filter (fun t : Fin (n+1) => t < j.succ), (F t).length) =
          (F 0).length + ∑ t ∈ Finset.univ.filter (fun t : Fin n => t < j), (F t.succ).length := by
        simp only [Finset.sum_filter,Fin.sum_univ_succ,Fin.succ_pos,if_true,Fin.succ_lt_succ_iff]
      simpa [List.finRange_succ,List.flatMap_cons,List.flatMap_map,hsum,Nat.add_assoc,
        List.getElem?_append,Function.comp_def] using ih (fun t => F t.succ) j s

private theorem w3_elem_slot (P Q : G) (i : Fin m) (r : Fin (FB.blocks i).length) :
    FB.elem P Q (FB.coordOf i r) = (FB.blocks i).get r := by
  have h := FB.blockOffset_add_lt i r
  have hlen : FB.blockOffset i + r.val < ((List.finRange m).flatMap FB.blocks).length := by
    rw [List.length_flatMap, ← Fin.sum_univ_def]; exact h
  have he := w3_flat_slot FB.blocks i r
  change ((List.finRange m).flatMap FB.blocks)[FB.blockOffset i + r.val]? = some _ at he
  rw [List.getElem?_eq_getElem hlen] at he
  unfold IndexedFactorBase.elem
  rw [dif_pos (show (FB.coordOf i r).val < FB.totalBaseSize from h)]
  exact Option.some.inj he

end Labels

theorem nativeLabels {p : ℕ} [Fact p.Prime] [NeZero (p-1)] (g a : (ZMod p)ˣ)
    (gen : orderOf g = p-1) (B : Blocks p) :
    ∃ z : w3_Label (p-1) (fb B).totalCoords,
      z (fb B).genCoord = 1 ∧
      (∀ j T, (fb B).tupleVal T = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j →
        w3_holds ((fun i => w3_unitRow (fb B) (p-1) j i -
          ((fb B).tupleCnt T i : ZMod (p-1))), 0) z) ∧
      w3_pass (fb B) (p-1) (Additive.ofMul g) z ∧
      ∀ j, (z j).val • Additive.ofMul g = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j := by
  classical
  let P := Additive.ofMul g
  let Q := Additive.ofMul a
  let FB := fb B
  have card : Nat.card (Additive (ZMod p)ˣ) = p-1 := by
    change Nat.card (ZMod p)ˣ = p-1
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hg : addOrderOf P=p-1 := (addOrderOf_ofMul_eq_orderOf g).trans gen
  have ht : AddSubgroup.zmultiples P = ⊤ := (AddSubgroup.zmultiples P).eq_top_of_card_eq
    ((Nat.card_zmultiples P).trans (hg.trans card.symm))
  have all (x : Additive (ZMod p)ˣ) : x ∈ AddSubgroup.zmultiples P := by rw [ht]; trivial
  let e := (zmodAddEquivOfGenerator all card).symm
  have hP : e P = 1 := zmodAddEquivOfGenerator_symm_apply_generator all card
  let z : w3_Label (p-1) FB.totalCoords := fun j => e (FB.elem P Q j)
  have hsum (X : FB.BlockTuple) : ((FB.tupleLabelSum (p-1) z X : ℤ) : ZMod (p-1)) = e (FB.tupleVal X) := by
    unfold IndexedFactorBase.tupleLabelSum
    rw [w3_sum_slots]
    push_cast
    simp [IndexedFactorBase.tupleVal, Fin.sum_univ_two, z, w3_elem_slot]
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · change e (FB.elem P Q FB.genCoord) = 1
    simpa [IndexedFactorBase.elem, IndexedFactorBase.genCoord] using hP
  · intro j X hX
    have h := hsum X
    rw [w3_label_cast] at h
    change FB.tupleVal X = FB.elem P Q j at hX
    rw [hX] at h
    simpa [w3_holds, w3_unitRow, sub_mul, Finset.sum_sub_distrib, ite_mul, sub_eq_zero] using h.symm
  · change w3_pass FB (p-1) P z
    intro X Y hgxy
    rw [w3_row_eq]
    change FB.tupleVal Y = FB.tupleVal X + P at hgxy
    simp [w3_delta, hsum, hgxy, map_add, hP]
  · intro j
    change (z j).val • P = FB.elem P Q j
    apply e.injective
    simp [z,hP,nsmul_eq_mul]

theorem nativeCover {p : ℕ} [Fact p.Prime] (large : w3_large p (p-1)) (B : Blocks p)
    (L : Plan p) (ok : m89_fp_plan_ok L)
    (hB : ∀ i, (B i).Nodup ∧ (B i).toFinset = m89_fp_plan_block L i) :
    Function.Surjective (fb B).tupleVal := by
  classical
  intro x
  obtain ⟨A,D,mem,prod⟩ := FpTraceBounds.planCover large L ok x.toMul
  have idx (i : Fin (m p)) (v : (ZMod p)ˣ) (hv : v ∈ m89_fp_plan_block L i) :
      ∃ k : Fin ((fb B).blocks i).length, ((fb B).blocks i).get k = Additive.ofMul v := by
    apply List.mem_iff_get.mp
    exact List.mem_map.mpr ⟨v, List.mem_toFinset.mp ((hB i).2.symm ▸ hv), rfl⟩
  choose kA hkA using fun i => idx i (A i) (mem i).1
  choose kD hkD using fun i => idx i (D i) (mem i).2
  refine ⟨fun i => ![kA i,kD i], ?_⟩
  simp only [IndexedFactorBase.tupleVal,Matrix.cons_val_zero,Matrix.cons_val_one,
    hkA,hkD,← ofMul_mul,← ofMul_prod]
  exact congrArg Additive.ofMul prod

theorem readTerminal {p : ℕ} [Fact p.Prime] [NeZero (p-1)] (large : w3_large p (p-1))
    (g a : (ZMod p)ˣ) (gen : orderOf g=p-1) (B : Blocks p)
    (cover : Function.Surjective (fb B).tupleVal) (z y : w3_Label (p-1) (fb B).totalCoords)
    (trueLabel : ∀ j, (z j).val • Additive.ofMul g = (fb B).elem (Additive.ofMul g) (Additive.ofMul a) j)
    (hy : y (fb B).genCoord=1)
    (rows : ∀ j, ∃ X, (fb B).tupleVal X=(fb B).elem (Additive.ofMul g) (Additive.ofMul a) j ∧
      w3_holds ((fun i => w3_unitRow (fb B) (p-1) j i - ((fb B).tupleCnt X i : ZMod (p-1))),0) y)
    (pass : w3_pass (fb B) (p-1) (Additive.ofMul g) y) :
    (y (fb B).targetCoord).val < p-1 ∧ g^(y (fb B).targetCoord).val=a := by
  classical
  let FB := fb B
  let P := Additive.ofMul g
  let Q := Additive.ofMul a
  choose U hU hrow using rows
  have hinit : FB.SatisfiesInitialCongruences (p-1) U y := by
    refine ⟨hy, fun j => ?_⟩
    rw [w3_label_cast]
    simpa [w3_holds,w3_unitRow,sub_mul,Finset.sum_sub_distrib,ite_mul,sub_eq_zero] using hrow j
  have hc : Fintype.card (Additive (ZMod p)ˣ) = p-1 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (ZMod p)ˣ = p-1
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have eq := proposition_4_1_fixed_shift_soundness (p-1)
    (by have := large.2.1; omega) hc
    P Q ((addOrderOf_ofMul_eq_orderOf g).trans gen) FB cover U hU z trueLabel y hinit
    (fun X Y h => (w3_row_eq FB (p-1) y X Y).mp (pass X Y h))
  refine ⟨(y FB.targetCoord).val_lt, ?_⟩
  rw [eq FB.targetCoord]
  change (z FB.targetCoord).val • P = Q
  have ht := trueLabel FB.targetCoord
  change (z FB.targetCoord).val • P = FB.elem P Q FB.targetCoord at ht
  simpa [IndexedFactorBase.elem,IndexedFactorBase.targetCoord] using ht

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTupleReadback

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem read_pair {G : Type} {m : ℕ} (FB : IndexedFactorBase G m)
    (b : ℕ) (hb : 0 < b) (value : G → ℕ) (fits : ∀ g, value g < 2 ^ b)
    (X Y : FB.BlockTuple) :
    let enc := fun g => countWord (value g)
    let v := FpTraceStep.tupleWords b (w3_tupleWord FB (fun g => w3_bits b (value g)) X Y)
    v.take (2 * m) = BlockLookup.words FB enc X ∧
      v.drop (2 * m) = BlockLookup.words FB enc Y := by
  let entries (T : FB.BlockTuple) := (List.finRange m).flatMap fun i =>
    [(FB.blocks i).get (T i 0), (FB.blocks i).get (T i 1)]
  let enc := fun g => countWord (value g)
  have hw (T : FB.BlockTuple) :
      (entries T).map enc = BlockLookup.words FB enc T := by
    simp [entries, BlockLookup.words, List.map_flatMap]
  have hlen : (BlockLookup.words FB enc X).length = 2 * m := by
    rw [← hw X, List.length_map]
    simp [entries, List.length_flatMap, Nat.mul_comm]
  have hcode : w3_tupleWord FB (fun g => w3_bits b (value g)) X Y =
      ((entries X ++ entries Y).map value).flatMap (w3_bits b) := by
    rw [List.flatMap_map]
    simp [w3_tupleWord, entries, List.flatMap_assoc, show List.finRange 2 = [0, 1] from rfl]
  have hfits : ∀ n ∈ (entries X ++ entries Y).map value, n < 2 ^ b := by
    intro n hn
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hn
    exact fits g
  have hr : FpTraceStep.tupleWords b (w3_tupleWord FB (fun g => w3_bits b (value g)) X Y) =
      BlockLookup.words FB enc X ++ BlockLookup.words FB enc Y := by
    rw [hcode, FpTraceStep.tupleWords_correct b hb _ hfits, List.map_map, List.map_append]
    exact congrArg₂ List.append (hw X) (hw Y)
  dsimp only
  rw [hr]
  exact ⟨List.take_left' hlen, List.drop_left' hlen⟩

theorem nativeTuples {p m : ℕ} [hp : Fact p.Prime] (B : Fin m → List (ZMod p)ˣ)
    (X Y : (w3_fpFB B).BlockTuple) :
    let val := fun x : Additive (ZMod p)ˣ => (x.toMul : ZMod p).val
    let enc := fun x => countWord (val x)
    let v := FpTraceStep.tupleWords (S8G.FpMoment.Code.width p)
      (w3_tupleWord (w3_fpFB B) (fun x => w3_bits (bitLen p) (val x)) X Y)
    v.take (2 * m) = BlockLookup.words (w3_fpFB B) enc X ∧
      v.drop (2 * m) = BlockLookup.words (w3_fpFB B) enc Y := by
  rw [S8G.FpMoment.Code.width_eq]
  exact read_pair (w3_fpFB B) (bitLen p) (Nat.clog_pos (by decide) hp.out.one_lt)
    (fun x => (x.toMul : ZMod p).val)
    (fun x => (x.toMul : ZMod p).val_lt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) p)) X Y

end DetDLP.W3C.FpTupleReadback
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpNativeQuery

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Queries FpOracles FpBaseCert BlockLookup

private theorem pairs_injective {α β : Type} {xs : List α} {f g : α → Fin 2 → β}
    (h : (xs.flatMap fun i => [f i 0, f i 1]) = xs.flatMap fun i => [g i 0, g i 1]) :
    ∀ i ∈ xs, ∀ j, f i j = g i j := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    intro i hi j
    rcases List.mem_cons.mp hi with rfl | hmem
    · fin_cases j <;> first | exact h.1 | exact h.2.1
    · exact ih h.2.2 i hmem j

private theorem enc_injective {p : ℕ} [Fact p.Prime] : Function.Injective (enc (p := p)) := by
  intro x y h
  change x.toMul = y.toMul
  apply Units.ext
  apply ZMod.val_injective
  exact (decode_count _).symm.trans ((congrArg Groundwork.PolyT.bval h).trans (decode_count _))

private theorem tuple_injective {p : ℕ} [Fact p.Prime] (B : FpOracles.Blocks p)
    (nd : ∀ i, ((fb B).blocks i).Nodup) :
    Function.Injective (Function.uncurry (w3_tupleWord (fb B)
      (fun A => w3_bits (bitLen p) (A.toMul : ZMod p).val))) := by
  have wi {X Y : (fb B).BlockTuple} (h : words (fb B) enc X = words (fb B) enc Y) : X = Y := by
    funext i j
    apply (nd i).injective_get
    apply enc_injective
    exact pairs_injective (f := fun i j => enc (((fb B).blocks i).get (X i j)))
      (g := fun i j => enc (((fb B).blocks i).get (Y i j))) h i (List.mem_finRange i) j
  let decode (u : List Bool) :=
    let vs := FpTraceStep.tupleWords (S8G.FpMoment.Code.width p) u
    (vs.take (2 * m p), vs.drop (2 * m p))
  have read (X Y : (fb B).BlockTuple) :
      decode (w3_tupleWord (fb B) (fun A => w3_bits (bitLen p) (A.toMul : ZMod p).val) X Y) =
        (words (fb B) enc X, words (fb B) enc Y) :=
    Prod.ext (FpTupleReadback.nativeTuples B X Y).1 (FpTupleReadback.nativeTuples B X Y).2
  rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
  have hh := (read X Y).symm.trans ((congrArg decode h).trans (read X' Y'))
  exact Prod.ext (wi (congrArg Prod.fst hh)) (wi (congrArg Prod.snd hh))

theorem nativeWires {p : ℕ} [Fact p.Prime] [NeZero (p-1)] (large : w3_large p (p-1))
    (seed : FpSeed p (m p)) (B : FpOracles.Blocks p) (g a : (ZMod p)ˣ)
    (hB : ∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (threshold p) seed i)
    (s : FpStep.FpState) (hs : Ready B (some (threshold p, seed)) g a s)
    (hT : s.T = threshold p) (y : w3_Label (p-1) (fb B).totalCoords) (pre : List Bool) :
    FpCutExec.Wires (nativeQuery seed B g y pre) s (4 * m p * bitLen p) enc := by
  have nd (i) : ((fb B).blocks i).Nodup :=
    (hB i).1.map (f := Additive.ofMul) (fun _ _ h => h)
  have blocksLen : (decodeBlocks s.blocksWord).length = m p := by
    rw [hs.blocks, FpTraceStep.native_blocks, List.length_ofFn]
  refine {
    modulus := congrArg (· - 1) hs.prime
    dimension := ?_
    blocks := hs.blocks ▸ wireBlocks B
    length := ?_
    width := ?_
    injective := tuple_injective B nd
    distinct := fun i => (nd i).map enc_injective
    valid := nativeQueryValid large seed B g hB s hs.prime hs.gen hT hs.plan hs.blocks y pre
    tuples := ?_ }
  · change (decodeBlocks s.blocksWord).flatten.length + 2 = (fb B).totalCoords
    rw [hs.blocks, sizeBlocks]
    rfl
  · rw [blocksLen, hs.prime, S8G.FpMoment.Code.width_eq]
  · intro X Y
    change (w3_tupleWord (fb B) (fun A => w3_bits (bitLen p) (A.toMul : ZMod p).val) X Y).length = _
    simp [w3_tupleWord, List.length_flatMap, w3_bits]
    change 2 * (m p * (bitLen p + bitLen p)) = 4 * m p * bitLen p
    ring
  · intro X Y
    dsimp only
    rw [blocksLen, hs.prime]
    exact FpTupleReadback.nativeTuples B X Y

end DetDLP.W3C.FpNativeQuery
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpDriverAssembly
open FpOracles FpStep FpBaseCert FpLargeEntry FpCoordinateWidths FpNativeQuery NineOracleLoop
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def CutTailAt {en de : Port} (kit : Kit en de) (J : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero (p-1)], w3_large p (p-1) →
    ∀ (seed : FpSeed p (m p)) (B : FpOracles.Blocks p),
    (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (threshold p) seed i) →
    (fb B).totalCoords ≤ headSize (kitCost kit) (bitLen p) →
    ∀ (g a : (ZMod p)ˣ) (e : FpState) (r : w3_Rep (p-1) (fb B).totalCoords)
      (z : w3_Label (p-1) (fb B).totalCoords),
    Ready B (some (threshold p,seed)) g a e → e.idx=(fb B).totalCoords → e.T=threshold p →
    Stored (fieldLimit (bitLen p) (bitLen (p-1)) (m p) (fb B).totalCoords (input g a).length) e →
    Stage2Trace.Invariant z r → w3_pass (fb B) (p-1) (Additive.ofMul g) z →
    ∃ (y : w3_Label (p-1) (fb B).totalCoords) (rounds cap : ℕ) (t σ : ℝ),
      y ∈ w3_coset r ∧ w3_pass (fb B) (p-1) (Additive.ofMul g) y ∧
      1 ≤ rounds ∧ 0 ≤ t ∧ 0 ≤ σ ∧
      LoopRuns stepFn (calls kit t σ) rounds (packState e) (repWord r) (countWord (y (fb B).targetCoord).val) cap ∧
      (rounds : ℝ) ≤ mainSpaceBound J (bitLen p) ∧ (cap : ℝ) ≤ mainSpaceBound J (bitLen p) ∧
      t ≤ mainTimeBound J (bitLen p) ∧ σ ≤ mainSpaceBound J (bitLen p)

def CutTail {en de : Port} (kit : Kit en de) : Prop := ∃ J, CutTailAt kit J

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpLargeTrace

open FpOracles FpStep FpLargeEntry NineOracleLoop
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem enlargeChain {R R' : Word → Word → Prop} {c C k : ℕ}
    {s e : FpState} {a y : Word} (ch : FpDecompLoop.Chain R c k s a e y)
    (hr : ∀ {q z}, R q z → R' q z) (hc : c ≤ C) :
    FpDecompLoop.Chain R' C k s a e y := by
  induction ch with
  | done => exact .done
  | step one _ ih =>
    exact .step { one with
      b0 := one.b0.trans hc, b1 := one.b1.trans hc, b2 := one.b2.trans hc,
      b3 := one.b3.trans hc, b4 := one.b4.trans hc, b5 := one.b5.trans hc,
      firstCall := hr one.firstCall, secondCall := hr one.secondCall } ih

theorem prependChainBounded {en de : Port} (kit : Kit en de)
    {tc sc tt st T S : ℝ} {cc ct C k n : ℕ} {s e : FpState} {a y o : Word}
    (ch : FpDecompLoop.Chain (calls kit tc sc) cc k s a e y)
    (tail : LoopRuns stepFn (calls kit tt st) n (packState e) y o ct)
    (hTc : tc ≤ T) (hSc : sc ≤ S) (hCc : cc ≤ C)
    (hTt : tt ≤ T) (hSt : st ≤ S) (hCt : ct ≤ C) :
    LoopRuns stepFn (calls kit T S) (n+2*k) (packState s) a o C := by
  apply FpDecompLoop.chain_trace (enlargeChain ch (R' := calls kit T S) ?_ hCc)
    (FpCutExec.enlarge kit hTt hSt hCt tail)
  rintro _ _ ⟨j, x, hw, run⟩
  exact ⟨j, x, hw, MachineComposition.runsWithin_mono run hTc hSc⟩

end DetDLP.W3C.FpLargeTrace
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpDriverAssembly
open FpOracles FpLargeEntry FpDriverFromCounts NineOracleLoop DetDLP_W1_Bounds
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def CompletedAt {en de : Port} (kit : Kit en de) (J p : ℕ) [Fact p.Prime] (g a : (ZMod p)ˣ) : Prop :=
  let b := bitLen p
  ∃ (u r cap : ℕ) (t σ : ℝ), u < p-1 ∧ g^u=a ∧ 1 ≤ r ∧ 0 ≤ t ∧ 0 ≤ σ ∧
    LoopRuns stepFn (calls kit t σ) r (input g a) [] (countWord u) cap ∧
    (r : ℝ) ≤ mainSpaceBound J b+mainSpaceBound J b ∧ (cap : ℝ) ≤ mainSpaceBound J b ∧
    t ≤ mainTimeBound J b ∧ σ ≤ mainSpaceBound J b

theorem timeMono {c C b : ℕ} (h : c ≤ C) : mainTimeBound c b ≤ mainTimeBound C b := by
  rw [← tEq, ← tEq]
  exact monoE (by unfold tScale; positivity) h

theorem spaceMono {c C b : ℕ} (h : c ≤ C) : mainSpaceBound c b ≤ mainSpaceBound C b := by
  rw [← sEq, ← sEq]
  exact monoE (div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans (le_max_left ..)) _)) h

private structure LargeInput where
  p : ℕ
  prime : Fact p.Prime
  g : (ZMod p)ˣ
  a : (ZMod p)ˣ
  generator : orderOf g=p-1
  large : w3_large p (p-1)
attribute [instance] LargeInput.prime

private theorem traceAtMono {en de : Port} {kit : Kit en de} {c C C' p : ℕ}
    [Fact p.Prime] {g a : (ZMod p)ˣ} (h : C ≤ C') (tr : TraceAt kit c C p g a) :
    TraceAt kit c C' p g a := by
  obtain ⟨u,r,n,t,σ,hu,he,hr,ht,hs,run,bt,bs⟩ := tr
  exact ⟨u,r,n,t,σ,hu,he,hr,ht,hs,run,bt.trans (timeMono h),bs.trans (spaceMono h)⟩

theorem closeBranches {en de : Port} (kit : Kit en de) (K J : ℕ)
    (largeRun : ∀ p [Fact p.Prime] (g a : (ZMod p)ˣ), orderOf g=p-1 → w3_large p (p-1) →
      CompletedAt kit J p g a) : TraceBounds kit K := by
  classical
  intro c _
  have traces (i : LargeInput) := largeRun i.p i.g i.a i.generator i.large
  choose u r n t σ hu he hr ht hs run br bc bt bs using traces
  let b (i : LargeInput) := bitLen i.p
  have hb (i : LargeInput) : 1 ≤ b i := Nat.clog_pos (by decide) i.prime.out.one_lt
  have hS (i : LargeInput) := scales_one (hb i)
  have sm : Dom (fun i => sScale (b i)) (fun i => mainSpaceBound J (b i)) :=
    ⟨J,fun i => (sEq (b i) J).ge⟩
  have tm : Dom (fun i => tScale (b i)) (fun i => mainTimeBound J (b i)) :=
    ⟨J,fun i => (tEq (b i) J).ge⟩
  obtain ⟨C, costs⟩ := FpTraceBounds.closeCosts b hb c r n t σ ht hs
    ((Dom.add hS sm sm).weaken br) (sm.weaken bc) (tm.weaken bt) (sm.weaken bs)
  obtain ⟨S,small⟩ := FpTraceBounds.small kit c
  refine ⟨max S C, ?_⟩
  intro p hp g a gen
  constructor
  · intro guard
    exact traceAtMono (le_max_left ..) (small p g a gen guard)
  · intro guard _ _
    let i : LargeInput := ⟨p,hp,g,a,gen,guard⟩
    apply traceAtMono (le_max_right S C)
    exact ⟨u i,r i,n i,t i,σ i,hu i,he i,hr i,ht i,hs i,run i,costs i⟩

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpDriverAssembly
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpStep FpTraceStep FpBaseCert FpLargeEntry FpCoordinateWidths FpNativeQuery
open NineOracleLoop BlockLookup

private theorem widenCall {en de : Port} (kit : Kit en de) {t σ T S : ℝ} {q y : Word}
    (h : calls kit t σ q y) (ht : t ≤ T) (hs : σ ≤ S) : calls kit T S q y := by
  obtain ⟨j,x,he,run⟩ := h
  exact ⟨j,x,he,MachineComposition.runsWithin_mono run ht hs⟩

theorem assembleLarge {en de : Port} (kit : Kit en de) (J H : ℕ) (tail : CutTailAt kit J)
    (p : ℕ) [hp : Fact p.Prime] (g a : (ZMod p)ˣ) (gen : orderOf g=p-1)
    (large : w3_large p (p-1))
    (headBounds : let k := kitCost kit; let b := bitLen p
      (headRounds k b : ℝ) ≤ mainSpaceBound H b ∧
      (headCap k b : ℝ) ≤ mainSpaceBound H b ∧ headOracle k b ≤ mainSpaceBound H b ∧
      headOracle k b ≤ mainTimeBound H b) : CompletedAt kit (max H J) p g a := by
  classical
  let _ : NeZero (p-1) := ⟨by have := large.2.1; omega⟩
  obtain ⟨L,ok,prep⟩ := kit.prep p
  obtain ⟨B,hB,enumerate⟩ := kit.enumerate p L ok
  obtain ⟨seed,hL⟩ : ∃ seed, L=some (threshold p,seed) := by
    cases L with
    | none =>
      have h : 4096*m p ≤ p-1-1 := large.2.2
      exact False.elim (ok ⟨large.2.1,by omega⟩)
    | some x => obtain ⟨t,S⟩ := x; exact ⟨S,by rw [show t=threshold p from ok.2.2.1]⟩
  subst L
  let L : Plan p := some (threshold p,seed)
  let N := (fb B).totalCoords
  let b := bitLen p
  let k := kitCost kit
  let I := (input g a).length
  let d := fieldLimit b (bitLen (p-1)) (m p) N I
  let v := next (g : ZMod p).val (a : ZMod p).val L
  let blockWord := encodeFpFactorBlocks B
  let s := firstCoordinateState g a L B
  have hv := preparedState (threshold p) seed g a
  change v=_ at hv
  have vp : v.p = p := congrArg FpState.p hv
  have phase : v.phase = 3 := congrArg FpState.phase hv
  have ready : Ready B L g a s := by
    simp only [s,firstCoordinateState,nextState,unpackState_packState]
    change Ready B L g a {v with phase:=4,idx:=0,blocksWord:=_,repWord:=_,pktWord:=_,pre:=[],fuel:=v.fuel}
    rw [hv]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have sT : s.T=threshold p := by
    simpa only [s,firstCoordinateState,nextState,unpackState_packState] using congrArg FpState.T hv
  have dim : (decodeBlocks blockWord).flatten.length+2=N := by
    rw [show (decodeBlocks blockWord).flatten.length = _ from sizeBlocks B]; rfl
  have hN := dimensionOfRun kit L B enumerate
  change N ≤ headSize k b at hN
  have heights := publicCap k g a N hN
  change 16*(cycleCap d+1) ≤ headCap k b at heights
  have hc : cycleCap d ≤ headCap k b := by omega
  have sizes := entrySizes g a large seed B ok k hN
  obtain ⟨z,hgen,consistent,pass,trueLabels⟩ := nativeLabels g a gen B
  obtain ⟨rep,initial,inv,oracle⟩ := FpTraceBounds.initialCall kit v blockWord
    (by have := large.2.1; omega : 2 ≤ p-1) (by rw [vp]) dim (fb B).genCoord (sizeBlocks B).symm z hgen
  have hstored := firstCoordinateStored B L large ok g a
  obtain ⟨e,r,he,idx,inv',eT,sub,rows,endStored,ch⟩ :=
    boundedChain B kit L large ok hB g a z consistent I s ready rep inv N
      (show 0+N=N from Nat.zero_add _) hstored
  obtain ⟨y,n,c,t,σ,ymem,yp,nn,tc,sc,tr,roundLim,capLim,timeLim,spaceLim⟩ :=
    tail p large seed B hB hN g a e r z he idx (eT.trans sT) endStored inv' pass
  have yy := sub ymem
  rw [initial.2] at yy
  have ygen : y (fb B).genCoord=1 := by simpa [w3_holds,ite_mul] using yy.2
  have yrows j := rows j (Nat.zero_le _)
  obtain ⟨hu,heq⟩ := readTerminal large g a gen B (nativeCover large B L ok hB) z y trueLabels ygen
    (fun j => by obtain ⟨X,hX,h⟩ := yrows j; exact ⟨X,hX,h y ymem⟩) yp
  let τ := max (headOracle k b) t
  let spaceBudget := max (headOracle k b) σ
  let cap := max (headCap k b) c
  obtain ⟨hprep,hprep',henum,hdec,hdec',hup⟩ := oracleLe kit hN
  have tim {x : ℝ} (h : x ≤ headOracle k b) : x ≤ τ := h.trans (le_max_left ..)
  have space {x : ℝ} (h : x ≤ headOracle k b) : x ≤ spaceBudget := h.trans (le_max_left ..)
  have length {x : ℕ} (h : x ≤ headCap k b) : x ≤ cap := h.trans (le_max_left ..)
  have joined : LoopRuns stepFn (calls kit τ spaceBudget) (n+2*N) (packState s) (repWord rep)
      (countWord (y (fb B).targetCoord).val) cap :=
    FpLargeTrace.prependChainBounded kit ch tr (tim (max_le hup hdec)) (space (max_le hup hdec'))
      (length hc) (le_max_right ..) (le_max_right ..) (le_max_right ..)
  have repLen : (repWord rep).length ≤ cap := by
    apply length
    have h := representativeLe rep inv.1
    have hr : repCap N (bitLen (p-1)) ≤ d := by dsimp only [d,fieldLimit]; omega
    have hdc : d ≤ cycleCap d := by unfold cycleCap; omega
    exact h.trans (hr.trans (hdc.trans hc))
  have first := FpRowExec.call_round (FpTraceBounds.initialStep v blockWord phase)
    (length sizes.enumerated) (length sizes.generator) repLen (widenCall kit oracle (tim hup) (space hup)) joined
  have second := FpRowExec.call_round (FpLargeEntry.second_call (g : ZMod p).val (a : ZMod p).val L)
    (length sizes.prepared) (length sizes.enumerate) (length sizes.blocks)
    (show calls kit τ spaceBudget (tag9 2 (prepAnswer L)) blockWord from
      ⟨2,_,rfl,MachineComposition.runsWithin_mono enumerate (tim henum) (space henum)⟩) first
  have run := FpRowExec.call_round (FpLargeEntry.first_call p (g : ZMod p).val (a : ZMod p).val large)
    (length sizes.input) (length sizes.prepare) (length sizes.plan)
    (show calls kit τ spaceBudget (tag9 1 (countWord p)) (prepAnswer L) from
      ⟨1,_,rfl,MachineComposition.runsWithin_mono prep (tim hprep) (space hprep')⟩) second
  obtain ⟨hr,hcH,hsH,htH⟩ := headBounds
  have headS := spaceMono (b:=b) (le_max_left H J)
  have tailS := spaceMono (b:=b) (le_max_right H J)
  have headT := timeMono (b:=b) (le_max_left H J)
  have tailT := timeMono (b:=b) (le_max_right H J)
  refine ⟨_,n+2*N+1+1+1,cap,τ,spaceBudget,hu,heq,by omega,tc.trans (le_max_right ..),
    sc.trans (le_max_right ..),run,?_,?_,max_le (htH.trans headT) (timeLim.trans tailT),
    max_le (hsH.trans headS) (spaceLim.trans tailS)⟩
  · have hn : n+2*N+1+1+1 ≤ n+headRounds k b := by dsimp only [headRounds]; omega
    exact (Nat.cast_le.mpr hn).trans (by rw [Nat.cast_add]; exact add_le_add (roundLim.trans tailS) (hr.trans headS))
  · simpa only [cap,Nat.cast_max] using max_le (hcH.trans headS) (capLim.trans tailS)

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpDriverAssembly
open FpCoordinateWidths DetDLP_W1_Bounds

theorem headBudgetsDominated (k : ℕ) : ∃ J : ℕ, ∀ p : ℕ, 2 ≤ p →
    let b := bitLen p
    (headRounds k b : ℝ) ≤ mainSpaceBound J b ∧ (headCap k b : ℝ) ≤ mainSpaceBound J b ∧
    headOracle k b ≤ mainSpaceBound J b ∧ headOracle k b ≤ mainTimeBound J b := by
  let I := {p : ℕ // 2 ≤ p}
  let b (i : I) := bitLen i.val
  let S (i : I) := sScale (b i)
  let D (f : I → ℕ) := Dom S (fun i => (f i : ℝ))
  have hs (i : I) : 1 ≤ S i := scales_one (Nat.clog_pos (by decide) i.property)
  have cn (n : ℕ) : D (fun _ => n) := dconst hs n
  have add {f g : I → ℕ} (hf : D f) (hg : D g) : D (fun i => f i+g i) := by
    simpa only [D, Nat.cast_add] using hf.add hs hg
  have mul {f g : I → ℕ} (hf : D f) (hg : D g) : D (fun i => f i*g i) := by
    simpa only [D, Nat.cast_mul] using hf.mul hg (fun i => Nat.cast_nonneg _) (fun i => Nat.cast_nonneg _)
  have dm : Dom S (fun i => mainSpaceBound k (b i)) := ⟨k,fun _ => (sEq ..).ge⟩
  have nonneg (i : I) : 0 ≤ mainSpaceBound k (b i) := by unfold mainSpaceBound; positivity
  have floorD : D (fun i => ⌊mainSpaceBound k (b i)⌋₊) := dm.weaken (fun i => Nat.floor_le (nonneg i))
  obtain ⟨c,hc⟩ := stage1_complexity_dominance.2.2.1 1 0
  have db : D b := by
    refine ⟨c,fun i => ?_⟩
    change (bitLen i.val : ℝ) ≤ E (sScale _) _
    rw [sEq]
    have h := (hc i.val 0 i.property (by omega)).1
    simp [polyBound] at h
    linarith
  have sizeD : D (fun i => headSize k (b i)) := add (add floorD db) (cn 16)
  have roundsD : D (fun i => headRounds k (b i)) := add (mul (cn 2) sizeD) (cn 3)
  have capD : D (fun i => headCap k (b i)) := by
    let one := cn 1
    let two := cn 2
    let b1 := add db one
    let m := add db two
    have list {n w : I → ℕ} (hn : D n) (hw : D w) : D (fun i => listCap (n i) (w i)) :=
      add (mul hn (add (mul two hw) two)) one
    let input := list (cn 3) b1
    let plan := add (mul two (add b1 (mul (mul m two) db))) (cn 6)
    let blocks := list m (list sizeD b1)
    let decomp := list (mul two m) b1
    let row := add (mul two (add (list sizeD b1) one)) (cn 5)
    let rep := add (mul two (add (list sizeD b1) (list (mul sizeD sizeD) m))) (cn 5)
    let dq := add (mul two (add (list two b1) plan)) (cn 5)
    let uq := add (mul two (add (add (add (add b1 (add sizeD one)) rep) (list sizeD b1)) one)) (cn 11)
    let hdr := add (add (add (add (cn 16) input) db) db) sizeD
    let f := add (add (add (add (add (add (add hdr plan) blocks) decomp) row) rep) dq) uq
    let cycle := add (add (mul two (list (cn 12) f)) f) (cn 5)
    exact mul (cn 16) (add cycle one)
  have polyD (f : I → ℕ) (hf : D f) : Dom S (fun i => polyBound k (f i)) := by
    have one := (hf.add hs (dconst hs 1)).pow hs (fun i => by positivity) k
    simpa only [polyBound, Nat.cast_one] using
      (dconst hs k).mul one (fun _ => Nat.cast_nonneg _) (fun i => by positivity)
  have oracleD : Dom S (fun i => headOracle k (b i)) :=
    dm.add hs (polyD _ (add (add sizeD db) (cn 1)))
  obtain ⟨j,hj⟩ := (roundsD.add hs capD).add hs oracleD
  refine ⟨4*j,fun p hp => ?_⟩
  let i : I := ⟨p,hp⟩
  have hsum := hj i
  change (headRounds k (bitLen p) : ℝ)+(headCap k (bitLen p) : ℝ)+headOracle k (bitLen p) ≤
    E (sScale (bitLen p)) j at hsum
  rw [sEq] at hsum
  have growth : mainSpaceBound j (bitLen p) ≤ mainSpaceBound (4*j) (bitLen p) :=
    (stage1_complexity_dominance.1 _ _ _ (by omega)).1
  have time : mainSpaceBound j (bitLen p) ≤ mainTimeBound (4*j) (bitLen p) := by
    rw [←sEq,←tEq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    calc
      (j : ℝ)*sScale (bitLen p) ≤ j*(4*tScale (bitLen p)) :=
        mul_le_mul_of_nonneg_left (compareScale _) (Nat.cast_nonneg _)
      _ = ((4*j : ℕ) : ℝ)*tScale (bitLen p) := by push_cast; ring
  have ho : 0 ≤ headOracle k (bitLen p) := by unfold headOracle mainSpaceBound polyBound; positivity
  have hr := Nat.cast_nonneg (α:=ℝ) (headRounds k (bitLen p))
  have ha := Nat.cast_nonneg (α:=ℝ) (headCap k (bitLen p))
  dsimp only
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end DetDLP.W3C.FpDriverAssembly
end

section
set_option autoImplicit false

namespace DetDLP.W3C
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem driverFromCountsOfCutTail
    (counts : M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_fpQueries) (hupdate : w3_hnfOps)
    (tail : FpDriverAssembly.CutTail
      (Classical.choice (FpOracles.available counts ⟨en,eo⟩ ⟨de,do'⟩ hnet hupdate))) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        let M := p-1
        let m := blockCount (bitLen p)
        orderOf h = M →
          let accepts := fun u => RunsWithin D out (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M (Additive.ofMul h) (Additive.ofMul a) accepts) ∧
          (∀ hg : w3_large p M, letI : NeZero M := ⟨by have := hg.2.1; omega⟩
            ∀ F : Fin m → List (ZMod p)ˣ, w3_fpBaseCalls en eo de do' K F →
              ∃ (seed : FpSeed p m) (B : Fin m → List (ZMod p)ˣ),
                (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p M m M) seed i) ∧
                w3_traceOutput (w3_fpFB F) (w3_fpFB B) M (Additive.ofMul h) (Additive.ofMul a) accepts) := by
  let kit := Classical.choice (FpOracles.available counts ⟨en,eo⟩ ⟨de,do'⟩ hnet hupdate)
  obtain ⟨J, tailAt⟩ := tail
  obtain ⟨H, costs⟩ := FpDriverAssembly.headBudgetsDominated (FpDriverAssembly.kitCost kit)
  apply FpDriverFromCounts.ofTraceBounds counts en eo de do' K hnet hupdate
  apply FpDriverAssembly.closeBranches kit K (max H J)
  intro p hp g a gen large
  exact FpDriverAssembly.assembleLarge kit J H tailAt p g a gen large (costs p hp.out.two_le)

end DetDLP.W3C
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTerminalBound

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpStep FpTraceStep FpCoordinateWidths NineOracleLoop

def packetLimit (K n : ℕ) := n+K*(n+1)^K
def answerLimit (q : w3_Query) := listCap (w3_len q) (w3_precision q+1)

theorem answerLength {q : w3_Query} {ans : Word} {P : TruncPoly (w3_precision q) (w3_len q)}
    (h : EncodesTruncPoly (w3_precision q) (w3_len q) ans P) : ans.length ≤ answerLimit q := by
  obtain ⟨coef, hc, rfl, _⟩ := h
  have hlen (i : Fin (w3_len q)) : (countWord (coef i)).length ≤ w3_precision q+1 := by
    have g := S8G.FpMoment.binaryLen (hc i).le
    simpa only [bitLen, Nat.clog_pow 2 _ (by decide)] using g
  have g := encodedListLe countWord (List.ofFn coef) (w3_precision q+1) (fun x hx => by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hlen i)
  simpa only [answerLimit,encodeNatListBin,List.length_ofFn] using g

theorem descLength {q : w3_Query} {C : ℕ} (net : w3_Net q C) : net.desc.length ≤ (w3_packet net).length := by
  unfold w3_packet encodeTerminalBTNInstance
  rw [encodedCons]
  simp only [id_eq]
  omega

theorem updatedLength (s : FpState) (hs : s.phase = 6) (pkt : Word) :
    (packState (nextState (packState s) 7 s.idx s.blocksWord s.repWord pkt s.pre)).length ≤
      (packState s).length + 2*pkt.length := by
  simp only [nextState, unpackState_packState]
  simp only [packState,fields,encodedCons,encodedNil,id_eq,hs,show (7 == 8) = false by decide,Bool.cond_false]
  have hphys : (countWord 7).length = (countWord 6).length := by decide
  rw [hphys]
  omega

def wordLimit {en de : Port} (kit : Kit en de) (q : w3_Query) (state initial : ℕ) :=
  initial+2*state+5*packetLimit kit.buildC q.input.length+q.input.length+answerLimit q+bitLen q.M+6

noncomputable def contractSpace {en de : Port} (kit : Kit en de) (q : w3_Query) :=
  polyBound kit.contractC (kit.netC*q.m*q.b+packetLimit kit.buildC q.input.length)

noncomputable def time {en de : Port} (kit : Kit en de) (q : w3_Query) :=
  max (polyBound kit.buildC q.input.length) (contractSpace kit q*mainTimeBound kit.contractC q.b)

noncomputable def space {en de : Port} (kit : Kit en de) (q : w3_Query) :=
  max (polyBound kit.buildC q.input.length) (contractSpace kit q)

theorem contractSpaceLe {en de : Port} (kit : Kit en de) {q : w3_Query} (net : w3_Net q kit.netC)
    (hp : (w3_packet net).length ≤ packetLimit kit.buildC q.input.length) :
    polyBound kit.contractC (net.S+net.desc.length) ≤ contractSpace kit q := by
  obtain ⟨_,_,_,_,_,hS,_⟩ := net.shape
  have hN := Nat.add_le_add hS ((descLength net).trans hp)
  unfold contractSpace polyBound
  gcongr

end DetDLP.W3C.FpTerminalBound
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpTailBudget

open DetDLP_W1_Bounds FpDriverAssembly FpCoordinateWidths

abbrev Input := {p : ℕ // 2 ≤ p}
abbrev bits (i : Input) := bitLen i.val
noncomputable abbrev S (i : Input) := sScale (bits i)
noncomputable abbrev T (i : Input) := tScale (bits i)
def Dominated (f : ℕ → ℕ) : Prop := Dom S (fun i => (f (bits i) : ℝ))

private theorem oneS (i : Input) : 1 ≤ S i := scales_one (Nat.clog_pos (by decide) i.property)

theorem constant (n : ℕ) : Dominated (fun _ => n) := dconst oneS n

theorem Dominated.weaken {f g : ℕ → ℕ} (hf : Dominated f) (le : ∀ b, g b ≤ f b) :
    Dominated g := Dom.weaken hf (fun i => by exact_mod_cast le (bits i))

theorem Dominated.add {f g : ℕ → ℕ} (hf : Dominated f) (hg : Dominated g) :
    Dominated (fun b => f b+g b) := by
  simpa only [Dominated,Nat.cast_add] using Dom.add oneS hf hg

theorem Dominated.mul {f g : ℕ → ℕ} (hf : Dominated f) (hg : Dominated g) :
    Dominated (fun b => f b*g b) := by
  simpa only [Dominated,Nat.cast_mul] using Dom.mul hf hg (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)

theorem Dominated.pow {f : ℕ → ℕ} (hf : Dominated f) (c : ℕ) :
    Dominated (fun b => (f b)^c) := by
  simpa only [Dominated,Nat.cast_pow] using Dom.pow oneS hf (fun _ => Nat.cast_nonneg _) c

theorem Dominated.max {f g : ℕ → ℕ} (hf : Dominated f) (hg : Dominated g) :
    Dominated (fun b => max (f b) (g b)) := (hf.add hg).weaken (fun _ => by omega)

theorem Dominated.list {f g : ℕ → ℕ} (hf : Dominated f) (hg : Dominated g) :
    Dominated (fun b => listCap (f b) (g b)) :=
  (hf.mul (((constant 2).mul hg).add (constant 2))).add (constant 1)

theorem bitDominated : Dominated id := by
  obtain ⟨c,h⟩ := stage1_complexity_dominance.2.2.1 1 0
  refine ⟨c,fun i => ?_⟩
  rw [sEq]
  have H := (h i.val 0 i.property (by omega)).1
  simp [polyBound] at H
  change (bitLen i.val : ℝ) ≤ _
  linarith

noncomputable def size (k b : ℕ) := headCap k b+headRounds k b+b+16

theorem sizeDominated (k : ℕ) : Dominated (size k) := by
  obtain ⟨c,hc⟩ := headBudgetsDominated k
  have cap : Dominated (headCap k) := ⟨c,fun i => (hc i.val i.property).2.1.trans_eq (sEq ..).symm⟩
  have rounds : Dominated (headRounds k) := ⟨c,fun i => (hc i.val i.property).1.trans_eq (sEq ..).symm⟩
  exact ((cap.add rounds).add bitDominated).add (constant 16)

def poly (K x : ℕ) := K*(x+1)^K

theorem poly_eq (K x : ℕ) : (poly K x : ℝ) = polyBound K x := by
  simp [poly,polyBound]

theorem Dominated.poly {f : ℕ → ℕ} (hf : Dominated f) (K : ℕ) :
    Dominated (fun b => FpTailBudget.poly K (f b)) :=
  (constant K).mul ((hf.add (constant 1)).pow K)

private theorem promote {f : Input → ℝ} (h : Dom S f) : Dom T f := by
  obtain ⟨c,hc⟩ := h
  refine ⟨4*c,fun i => (hc i).trans ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  calc
    (c:ℝ)*S i ≤ c*(4*T i) := mul_le_mul_of_nonneg_left (compareScale _) (Nat.cast_nonneg _)
    _ = ((4*c:ℕ):ℝ)*T i := by push_cast; ring

theorem time_one (C b : ℕ) : (1:ℝ) ≤ mainTimeBound C b := by
  unfold mainTimeBound
  apply Real.one_le_rpow (by norm_num)
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)

theorem absorb (k : ℕ) {U : ℕ → ℕ} (h : Dominated U) :
    ∃ J : ℕ, ∀ p : ℕ, 2≤p → let b := bitLen p
      ((2*U b : ℕ):ℝ) ≤ mainSpaceBound J b ∧
      (U b:ℝ)*mainTimeBound k b ≤ mainTimeBound J b := by
  have hS := (constant 2).mul h
  have tk : Dom T (fun i => mainTimeBound k (bits i)) := ⟨k,fun i => (tEq ..).ge⟩
  have hT := (promote h).mul tk (fun _ => Nat.cast_nonneg _) (fun i => zero_le_one.trans (time_one k (bits i)))
  obtain ⟨cs,hs⟩ := hS
  obtain ⟨ct,ht⟩ := hT
  refine ⟨max cs ct,fun p hp => ?_⟩
  let i : Input := ⟨p,hp⟩
  exact ⟨((hs i).trans_eq (sEq ..)).trans (spaceMono (le_max_left ..)),
    ((ht i).trans_eq (tEq ..)).trans (timeMono (le_max_right ..))⟩

end DetDLP.W3C.FpTailBudget
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpTailBudget

open FpOracles FpDriverAssembly FpCoordinateWidths FpTerminalBound

def tupleWidth (x : ℕ) := 4*x*x
def cutCount (x : ℕ) := x*x
def rounds (x : ℕ) := 3+cutCount x*(2*tupleWidth x+3)

def query (x : ℕ) :=
  2*(listCap 4 (x+1)+listCap (x*2) (x+1)+blocksCap x x x+listCap x (x+1)+tupleWidth x)+11

def saved (x : ℕ) :=
  listCap 12 (2*x+cutCount x+repCap x x+rowCap x x+tupleWidth x+12)

def updateWords (x : ℕ) := 2*saved x+updateQueryCap x x+repCap x x+5
def initialWords (x : ℕ) := 2*listCap 12 (x+x+12)+1+repCap x x

def packet (build x : ℕ) := packetLimit build (query x)
def answer (net x : ℕ) := listCap (net*x) (net*x*x+1)
def probeWords (build net x : ℕ) :=
  2*saved x+5*packet build x+query x+answer net x+x+6

def oracleCosts {en de : Port} (kit : Kit en de) (x : ℕ) :=
  poly kit.buildC (query x)+poly kit.contractC (kit.netC*x*x+packet kit.buildC x)+poly kit.updateC (x+x)

def uniform {en de : Port} (kit : Kit en de) (x : ℕ) :=
  1+rounds x+updateWords x+initialWords x+probeWords kit.buildC kit.netC x+oracleCosts kit x

private theorem domEnvelope {en de : Port} (kit : Kit en de) {X : ℕ → ℕ} (u : Dominated X) :
    Dominated (fun b => uniform kit (X b)) := by
  let cn := constant
  let one := cn 1
  let two := cn 2
  let x1 := u.add one
  let x2 := u.add two
  let h := u.mul u
  let l := ((cn 4).mul u).mul u
  let rep := (two.mul ((u.list x1).add (h.list x2))).add (cn 5)
  let row := (two.mul ((u.list x1).add one)).add (cn 5)
  let upd := (two.mul (((x1.add x1).add rep).add (u.list x1) |>.add one)).add (cn 11)
  let r := (cn 3).add (h.mul ((two.mul l).add (cn 3)))
  let queries := (two.mul (((((cn 4).list x1).add ((u.mul two).list x1)).add
    (u.list (u.list x1))).add (u.list x1) |>.add l)).add (cn 11)
  let v := (cn 12).list (((((two.mul u).add h).add rep).add row).add l |>.add (cn 12))
  let uw := (((two.mul v).add upd).add rep).add (cn 5)
  let iw := ((two.mul ((cn 12).list ((u.add u).add (cn 12)))).add one).add rep
  let pkt := queries.add (queries.poly kit.buildC)
  let nx := (cn kit.netC).mul u
  let ans := nx.list ((nx.mul u).add one)
  let pw := (((((two.mul v).add ((cn 5).mul pkt)).add queries).add ans).add u).add (cn 6)
  let oc := ((queries.poly kit.buildC).add (((nx.mul u).add pkt).poly kit.contractC)).add ((u.add u).poly kit.updateC)
  exact ((((one.add r).add uw).add iw).add pw).add oc

theorem budgets {en de : Port} (kit : Kit en de) :
    ∃ J : ℕ, ∀ p : ℕ, 2 ≤ p → let b := bitLen p
      let U := uniform kit (size (kitCost kit) b)
      ((2*U : ℕ):ℝ) ≤ mainSpaceBound J b ∧ (U:ℝ)*mainTimeBound kit.contractC b ≤ mainTimeBound J b :=
  absorb kit.contractC (domEnvelope kit (sizeDominated (kitCost kit)))

theorem fields {en de : Port} (kit : Kit en de) {p : ℕ} [Fact p.Prime]
    (g a : (ZMod p)ˣ) {N : ℕ} (hN : N ≤ headSize (kitCost kit) (bitLen p)) :
    let b := bitLen p
    let X := size (kitCost kit) b
    b≤X ∧ m p≤X ∧ N≤X ∧ bitLen (p-1)≤X ∧
    fieldLimit b (bitLen (p-1)) (m p) N (input g a).length ≤ X := by
  let k := kitCost kit
  let b := bitLen p
  let D := fieldLimit b (bitLen (p-1)) (m p) N (input g a).length
  have hd := publicCap k g a N hN
  have hl := S8G.FpMoment.blockUpper b
  have hb : bitLen (p-1) ≤ b := Nat.clog_mono_right 2 (Nat.sub_le p 1)
  change 16*(cycleCap D+1) ≤ headCap k b at hd
  change N ≤ headSize k b at hN
  change b ≤ size k b ∧ m p ≤ size k b ∧ N ≤ size k b ∧ bitLen (p-1) ≤ size k b ∧ D ≤ size k b
  unfold size headRounds
  unfold cycleCap listCap at hd
  change m p ≤ b+2 at hl
  omega

theorem polyMono (K : ℕ) {a b : ℕ} (h : a≤b) : poly K a ≤ poly K b := by
  unfold poly
  gcongr

theorem packetMono (K : ℕ) {a b : ℕ} (h : a≤b) : packetLimit K a≤packetLimit K b :=
  Nat.add_le_add h (polyMono K h)

theorem listMono {n k a b : ℕ} (hn : n≤k) (ha : a≤b) : listCap n a≤listCap k b := by
  unfold listCap
  gcongr

end DetDLP.W3C.FpTailBudget
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTerminalBound

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open FpOracles FpCoordinateWidths

def queryLimit (b m N U : ℕ) :=
  2*(listCap 4 (b+1)+listCap (m*2) (b+1)+blocksCap b m N+listCap N (b+1)+U)+11

private theorem seedLength {p m : ℕ} [Fact p.Prime] (seed : FpSeed p m) :
    (encodeNatListBin ((List.finRange m).flatMap fun i => [(seed i).1.val+1,(seed i).2.val])).length ≤
      listCap (m*2) (bitLen p+1) := by
  let nums := (List.finRange m).flatMap fun i => [(seed i).1.val+1,(seed i).2.val]
  have plen : nums.length=m*2 := by simp [nums,List.length_flatMap]
  rw [← plen]
  apply encodedListLe
  intro x hx
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl
  · exact S8G.FpMoment.binaryLen (by have := (seed i).1.isLt; omega)
  · exact S8G.FpMoment.binaryLen (seed i).2.isLt.le

theorem queryLength {q : w3_Query} (hq : w3_fpQueries q) :
    q.input.length ≤ queryLimit q.b q.m q.FB.totalCoords q.pre.length := by
  obtain ⟨p,hp,_,hnz,h64,h4096,seed,B,_,g,y,u,rfl⟩ := hq
  let _ : Fact p.Prime := hp
  let _ : NeZero (p-1) := ⟨hnz.ne'⟩
  have hT : hashThreshold p (p-1) (m p) (p-1) ≤ p :=
    m89_decode.threshold_le (le_max_left ..) h64 h4096
  have hhead : (encodeNatListBin [p,(g : ZMod p).val,p-1,hashThreshold p (p-1) (m p) (p-1)]).length ≤
        listCap 4 (bitLen p+1) := by
    apply encodedListLe
    intro x hx
    apply S8G.FpMoment.binaryLen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · exact (g : ZMod p).val_lt.le
    · omega
    · exact hT
  have hlab : (encodeNatListBin (List.ofFn fun i => (y i).val)).length ≤
      listCap (w3_fpFB B).totalCoords (bitLen p+1) := by
    have h := encodedListLe countWord (List.ofFn fun i => (y i).val) (bitLen p+1) (fun x hx => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact S8G.FpMoment.binaryLen ((y i).val_lt.le.trans (Nat.sub_le p 1)))
    simpa only [encodeNatListBin,List.length_ofFn] using h
  have hseed := seedLength seed
  have hblocks := blocksLe B
  change (Encoding.encodeList id [_ , _, encodeFpFactorBlocks B, _, u]).length ≤
    queryLimit (bitLen p) (m p) (w3_fpFB B).totalCoords u.length
  change (encodeFpFactorBlocks B).length ≤ blocksCap (bitLen p) (m p) (w3_fpFB B).totalCoords at hblocks
  simp only [encodedCons,encodedNil,id_eq,queryLimit]
  dsimp only [FpOracles.m] at hhead hblocks ⊢
  omega

theorem answerLimit_le {q : w3_Query} {C : ℕ} (net : w3_Net q C) :
    answerLimit q ≤ listCap (C*q.m) (C*q.m*q.b+1) := by
  obtain ⟨_,_,_,_,_,hs,_,_,_,hp,_,hl⟩ := net.shape
  have hh := hp.trans hs
  unfold answerLimit listCap
  gcongr

theorem fuelWidth (base k f : ℕ) (hf : f ≤ base+k) :
    (countWord f).length ≤ (countWord base).length+k+1 := by
  have hbase : base < 2^(countWord base).length := by
    by_cases h : base=0
    · subst base; decide
    · simpa only [countWord,if_neg h,← Nat.size_eq_bits_len] using Nat.lt_size_self base
  have hsum (n : ℕ) : base+n < 2^((countWord base).length+n) := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      rw [show (countWord base).length+(n+1) = ((countWord base).length+n)+1 by omega, pow_succ]
      omega
  have h := S8G.FpMoment.binaryLen (hf.trans (hsum k).le)
  simpa only [bitLen,Nat.clog_pow 2 _ (by decide)] using h

theorem cutHeight (M N : ℕ) : Nat.clog 2 (M^N) ≤ bitLen M*N := by
  have h : M^N ≤ 2^(bitLen M*N) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) M) N
  simpa only [Nat.clog_pow 2 _ (by decide)] using Nat.clog_mono_right 2 h

end DetDLP.W3C.FpTerminalBound
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTerminalBound

open FpOracles FpCoordinateWidths FpStep FpCutExec FpLargeEntry NineOracleLoop
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def savedCap (D H R P U : ℕ) := listCap 12 (2*D+H+R+P+U+12)

theorem savedLength {s : FpState} {D : ℕ} (hs : Stored D s) (H R P U : ℕ) (k idx f : ℕ)
    (r pkt u : Word) (hk : k ≤ 8) (hi : idx ≤ 1) (hf : f ≤ s.fuel+H)
    (hr : r.length ≤ R) (hp : pkt.length ≤ P) (hu : u.length ≤ U) :
    (packState (st s k idx f r pkt u)).length ≤ savedCap D H R P U := by
  let K := 2*D+H+R+P+U+12
  have hbase (w : Word) (hw : w ∈ baseWords s) : w.length ≤ K :=
    (hs.header w hw).trans (by dsimp [K]; omega)
  have hif := w3_queryIndexLength idx
  have hkf := w3_queryIndexLength k
  have hfuel := fuelWidth s.fuel H f hf
  have hprev := hs.header (countWord s.fuel) (by simp [baseWords])
  apply packedLe
  intro z hz
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | omega | exact hbase _ (by simp [baseWords])

theorem startPairLength {q : w3_Query} {s : FpState} {D : ℕ} (hs : Stored D s)
    (hk : s.phase ≤ 8) (hi : s.idx ≤ q.FB.totalCoords) (r : Rep q)
    (hr : IsModularLatticeBasis q.M r.2) :
    (pairWord (packState s) (FpCutExec.repWord r)).length ≤
      2*listCap 12 (D+q.FB.totalCoords+12)+1+repCap q.FB.totalCoords (bitLen q.M) := by
  let K := D+q.FB.totalCoords+12
  have hnew : Stored K s := by
    refine ⟨fun z hz => (hs.header z hz).trans ?_,hs.rep.trans ?_,hs.pkt.trans ?_,hs.pre.trans ?_⟩ <;>
      dsimp only [K] <;> omega
  have h0 := w3_queryIndexLength s.phase
  have h1 := w3_queryIndexLength s.idx
  have hstate := packStored hnew (by dsimp [K]; omega) (by dsimp [K]; omega)
  have hrep : (FpCutExec.repWord r).length ≤ repCap q.FB.totalCoords (bitLen q.M) := representativeLe r hr
  rw [pairLength]
  change _ ≤ 2*listCap 12 K+1+_
  omega

theorem probeStateLength {q : w3_Query} {s : FpState} {D : ℕ} (hs : Stored D s)
    (r : Rep q) (hr : IsModularLatticeBasis q.M r.2) {H L f idx : ℕ} (saved : Word)
    (hf : f ≤ s.fuel+H) (hi : idx ≤ 1) (hu : saved.length ≤ L) :
    (packState (st s 6 idx f (FpCutExec.repWord r) [] saved)).length ≤
      savedCap D H (repCap q.FB.totalCoords (bitLen q.M)) 0 L :=
  savedLength hs _ _ _ _ _ _ _ _ _ _ (by decide) hi hf (representativeLe r hr) (by decide) hu

end DetDLP.W3C.FpTerminalBound
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpProbeWidths

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private def rightBlank {A : PrimitiveMachine} (c : A.Cfg) (n : ℕ) : Prop :=
  ∀ i (k : ℤ), (n : ℤ) ≤ k → (c.tapes i).nth k = none

private theorem stepBlank {A : PrimitiveMachine} {c e : A.Cfg} {n : ℕ}
    (h : A.step c = some e) (hb : rightBlank c n) : rightBlank e (n+1) := by
  cases c with
  | mk state tapes =>
    cases state with
    | inl halt => simp [PrimitiveMachine.step] at h
    | inr q =>
      cases ha : A.transition q (tapes (A.scan q)).head with
      | inl halt =>
        simp [PrimitiveMachine.step,ha] at h
        subst e
        exact fun i k hk => hb i k (by omega)
      | inr qa =>
        obtain ⟨next, action⟩ := qa
        simp only [PrimitiveMachine.step,ha,Option.some.injEq] at h
        subst e
        intro i k hk
        by_cases hi : i = A.scan q
        · subst i
          simp only [Function.update_self]
          cases action with
          | move dir =>
            cases dir with
            | left => exact (Turing.Tape.move_left_nth ..).trans (hb _ _ (by omega))
            | right => exact (Turing.Tape.move_right_nth ..).trans (hb _ _ (by omega))
          | write sym =>
            rw [Turing.Tape.write_nth, if_neg (show k ≠ 0 by omega)]
            exact hb _ _ (by omega)
        · simp only [Function.update_of_ne hi]
          exact hb _ _ (by omega)

private theorem traceBlank {A : PrimitiveMachine} {c e : LocatedCfg A} {t n : ℕ}
    (h : Trace (locatedStep A) t c e) (hb : rightBlank c.config n) : rightBlank e.config (n+t) := by
  induction h generalizing n with
  | refl => exact hb
  | cons hs _ ih =>
    have g := ih (stepBlank (locatedStep_config hs) hb)
    simpa only [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1] using g

private theorem initialBlank (A : PrimitiveMachine) (w : List Bool) :
    rightBlank (locatedInit A w).config w.length := by
  intro i k hk
  lift k to ℕ using (by omega)
  simp only [locatedInit, PrimitiveMachine.init]
  split
  · simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk]
    exact List.getI_eq_default _ (by simpa using hk)
  · simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
    rfl

theorem outputLength {A : PrimitiveMachine} {out : Fin A.tapeCount} {w y : List Bool} {τ σ : ℝ}
    (h : RunsWithin A out w y τ σ) : (y.length : ℝ) ≤ (w.length : ℝ)+τ := by
  obtain ⟨t, e, tr, _, hout, ht, _⟩ := h
  have hblank := traceBlank tr (initialBlank A w) out ((w.length+t : ℕ) : ℤ) (by omega)
  have hlen : y.length ≤ w.length+t := by
    by_contra! hlong
    rw [hout] at hblank
    simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk] at hblank
    rw [List.getI_eq_getElem _ (by simpa using hlong), List.getElem_map] at hblank
    contradiction
  have hreal : (y.length : ℝ) ≤ (w.length : ℝ)+(t : ℝ) := by exact_mod_cast hlen
  exact hreal.trans (add_le_add_right ht _)

theorem polyOutputLength {A : PrimitiveMachine} {out : Fin A.tapeCount} {w y : List Bool} {K : ℕ} {σ : ℝ}
    (h : RunsWithin A out w y (polyBound K w.length) σ) : y.length ≤ w.length+K*(w.length+1)^K := by
  have H := outputLength h
  unfold polyBound at H
  exact_mod_cast H

end DetDLP.W3C.FpProbeWidths
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTerminalBound

open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup FpCoordinateWidths
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem boundedProbe {en de : Port} (kit : Kit en de) {q : w3_Query} (hq : w3_fpQueries q) :
    ∃ (net : w3_Net q kit.netC) (ans : Word),
      EncodesTruncPoly (w3_precision q) (w3_len q) ans (BTNContract net.G net.T) ∧
      calls kit (time kit q) (space kit q) (tag9 6 q.input) (w3_packet net) ∧
      calls kit (time kit q) (space kit q) (tag9 7 (w3_packet net)) ans ∧
      (w3_packet net).length ≤ packetLimit kit.buildC q.input.length ∧ ans.length ≤ answerLimit q := by
  obtain ⟨net,ans,hbuild,henc,hcontract⟩ := kit.probe q hq
  have hp : (w3_packet net).length ≤ packetLimit kit.buildC q.input.length :=
    FpProbeWidths.polyOutputLength hbuild
  have hcs := contractSpaceLe kit net hp
  refine ⟨net,ans,henc,⟨6,_,rfl,MachineComposition.runsWithin_mono hbuild (le_max_left ..) (le_max_left ..)⟩,
    ⟨7,_,rfl,MachineComposition.runsWithin_mono hcontract ?_ (hcs.trans (le_max_right ..))⟩,hp,answerLength henc⟩
  apply le_trans _ (le_max_right ..)
  exact mul_le_mul_of_nonneg_right hcs (by unfold mainTimeBound; positivity)

theorem rootProbe {en de : Port} (kit : Kit en de) {q : w3_Query}
    (hq : w3_fpQueries q) (hz : w3_mass q = 0) {N : ℕ} (r : w3_Rep q.M N) (j : Fin N)
    (s : FpState) (hk : s.phase=6) (hi : s.idx=0) (hm : s.p-1=q.M)
    (hr : s.repWord=encodeCosetRep (fun i => (r.1 i).val) r.2)
    (hj : (decodeBlocks s.blocksWord).flatten.length+1=j.val) (v a : Word)
    (root : stepFn (pairWord v a)=false :: pairWord (packState s) (tag9 6 q.input)) :
    LoopRuns stepFn (calls kit (time kit q) (space kit q)) 3 v a (countWord (r.1 j).val)
      (wordLimit kit q (packState s).length (pairWord v a).length) := by
  obtain ⟨net,ans,henc,hb,hc,hpkt,ha⟩ := boundedProbe kit hq
  let pkt := w3_packet net
  let s' := nextState (packState s) 7 s.idx s.blocksWord s.repWord pkt s.pre
  let y := countWord (r.1 j).val
  let C := wordLimit kit q (packState s).length (pairWord v a).length
  have hp : pkt.length ≤ packetLimit kit.buildC q.input.length := hpkt
  have hy : y.length ≤ bitLen q.M + 1 := S8G.FpMoment.binaryLen (r.1 j).val_lt.le
  have hs' : (packState s').length ≤ (packState s).length+2*pkt.length := updatedLength s hk pkt
  have hpos : positive q.M pkt ans = false := by simp only [pkt,positive_spec net henc,hz,lt_self_iff_false,decide_false]
  have halt : stepFn (pairWord (packState s') ans)=true::y := by
    exact root_output s' r j rfl hi (by simpa only [s',nextState,unpackState_packState] using hm)
      hr hj hpos
  have tag6 : (tag9 6 q.input).length = q.input.length+3 := rfl
  have tag7 : (tag9 7 pkt).length = pkt.length+4 := rfl
  have cap1 : (pairWord v a).length ≤ C := by dsimp only [C,wordLimit]; omega
  have cap2 : (pairWord (packState s) (tag9 6 q.input)).length ≤ C := by
    rw [pairLength,tag6]; dsimp only [C,wordLimit]; omega
  have capp : pkt.length ≤ C := by dsimp only [C,wordLimit]; omega
  refine Or.inr ⟨packState s,tag9 6 q.input,pkt,root,cap1,cap2,capp,hb,?_⟩
  change LoopRuns stepFn (calls kit (time kit q) (space kit q)) 2 (packState s) pkt y C
  apply contract_round (j:=1) s hk pkt ans _ hc
  · rw [pairLength]; dsimp only [C,wordLimit]; omega
  · change (pairWord (packState s') (tag9 7 pkt)).length ≤ C
    rw [pairLength,tag7]; dsimp only [C,wordLimit]; omega
  · dsimp only [C,wordLimit]; omega
  · refine Or.inl ⟨halt,?_,?_⟩
    · change (pairWord (packState s') ans).length ≤ C
      rw [pairLength]; dsimp only [C,wordLimit]; omega
    · dsimp only [C,wordLimit]; omega

theorem zeroRoot {en de : Port} (kit : Kit en de) {q : w3_Query} {s : FpState} {L : ℕ}
    {enc : q.V → Word} (w : FpCutExec.Wires q s L enc) (r : FpCutExec.Rep q)
    (j : Fin q.FB.totalCoords) (hj : (decodeBlocks s.blocksWord).flatten.length+1=j.val)
    (hz : w3_mass (Stage2Trace.root q r)=0) (f : ℕ) (v a : Word)
    (root : FpCutExec.RootStep (s:=s) r f v a) :
    let query := FpCutExec.probe q s r []
    let state := FpCutExec.rootState (s:=s) r f
    r.1 ∈ w3_coset r ∧ w3_pass q.FB q.M q.P r.1 ∧
      LoopRuns stepFn (calls kit (time kit query) (space kit query)) 3 v a (countWord (r.1 j).val)
        (wordLimit kit query (packState state).length (pairWord v a).length) := by
  refine ⟨⟨0, fun i => by simp⟩, w3c_zero_pass (Stage2Trace.root q r) rfl hz, ?_⟩
  exact rootProbe kit (w.valid r []) hz r j (FpCutExec.rootState (s:=s) r f) rfl rfl w.modulus
    rfl hj v a root

end DetDLP.W3C.FpTerminalBound
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTerminalBound

open FpOracles FpCoordinateWidths FpCutExec FpStep FpLargeEntry NineOracleLoop

def queryPacket {en de : Port} (kit : Kit en de) (b m N L : ℕ) :=
  packetLimit kit.buildC (queryLimit b m N L)

noncomputable def probeSpace {en de : Port} (kit : Kit en de) (b m N L : ℕ) :=
  max (polyBound kit.buildC (queryLimit b m N L))
    (polyBound kit.contractC (kit.netC*m*b+queryPacket kit b m N L))

noncomputable def probeTime {en de : Port} (kit : Kit en de) (b m N L : ℕ) :=
  max (polyBound kit.buildC (queryLimit b m N L))
    (polyBound kit.contractC (kit.netC*m*b+queryPacket kit b m N L)*mainTimeBound kit.contractC b)

def probeCap {en de : Port} (kit : Kit en de) (b m N bm D H L : ℕ) :=
  2*savedCap D H (repCap N bm) 0 L + 5*queryPacket kit b m N L + queryLimit b m N L +
    listCap (kit.netC*m) (kit.netC*m*b+1) + bm + 6

private theorem monoInput (K : ℕ) {a b : ℕ} (h : a ≤ b) : polyBound K a ≤ polyBound K b := by
  unfold polyBound; gcongr

theorem probeBounds {en de : Port} (kit : Kit en de) {q : w3_Query} {s : FpState} {D H L : ℕ}
    {enc : q.V → Word} (w : Wires q s L enc) (hs : Stored D s) (r : Rep q)
    (hr : IsModularLatticeBasis q.M r.2) (f idx : ℕ) (saved queried : Word)
    (hf : f ≤ s.fuel+H) (hi : idx ≤ 1) (ha : saved.length ≤ L) (hu : queried.length ≤ L) :
    let q' := probe q s r queried
    let state := st s 6 idx f (FpCutExec.repWord r) [] saved
    time kit q' ≤ probeTime kit q.b q.m q.FB.totalCoords L ∧
      space kit q' ≤ probeSpace kit q.b q.m q.FB.totalCoords L ∧
      wordLimit kit q' (packState state).length 0 ≤ probeCap kit q.b q.m q.FB.totalCoords (bitLen q.M) D H L := by
  let q' := probe q s r queried
  let state := st s 6 idx f (FpCutExec.repWord r) [] saved
  have hv := w.valid r queried
  have hi' : q'.input.length ≤ queryLimit q.b q.m q.FB.totalCoords L := by
    have g := queryLength hv
    change q'.input.length ≤ queryLimit q.b q.m q.FB.totalCoords queried.length at g
    exact g.trans (by unfold queryLimit; omega)
  have hp : packetLimit kit.buildC q'.input.length ≤ queryPacket kit q.b q.m q.FB.totalCoords L := by
    unfold queryPacket packetLimit; gcongr
  have ha' : answerLimit q' ≤ listCap (kit.netC*q.m) (kit.netC*q.m*q.b+1) := by
    obtain ⟨net,_,_⟩ := kit.probe _ hv
    exact answerLimit_le net
  have hs' : (packState state).length ≤ savedCap D H (repCap q.FB.totalCoords (bitLen q.M)) 0 L :=
    probeStateLength hs r hr saved hf hi ha
  have hb := monoInput kit.buildC hi'
  have hc : contractSpace kit q' ≤ polyBound kit.contractC (kit.netC*q.m*q.b+queryPacket kit q.b q.m q.FB.totalCoords L) :=
    monoInput _ (Nat.add_le_add_left hp _)
  refine ⟨max_le_max hb (mul_le_mul_of_nonneg_right hc (by unfold mainTimeBound; positivity)),max_le_max hb hc,?_⟩
  change wordLimit kit q' (packState state).length 0 ≤ _
  unfold wordLimit probeCap
  change 0+2*(packState state).length + 5*packetLimit kit.buildC q'.input.length + q'.input.length + answerLimit q' + bitLen q.M + 6 ≤ _
  omega

end DetDLP.W3C.FpTerminalBound
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpPositiveCuts
open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup FpCutExec
open FpTerminalBound FpCoordinateWidths
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def updateStateOf (q : w3_Query) (s : FpState) (enc : q.V → Word)
    (r : Rep q) (f : ℕ) (X Y : q.FB.BlockTuple) : FpState :=
  st s 8 0 f (FpCutExec.repWord r)
    (rowPkt q.M 1 (shiftRowCounts (blocks q.FB enc) (words q.FB enc X) (words q.FB enc Y))) []

structure Caps {en de : Port} (kit : Kit en de) (q : w3_Query) (s : FpState) (L : ℕ)
    (enc : q.V → Word) (z : w3_Label q.M q.FB.totalCoords) (F : ℕ) (τ σ : ℝ) (C : ℕ) : Prop where
  probes : ∀ (r : Rep q), Stage2Trace.Invariant z r → ∀ (f idx : ℕ) (saved queried : Word),
    f ≤ F → idx ≤ 1 → saved.length ≤ L → queried.length ≤ L →
    let query := probe q s r queried
    let state := st s 6 idx f (FpCutExec.repWord r) [] saved
    FpTerminalBound.time kit query ≤ τ ∧ FpTerminalBound.space kit query ≤ σ ∧ FpTerminalBound.wordLimit kit query (packState state).length 0 ≤ C
  updateTime : polyBound kit.updateC (q.FB.totalCoords+bitLen q.M) ≤ τ
  updateSpace : polyBound kit.updateC (q.FB.totalCoords+bitLen q.M) ≤ σ
  updates : ∀ (r r' : Rep q), Stage2Trace.Invariant z r → Stage2Trace.Invariant z r' →
    ∀ (f : ℕ), f ≤ F → ∀ X Y : q.FB.BlockTuple,
    let up := updateStateOf q s enc r f X Y
    (pairWord (packState up) (tag9 8 (queryInput 8 up))).length ≤ C ∧
      (pairWord (packState up) (FpCutExec.repWord r')).length ≤ C

end DetDLP.W3C.FpPositiveCuts
end

section
set_option autoImplicit false

namespace DetDLP.W3C.FpTerminalBound

open FpCoordinateWidths FpTraceStep FpStep FpLargeEntry FpCutExec NineOracleLoop BlockLookup
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

def updateCap (D H N b : ℕ) :=
  2*savedCap D H (repCap N b) (rowCap b N) 0 + updateQueryCap b N + repCap N b + 5

theorem updateLengths {q : w3_Query} {s : FpState} {enc : q.V → Word} {L D H : ℕ}
    (w : Wires q s L enc) (hs : Stored D s) (r r' : Rep q)
    (basis : IsModularLatticeBasis q.M r.2) (basis' : IsModularLatticeBasis q.M r'.2)
    (f : ℕ) (hf : f ≤ s.fuel+H) (X Y : q.FB.BlockTuple) :
    let up := FpPositiveCuts.updateStateOf q s enc r f X Y
    let C := updateCap D H q.FB.totalCoords (bitLen q.M)
    (pairWord (packState up) (tag9 8 (queryInput 8 up))).length ≤ C ∧
      (pairWord (packState up) (FpCutExec.repWord r')).length ≤ C := by
  let raw := shiftRowCounts (blocks q.FB enc) (words q.FB enc X) (words q.FB enc Y)
  let z := (w3_shiftRow q.FB q.M X Y).1
  let up := FpPositiveCuts.updateStateOf q s enc r f X Y
  have hraw : raw.map (fun x : ℤ => (x : ZMod q.M))=List.ofFn z :=
    congrArg Prod.fst (shiftRowCounts_correct q.FB enc w.distinct q.M X Y)
  have hn : raw.length=q.FB.totalCoords := by simpa only [List.length_map,List.length_ofFn] using congrArg List.length hraw
  have hip : (rowPkt q.M 1 raw).length ≤ rowCap (bitLen q.M) q.FB.totalCoords :=
    (rowPacketLe raw 1 (by decide)).trans_eq (congrArg _ hn)
  have hstate : (packState up).length ≤ savedCap D H (repCap q.FB.totalCoords (bitLen q.M))
      (rowCap (bitLen q.M) q.FB.totalCoords) 0 :=
    savedLength hs _ _ _ _ 8 0 f _ _ [] (by decide) (by decide) hf (representativeLe r basis) hip (by decide)
  have hquery : queryInput 8 up = encodeCosetUpdateInput q.M (fun i => (r.1 i).val) r.2 (fun i => (z i).val) 1 :=
    update_input (st s 8 0 f [] [] []) _ _ z 1 raw w.modulus w.dimension hraw
  have hq : (queryInput 8 up).length ≤ updateQueryCap (bitLen q.M) q.FB.totalCoords := by
    rw [hquery]
    have g := updateQueryLe r basis z
    simpa only [encodeCosetUpdateInput, encodedCons, encodedNil, id_eq,
      show (countWord 0).length = (countWord 1).length from rfl] using g
  have hr : (FpCutExec.repWord r').length ≤ repCap q.FB.totalCoords (bitLen q.M) := representativeLe r' basis'
  change (pairWord (packState up) (tag9 8 (queryInput 8 up))).length ≤ _ ∧
    (pairWord (packState up) (FpCutExec.repWord r')).length ≤ _
  simp only [pairLength,tag8Length,updateCap]
  omega

end DetDLP.W3C.FpTerminalBound
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpTailBudget

open FpOracles FpTerminalBound FpCoordinateWidths

private theorem factorTime {en de : Port} (kit : Kit en de) (x b : ℕ) :
    (uniform kit x:ℝ) ≤ (uniform kit x:ℝ)*mainTimeBound kit.contractC b :=
  le_mul_of_one_le_right (Nat.cast_nonneg _) (time_one ..)

private theorem repLe {x n b : ℕ} (hn : n≤x) (hb : b≤x) : repCap n b≤repCap x x := by
  unfold repCap listCap
  gcongr

private theorem rowLe {x n b : ℕ} (hn : n≤x) (hb : b≤x) : rowCap b n≤rowCap x x := by
  unfold rowCap listCap
  gcongr

private theorem savedLe {x D H R P L : ℕ} (hd : D≤x) (hh : H≤cutCount x)
    (hr : R≤repCap x x) (hp : P≤rowCap x x) (hl : L≤tupleWidth x) :
    savedCap D H R P L ≤ saved x := by
  apply listMono (le_refl 12)
  omega

theorem probeCosts {en de : Port} (kit : Kit en de) {x b m N bm D H L : ℕ} (hb : b≤x) (hm : m≤x)
    (hn : N≤x) (hM : bm≤x) (hd : D≤x) (hh : H≤cutCount x) (hl : L≤tupleWidth x) :
    probeTime kit b m N L ≤ (uniform kit x:ℝ)*mainTimeBound kit.contractC b ∧
    probeSpace kit b m N L ≤ (uniform kit x:ℝ) ∧ probeCap kit b m N bm D H L ≤ uniform kit x := by
  have hq : queryLimit b m N L ≤ query x := by unfold queryLimit query blocksCap listCap; gcongr
  have hp := packetMono kit.buildC hq
  change queryPacket kit b m N L≤packet kit.buildC x at hp
  have hg := Nat.mul_le_mul (Nat.mul_le_mul_left kit.netC hm) hb
  have ha : listCap (kit.netC*m) (kit.netC*m*b+1) ≤ answer kit.netC x :=
    listMono (Nat.mul_le_mul_left kit.netC hm) (Nat.add_le_add_right hg 1)
  have hs := savedLe hd hh (repLe hn hM) (Nat.zero_le (rowCap x x)) hl
  have hBuild : polyBound kit.buildC (queryLimit b m N L) ≤ (uniform kit x:ℝ) := by
    rw [← poly_eq]
    exact_mod_cast (polyMono kit.buildC hq).trans (by unfold uniform oracleCosts; omega)
  have hcontract : polyBound kit.contractC (kit.netC*m*b+queryPacket kit b m N L) ≤ (uniform kit x:ℝ) := by
    rw [← poly_eq]
    exact_mod_cast (polyMono kit.contractC (Nat.add_le_add hg hp)).trans (by unfold uniform oracleCosts; omega)
  refine ⟨max_le (hBuild.trans (factorTime kit x b))
    (mul_le_mul_of_nonneg_right hcontract (zero_le_one.trans (time_one ..))),max_le hBuild hcontract,?_⟩
  unfold probeCap uniform probeWords
  omega

theorem updateBounds {en de : Port} (kit : Kit en de) {x N bm b : ℕ} (hn : N≤x) (hm : bm≤x) :
    polyBound kit.updateC (N+bm) ≤ (uniform kit x:ℝ)*mainTimeBound kit.contractC b ∧
    polyBound kit.updateC (N+bm) ≤ (uniform kit x:ℝ) := by
  have hu : polyBound kit.updateC (N+bm) ≤ (uniform kit x:ℝ) := by
    rw [← poly_eq]
    exact_mod_cast (polyMono kit.updateC (Nat.add_le_add hn hm)).trans (by unfold uniform oracleCosts; omega)
  exact ⟨hu.trans (factorTime kit x b),hu⟩

theorem updateCapLe {en de : Port} (kit : Kit en de) {x D H N bm : ℕ}
    (hd : D≤x) (hh : H≤cutCount x) (hn : N≤x) (hb : bm≤x) : updateCap D H N bm≤uniform kit x := by
  have hr := repLe hn hb
  have hp := rowLe hn hb
  have hs := savedLe hd hh hr hp (Nat.zero_le (tupleWidth x))
  have hq : updateQueryCap bm N≤updateQueryCap x x := by unfold updateQueryCap repCap listCap; gcongr
  unfold updateCap uniform updateWords
  omega

theorem initialLe {en de : Port} (kit : Kit en de) {x D N bm : ℕ}
    (hd : D≤x) (hn : N≤x) (hb : bm≤x) :
    2*listCap 12 (D+N+12)+1+repCap N bm ≤ uniform kit x := by
  have hr := repLe hn hb
  have hq : listCap 12 (D+N+12)≤listCap 12 (x+x+12) := listMono (le_refl _) (by omega)
  unfold uniform initialWords
  omega

theorem roundsLe {en de : Port} (kit : Kit en de) {x n L : ℕ} (hn : n≤cutCount x) (hl : L≤tupleWidth x) :
    3+n*(2*L+3) ≤ uniform kit x := by
  have hr : 3+n*(2*L+3) ≤ rounds x := by unfold rounds; gcongr
  unfold uniform
  omega

end DetDLP.W3C.FpTailBudget
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpTailBudget

open FpOracles FpTerminalBound FpCoordinateWidths FpCutExec FpPositiveCuts FpStep

theorem assembleCaps {en de : Port} (kit : Kit en de) {q : w3_Query} {s : FpState} {L : ℕ}
    {enc : q.V → List Bool} (w : Wires q s L enc) {D H x : ℕ} (hs : Stored D s)
    (hb : q.b≤x) (hm : q.m≤x) (hn : q.FB.totalCoords≤x) (hM : bitLen q.M≤x)
    (hd : D≤x) (hh : H≤cutCount x) (hl : L≤tupleWidth x) (z : w3_Label q.M q.FB.totalCoords) :
    Caps kit q s L enc z (s.fuel+H) ((uniform kit x:ℝ)*mainTimeBound kit.contractC q.b)
      (uniform kit x:ℝ) (uniform kit x) := by
  have up := updateBounds (b := q.b) kit hn hM
  refine ⟨?_,up.1,up.2,?_⟩
  · intro r inv f idx saved queried hf hi ha hu
    obtain ⟨ht,ho,hc⟩ := FpTerminalBound.probeBounds kit w hs r inv.1 f idx saved queried hf hi ha hu
    obtain ⟨rt,rs,rc⟩ := probeCosts kit hb hm hn hM hd hh hl
    exact ⟨ht.trans rt,ho.trans rs,hc.trans rc⟩
  · intro r r' h h' f hf X Y
    obtain ⟨h1,h2⟩ := updateLengths w hs r r' h.1 h'.1 f hf X Y
    have hc := updateCapLe kit hd hh hn hM
    exact ⟨h1.trans hc,h2.trans hc⟩

end DetDLP.W3C.FpTailBudget
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpPositiveCuts
open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup
open FpCoordinateWidths FpTerminalBound
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev afterPacket (state : FpState) (pkt : Word) :=
  nextState (packState state) 7 state.idx state.blocksWord state.repWord pkt state.pre

private theorem raiseCall {en de : Port} (kit : Kit en de) {t s τ σ : ℝ}
    (ht : t ≤ τ) (hs : s ≤ σ) {q a : Word} (h : calls kit t s q a) : calls kit τ σ q a := by
  obtain ⟨j,x,hx,run⟩ := h
  exact ⟨j,x,hx,MachineComposition.runsWithin_mono run ht hs⟩

theorem probeTwo {en de : Port} (kit : Kit en de) {q : w3_Query} (hq : w3_fpQueries q)
    {state : FpState} (atBuild : state.phase=6) {τ σ : ℝ} {C n : ℕ} {v a out : Word}
    (redirect : stepFn (pairWord v a) = false :: pairWord (packState state) (tag9 6 q.input))
    (incoming : (pairWord v a).length ≤ C)
    (ht : FpTerminalBound.time kit q ≤ τ) (hs : FpTerminalBound.space kit q ≤ σ)
    (cap : wordLimit kit q (packState state).length 0 ≤ C)
    (cont : ∀ (net : w3_Net q kit.netC) (ans : Word),
      EncodesTruncPoly (w3_precision q) (w3_len q) ans (BTNContract net.G net.T) →
      (pairWord (packState (afterPacket state (w3_packet net))) ans).length ≤ C →
      LoopRuns stepFn (calls kit τ σ) n (packState (afterPacket state (w3_packet net))) ans out (2*C)) :
    LoopRuns stepFn (calls kit τ σ) (n+2) v a out (2*C) := by
  obtain ⟨net,ans,henc,hbuild,hcon,hpkt,hans⟩ := boundedProbe kit hq
  let pkt := w3_packet net
  let next := afterPacket state pkt
  have hx : (packState next).length ≤ (packState state).length+2*pkt.length :=
    updatedLength state atBuild pkt
  change pkt.length ≤ packetLimit kit.buildC q.input.length at hpkt
  change ans.length ≤ answerLimit q at hans
  dsimp only [wordLimit, Nat.zero_add] at cap
  have t6 : (tag9 6 q.input).length = q.input.length+3 := rfl
  have t7 : (tag9 7 pkt).length = pkt.length+4 := rfl
  have b0 : (pairWord v a).length ≤ 2*C := by omega
  have b1 : (pairWord (packState state) (tag9 6 q.input)).length ≤ 2*C := by
    rw [pairLength,t6]; omega
  have b2 : pkt.length ≤ 2*C := by omega
  refine Or.inr ⟨packState state,tag9 6 q.input,pkt,redirect,b0,b1,b2,
    raiseCall kit ht hs hbuild,?_⟩
  apply contract_round state atBuild pkt ans _ (raiseCall kit ht hs hcon)
  · rw [pairLength]; omega
  · change (pairWord (packState next) (tag9 7 pkt)).length ≤ 2*C
    rw [pairLength,t7]; omega
  · omega
  · apply cont net ans henc
    change (pairWord (packState next) ans).length ≤ C
    rw [pairLength]
    omega

end DetDLP.W3C.FpPositiveCuts
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpPositiveCuts
open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup FpCutExec
open FpCoordinateWidths FpTerminalBound
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open private seek_st path_length from Definitions.Def_DetDLP_W3C_FpCutExec

variable {en de : Port} (kit : Kit en de) {q : w3_Query} {s : FpState} {L F C : ℕ}
variable {enc : q.V → Word} {z : w3_Label q.M q.FB.totalCoords} {τ σ : ℝ}
variable (w : Wires q s L enc) (caps : Caps kit q s L enc z F τ σ C)

include w caps in
theorem seekBounded (r : Rep q) (inv : Stage2Trace.Invariant z r) (f : ℕ) (fuel : f ≤ F)
    {out : Word} {n : ℕ}
    (leaf : ∀ v a, stepFn (pairWord v a) = Search q s r f (path q r L) →
      (pairWord v a).length ≤ C → LoopRuns stepFn (calls kit τ σ) n v a out (2*C))
    (k i : ℕ) (ik : i+k=L) (v a : Word)
    (atSeek : stepFn (pairWord v a) = Search q s r f (path q r i)) (incoming : (pairWord v a).length ≤ C) :
    LoopRuns stepFn (calls kit τ σ) (n+2*k) v a out (2*C) := by
  induction k generalizing i v a with
  | zero => simpa using leaf v a (by simpa [← ik] using atSeek) incoming
  | succ k ih =>
    let u := path q r i
    let query := probe q s r (u++[false])
    let b := st s 6 1 f (FpCutExec.repWord r) [] u
    have lu : u.length = i := path_length (q:=q) r i
    have hlen : u.length < 4*(decodeBlocks s.blocksWord).length*S8G.FpMoment.Code.width s.p := by
      rw [w.length,lu]; omega
    have jump : stepFn (pairWord v a) = false :: pairWord (packState b) (tag9 6 query.input) := by
      rw [atSeek]
      simp [Search,seek,emit,call,nextState,st,b,query,probe,u,show (path q r i).length < _ from hlen,queryInput]
    obtain ⟨ht,hs,hc⟩ := caps.probes r inv f 1 u (u++[false]) fuel (by decide) (by omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil, lu]; omega)
    have root := probeTwo kit (q:=query) (state:=b) (w.valid ..) rfl
      (n:=n+2*k) (out:=out) jump incoming ht hs hc
    rw [Nat.mul_succ,← Nat.add_assoc]
    apply root
    intro net ans henc hsize
    let d := st s 7 1 f (FpCutExec.repWord r) (w3_packet net) u
    have hd : afterPacket b (w3_packet net) = d := by
      simp only [afterPacket, nextState, unpackState_packState, b, d, st, show (7 == 8) = false by decide, Bool.cond_false]
    rw [hd] at hsize ⊢
    have next : stepFn (pairWord (packState d) ans) = Search q s r f (path q r (i+1)) := by
      rw [stepFn,child_round net henc d rfl rfl w.modulus rfl]
      apply seek_st
    exact ih (i+1) (by omega) _ _ next hsize

include w caps in
theorem rootSeekBounded (r : Rep q) (inv : Stage2Trace.Invariant z r)
    (pos : 0 < w3_mass (Stage2Trace.root q r)) (f : ℕ) (fuel : f ≤ F) {out : Word} {n : ℕ}
    (leaf : ∀ v a, stepFn (pairWord v a) = Search q s r f (path q r L) →
      (pairWord v a).length ≤ C → LoopRuns stepFn (calls kit τ σ) n v a out (2*C))
    (v a : Word) (root : RootStep (s:=s) r f v a) (incoming : (pairWord v a).length ≤ C) :
    LoopRuns stepFn (calls kit τ σ) (n+2*L+2) v a out (2*C) := by
  let query := probe q s r []
  let b := rootState (s:=s) r f
  obtain ⟨ht,hs,hc⟩ := caps.probes r inv f 0 [] [] fuel (by decide) (by simp) (by simp)
  apply probeTwo kit (q:=query) (state:=b) (w.valid ..) rfl root incoming ht hs hc
  intro net ans henc hsize
  let d := st s 7 0 f (FpCutExec.repWord r) (w3_packet net) []
  have hd : afterPacket b (w3_packet net) = d := by
    simp only [afterPacket, nextState, unpackState_packState, b, rootState, d, st, show (7 == 8) = false by decide, Bool.cond_false]
  rw [hd] at hsize ⊢
  have hp : positive (s.p-1) (w3_packet net) ans = true := by
    rw [w.modulus]
    exact (positive_spec net henc).trans (decide_eq_true pos)
  have seek0 : stepFn (pairWord (packState d) ans) = Search q s r f (path q r 0) := by
    rw [stepFn,round_eq d _ (by decide : 3 ≤ 7)]
    change resume (packState d,ans) = Search q s r f []
    simpa [resume,d,st,hp] using seek_st q s r f 0 (w3_packet net) [] []
  exact seekBounded kit w caps r inv f fuel leaf L 0 (by omega) _ _ seek0 hsize

end DetDLP.W3C.FpPositiveCuts
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpPositiveCuts
open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup FpCutExec
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open private path_length from Definitions.Def_DetDLP_W3C_FpCutExec

theorem positiveUpdate {en de : Port} (kit : Kit en de)
    {q : w3_Query} {s : FpState} {L F C : ℕ} {enc : q.V → Word}
    {z : w3_Label q.M q.FB.totalCoords} {τ σ : ℝ}
    (w : Wires q s L enc) (caps : Caps kit q s L enc z F τ σ C)
    (pass : w3_pass q.FB q.M q.P z) (hM : 2 ≤ q.M) (k f : ℕ) (r : Rep q)
    (inv : Stage2Trace.Invariant z r) (cnt : Nat.card (w3_coset r) ≤ 2^(k+1))
    (pos : 0 < w3_mass (Stage2Trace.root q r)) (fuel : f+1 ≤ F) :
    ∃ (r' : Rep q) (up : FpState), w3_cut q.FB q.M q.P r r' ∧
      Stage2Trace.Invariant z r' ∧ Nat.card (w3_coset r') ≤ 2^k ∧
      RootStep (s:=s) r' (f+1) (packState up) (FpCutExec.repWord r') ∧
      (pairWord (packState up) (FpCutExec.repWord r')).length ≤ C ∧
      ∀ {n : ℕ} {o v a : Word},
        stepFn (pairWord v a) = Search q s r f (path q r L) →
        (pairWord v a).length ≤ C →
        LoopRuns stepFn (calls kit τ σ) n (packState up) (FpCutExec.repWord r') o (2*C) →
        LoopRuns stepFn (calls kit τ σ) (n+1) v a o (2*C) := by
  obtain ⟨X,Y,r',code,cut,inv',cnt',update⟩ := FpRowTrace.positive_row kit
    (Stage2Trace.root q r) w.width w.injective hM z pass r rfl inv cnt pos
    s w.modulus enc w.dimension w.distinct
  let raw := shiftRowCounts (blocks q.FB enc) (words q.FB enc X) (words q.FB enc Y)
  let up := updateStateOf q s enc r (f+1) X Y
  have restart : RootStep (s:=s) r' (f+1) (packState up) (FpCutExec.repWord r') := by
    unfold RootStep stepFn
    rw [round_eq up _ (by decide : 3 ≤ 8)]
    simp [resume,emit,call,up,updateStateOf,st,nextState,rootState,probe,queryInput]
  obtain ⟨queryCap, answerCap⟩ := caps.updates r r' inv inv' (f+1) fuel X Y
  change (pairWord (packState up) (tag9 8 (queryInput 8 up))).length ≤ C at queryCap
  change (pairWord (packState up) (FpCutExec.repWord r')).length ≤ C at answerCap
  refine ⟨r',up,cut,inv',cnt',restart,answerCap,?_⟩
  intro n o v a leaf inputCap tail
  have sendUpdate : stepFn (pairWord v a) =
      false :: pairWord (packState up) (tag9 8 (queryInput 8 up)) := by
    rw [leaf,Search,seek]
    simp only [unpackState_packState,st,w.length,path_length,lt_self_iff_false,if_false]
    change q.code X Y = path q r L at code
    obtain ⟨left,right⟩ := w.tuples X Y
    rw [← code,left,right]
    simp only [w.blocks,w.modulus,emit,call,nextState,unpackState_packState,up,updateStateOf,st]
    rfl
  let u := polyBound kit.updateC (q.FB.totalCoords+bitLen q.M)
  have measured : calls kit u u (tag9 8 (queryInput 8 up)) (FpCutExec.repWord r') := by
    change FpRowTrace.calls kit u u (tag9 8 (queryInput 8
      {s with
        repWord := FpCutExec.repWord r
        pktWord := rowPkt q.M (1 : ZMod q.M).val raw})) (FpCutExec.repWord r') at update
    rw [ZMod.val_one'' (by omega : q.M ≠ 1)] at update
    exact update
  obtain ⟨j,x,tag,run⟩ := measured
  have responseCap : (FpCutExec.repWord r').length ≤ 2*C := by
    rw [FpCoordinateWidths.pairLength] at answerCap
    omega
  exact FpRowExec.call_round sendUpdate (by omega) (by omega) responseCap
    ⟨j,x,tag,MachineComposition.runsWithin_mono run caps.updateTime caps.updateSpace⟩ tail

end DetDLP.W3C.FpPositiveCuts
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpPositiveCuts
open FpOracles FpStep FpTraceStep FpLargeEntry NineOracleLoop BlockLookup FpCutExec
open FpCoordinateWidths FpTerminalBound
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem executeBounded {en de : Port} (kit : Kit en de) {q : w3_Query} {s : FpState} {L F C : ℕ}
    {enc : q.V → Word} {z : w3_Label q.M q.FB.totalCoords} {τ σ : ℝ}
    (w : Wires q s L enc) (caps : Caps kit q s L enc z F τ σ C)
    (pass : w3_pass q.FB q.M q.P z) (hM : 2 ≤ q.M)
    (j : Fin q.FB.totalCoords) (hj : (decodeBlocks s.blocksWord).flatten.length+1=j.val)
    (k : ℕ) (r : Rep q) (inv : Stage2Trace.Invariant z r) (cnt : Nat.card (w3_coset r) ≤ 2^k)
    (f : ℕ) (fuel : f+k ≤ F) (v a : Word) (root : RootStep (s:=s) r f v a)
    (incoming : (pairWord v a).length ≤ C) :
    ∃ n last, n ≤ k ∧ w3_Cuts q.FB q.M q.P n r last ∧ Stage2Trace.Invariant z last ∧
      w3_mass (Stage2Trace.root q last) = 0 ∧
      LoopRuns stepFn (calls kit τ σ) (3+n*(2*L+3)) v a (countWord (last.1 j).val) (2*C) := by
  induction k using Nat.strong_induction_on generalizing r f v a with
  | h k rec =>
    by_cases hz : w3_mass (Stage2Trace.root q r) = 0
    · obtain ⟨_,_,hzero⟩ := zeroRoot kit w r j hj hz f v a root
      obtain ⟨ht,hs,hc⟩ := caps.probes r inv f 0 [] [] (by omega) (by decide) (by simp) (by simp)
      have bound : wordLimit kit (probe q s r []) (packState (rootState (s:=s) r f)).length
          (pairWord v a).length ≤ 2*C := by
        change wordLimit kit (probe q s r []) (packState (rootState (s:=s) r f)).length 0 ≤ C at hc
        dsimp only [wordLimit, Nat.zero_add] at hc ⊢
        omega
      refine ⟨0,r,Nat.zero_le _,.nil r,inv,hz,?_⟩
      simpa only [Nat.zero_mul,Nat.add_zero] using enlarge kit ht hs bound hzero
    · have pos : 0 < w3_mass (Stage2Trace.root q r) := lt_of_le_of_ne (w3c_mass_nonneg _) (Ne.symm hz)
      cases k with
      | zero =>
        obtain ⟨_,_,r',_,cut,hi,_,_⟩ := FpRowTrace.positive_row kit (Stage2Trace.root q r) (k:=0)
          w.width w.injective hM z pass r rfl inv (cnt.trans (by decide)) pos
          s w.modulus enc w.dimension w.distinct
        obtain ⟨_,_,_,_,_,_,half⟩ := cut
        have nonempty : 1 ≤ Nat.card (w3_coset (M:=q.M) r') := (Stage2Trace.card_bounds hi.2).1
        change 2 * Nat.card (w3_coset (M:=q.M) r') ≤ Nat.card (w3_coset (M:=q.M) r) at half
        simp only [pow_zero] at cnt
        exact False.elim (by omega)
      | succ k =>
        obtain ⟨r',up,cut,hi,small,restart,upCap,link⟩ :=
          positiveUpdate kit w caps pass hM k f r inv cnt pos (by omega)
        obtain ⟨n,last,hn,cuts,hi',hz',tail⟩ := rec k (by omega) r' hi small (f+1) (by omega)
          (packState up) (FpCutExec.repWord r') restart upCap
        have run := rootSeekBounded kit w caps r inv pos f (by omega) (n:=3+n*(2*L+3)+1)
          (fun v' a' hstart size => link hstart size tail) v a root incoming
        refine ⟨n+1,last,by omega,.cons cut cuts,hi',hz',?_⟩
        have count : 3+(n+1)*(2*L+3) = (3+n*(2*L+3)+1)+2*L+2 := by ring
        rw [count]
        exact run

end DetDLP.W3C.FpPositiveCuts
end

section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpLargeTrace
open FpOracles FpStep FpTraceStep FpLargeEntry FpCutExec NineOracleLoop BlockLookup
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {en de : Port} (kit : Kit en de)

theorem cuts_subset {q : w3_Query} {n : ℕ} {r l : Rep q}
    (cuts : w3_Cuts q.FB q.M q.P n r l) : w3_coset l ⊆ w3_coset r := by
  induction cuts with
  | nil => exact Set.Subset.rfl
  | cons cut _ ih =>
    obtain ⟨_,_,_,_,_,hu,_⟩ := cut
    exact ih.trans (hu.2.symm ▸ Set.sep_subset ..)

variable {p : ℕ} [Fact p.Prime] [NeZero (p-1)] (g a : (ZMod p)ˣ)
variable (L : Plan p) (B : FpOracles.Blocks p)
open FpBaseCert DetDLP_W1_Queries

end DetDLP.W3C.FpLargeTrace
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpTailBudget

open FpOracles FpStep FpTraceStep FpLargeEntry FpCutExec NineOracleLoop BlockLookup

theorem firstRoot {q : w3_Query} {e : FpState} {L : ℕ} {enc : q.V → Word}
    (w : Wires q e L enc) (phase : e.phase=4) (idx : e.idx=q.FB.totalCoords) (r : Rep q) :
    (decodeBlocks e.blocksWord).flatten.length+1=q.FB.targetCoord.val ∧
    RootStep (q := q) (s := e) r e.fuel (packState e) (FpCutExec.repWord r) := by
  have coord := w.dimension
  have done : (decodeBlocks e.blocksWord).flatten.length+2 ≤ e.idx := coord.le.trans idx.ge
  constructor
  · change (decodeBlocks e.blocksWord).flatten.length+2=q.FB.totalBaseSize+2 at coord
    change _=q.FB.totalBaseSize+1
    omega
  · rw [RootStep,stepFn,FpBaseChain.enterRoot e _ phase done]
    simp [nextState,rootState,probe,st,queryInput]

theorem initialCard {q : w3_Query} {z : w3_Label q.M q.FB.totalCoords} {r : Rep q}
    (inv : Stage2Trace.Invariant z r) : Nat.card (w3_coset r) ≤ 2^(Nat.clog 2 (q.M^q.FB.totalCoords)) :=
  (Stage2Trace.card_bounds inv.2).2.trans (Nat.le_pow_clog (by decide) _)

theorem atZero {q : w3_Query} {n : ℕ} {r last : Rep q} (cuts : w3_Cuts q.FB q.M q.P n r last)
    (zero : w3_mass (Stage2Trace.root q last)=0) :
    last.1 ∈ w3_coset r ∧ w3_pass q.FB q.M q.P last.1 := by
  have inside : last.1 ∈ w3_coset (M := q.M) last := ⟨0,fun i => by simp⟩
  exact ⟨FpLargeTrace.cuts_subset (q := q) cuts inside,w3c_zero_pass (Stage2Trace.root q last) rfl zero⟩

end DetDLP.W3C.FpTailBudget
end

section
set_option autoImplicit false
namespace DetDLP.W3C.FpTailBudget

open FpOracles FpStep FpTraceStep FpBaseCert FpLargeEntry FpCoordinateWidths FpNativeQuery
open FpDriverAssembly FpTerminalBound FpCutExec NineOracleLoop BlockLookup

theorem cutTail {en de : Port} (kit : Kit en de) : CutTail kit := by
  obtain ⟨J,hJ⟩ := budgets kit
  refine ⟨J,?_⟩
  intro p hp _ large seed B hB hN g a e r z ready idx tEq stored inv pass
  let b := bitLen p
  let N := (fb B).totalCoords
  let q := nativeQuery seed B g z []
  let L := 4*m p*b
  let x := size (kitCost kit) b
  let H := Nat.clog 2 ((p-1)^N)
  let D := fieldLimit b (bitLen (p-1)) (m p) N (input g a).length
  let U := uniform kit x
  have ix : N ≤ headSize (kitCost kit) b := hN
  obtain ⟨hb,hm,hn,hM,hd⟩ := fields kit g a ix
  have hh : H ≤ cutCount x := (cutHeight (p-1) N).trans (Nat.mul_le_mul hM hn)
  have hl : L ≤ tupleWidth x := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hm) hb
  have w : Wires q e L enc := nativeWires large seed B g a hB e ready tEq z []
  have caps := assembleCaps (q := q) (D := D) kit w stored hb hm hn hM hd hh hl z
  have hi : e.idx ≤ q.FB.totalCoords := idx.le
  have start := startPairLength (q := q) stored (by rw [ready.phase]; decide) hi r inv.1
  have incoming : (pairWord (packState e) (FpCutExec.repWord r)).length ≤ U := start.trans (initialLe kit hd hn hM)
  have count : Nat.card (w3_coset r) ≤ 2^H := initialCard (q := q) inv
  obtain ⟨coord,root⟩ := firstRoot w ready.phase idx r
  have m2 : 2 ≤ q.M := by change 2 ≤ p-1; have := large.2.1; omega
  obtain ⟨n,last,hc,cuts,_,zero,run⟩ := FpPositiveCuts.executeBounded kit w caps pass m2 (fb B).targetCoord
    coord H r inv count e.fuel (le_refl _) _ _ root incoming
  obtain ⟨inside,valid⟩ := atZero (q := q) cuts zero
  have limits := hJ p hp.out.two_le
  change ((2*U : ℕ):ℝ) ≤ mainSpaceBound J b ∧ (U:ℝ)*mainTimeBound kit.contractC b ≤ mainTimeBound J b at limits
  have roundsCap := roundsLe kit (hc.trans hh) hl
  have natU : U ≤ 2*U := by omega
  have spaceU : (U:ℝ) ≤ mainSpaceBound J b := (by exact_mod_cast natU : (U:ℝ) ≤ ((2*U : ℕ):ℝ)) |>.trans limits.1
  refine ⟨last.1,3+n*(2*L+3),2*U,(U:ℝ)*mainTimeBound kit.contractC b,(U:ℝ),
    inside,valid,
    by omega,mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (time_one ..)),Nat.cast_nonneg _,run,
    ?_,limits.1,limits.2,spaceU⟩
  have hc' : ((3+n*(2*L+3) : ℕ):ℝ) ≤ (U:ℝ) := by exact_mod_cast roundsCap
  exact hc'.trans spaceU

end DetDLP.W3C.FpTailBudget
end

set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution
    (counts : M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_fpQueries) (hupdate : w3_hnfOps) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        let M := p-1
        let m := blockCount (bitLen p)
        orderOf h = M →
          let accepts := fun u => RunsWithin D out (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M (Additive.ofMul h) (Additive.ofMul a) accepts) ∧
          (∀ hg : w3_large p M, letI : NeZero M := ⟨by have := hg.2.1; omega⟩
            ∀ F : Fin m → List (ZMod p)ˣ, w3_fpBaseCalls en eo de do' K F →
              ∃ (seed : FpSeed p m) (B : Fin m → List (ZMod p)ˣ),
                (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p M m M) seed i) ∧
                w3_traceOutput (w3_fpFB F) (w3_fpFB B) M (Additive.ofMul h) (Additive.ofMul a) accepts)  := by
  exact W3C.driverFromCountsOfCutTail counts en eo de do' K hnet hupdate
    (W3C.FpTailBudget.cutTail _)
