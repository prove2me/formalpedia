-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_equal_II_a_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T18:24:11.393589+00:00
-- url     : https://prove2.me/submissions/e63fd675-1ade-4f1d-8733-3f61aeb2dadb

import Definitions.Def_Freiman_middleRepairLedger
import Mathlib.Tactic.NormNum

open Freiman

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

local instance (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) :
    Decidable (middleCertPairValid C p direction) := by
  unfold middleCertPairValid
  infer_instance
local instance (C : MiddleCertCatalog) (p : MiddleCertProof) :
    Decidable (middleCertProofValid C p) := by
  cases p <;> unfold middleCertProofValid <;> infer_instance
local instance (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect)
    (rec : MiddleCertRecord) (parent : ℤ) :
    Decidable (middleRepairRecordValid C redirects rec parent) := by
  unfold middleRepairRecordValid
  infer_instance

namespace Row5D

private theorem bound_eq (C : MiddleCertCatalog) (b : MiddleCertBoundRef) (x : CertBound)
    (hl : x.lower = b.lower) (hs : x.strict = b.strict)
    (ht : x.threshold = middleCertThreshold C b.threshold) : middleCertBound C b = x := by
  rcases x with ⟨xl,xs,xt⟩
  simp only [middleCertBound, CertBound.mk.injEq]
  exact ⟨hl.symm, hs.symm, ht.symm⟩

private theorem strengthen_strict (C : MiddleCertCatalog) (cs : List CertBound)
    (b : MiddleCertBoundRef) (x : CertBound) (hx : x ∈ cs)
    (hl : x.lower = b.lower) (hs : x.strict = true)
    (ht : x.threshold = middleCertThreshold C b.threshold) :
    (middleRepairStrengthen C cs b).strict = true := by
  apply List.any_eq_true.mpr
  exact ⟨x,hx,by simp [hl,hs,ht]⟩

private theorem strengthen_mem (C : MiddleCertCatalog) (cs : List CertBound) (b : MiddleCertBoundRef)
    (hw : ∃ x ∈ cs, x.lower = b.lower ∧ x.threshold = middleCertThreshold C b.threshold) :
    middleCertBound C (middleRepairStrengthen C cs b) ∈ cs := by
  by_cases hh : (middleRepairStrengthen C cs b).strict = true
  · have ha := List.any_eq_true.mp hh
    obtain ⟨x,hx,hp⟩ := ha
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    rw [bound_eq C (middleRepairStrengthen C cs b) x hp.1.1 (hp.1.2.trans hh.symm) hp.2]
    exact hx
  · obtain ⟨x,hx,hl,ht⟩ := hw
    have hs : x.strict = false := by
      apply Bool.eq_false_iff.mpr
      intro ht'
      exact hh (strengthen_strict C cs b x hx hl ht' ht)
    have hh' : (middleRepairStrengthen C cs b).strict = false := Bool.eq_false_iff.mpr hh
    rw [bound_eq C (middleRepairStrengthen C cs b) x hl (hs.trans hh'.symm) ht]
    exact hx

private def refMatches (bs : List MiddleCertBoundRef) (b : MiddleCertBoundRef) : Prop :=
  ∃ x ∈ bs, x.lower = b.lower ∧ x.threshold = b.threshold
private def refStrict (bs : List MiddleCertBoundRef) (b : MiddleCertBoundRef) : Prop :=
  ∃ x ∈ bs, x.lower = b.lower ∧ x.threshold = b.threshold ∧ x.strict = true

private theorem ref_mem (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) (b : MiddleCertBoundRef)
    (hh : refMatches bs b) :
    middleCertBound C (middleRepairStrengthen C (middleCertBounds C bs) b) ∈ middleCertBounds C bs := by
  apply strengthen_mem
  obtain ⟨x,hx,hl,ht⟩ := hh
  refine ⟨middleCertBound C x,List.mem_map.mpr ⟨x,hx,rfl⟩,hl,?_⟩
  simp only [middleCertBound, ht]

private theorem ref_strict (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) (b : MiddleCertBoundRef)
    (hh : refStrict bs b) :
    (middleRepairStrengthen C (middleCertBounds C bs) b).strict = true := by
  obtain ⟨x,hx,hl,ht,hs⟩ := hh
  exact strengthen_strict C _ b (middleCertBound C x) (List.mem_map.mpr ⟨x,hx,rfl⟩) hl hs
    (by simp only [middleCertBound, ht])

private def pairReady (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef)
    (p : MiddleCertPair) (direction : ℤ) : Prop :=
  middleCertPairValid C p direction ∧ refMatches bs p.lowerBound ∧ refMatches bs p.upperBound ∧
    ((direction = 0 ∧ 0 < (middleCertWitness C p.witness).lowerNumerator) ∨
      refStrict bs p.lowerBound ∨ refStrict bs p.upperBound)

private theorem pair_ready (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef)
    (p : MiddleCertPair) (direction : ℤ) (hh : pairReady C bs p direction) :
    middleCertPairValid C (middleRepairAdaptPair C (middleCertBounds C bs) p) direction ∧
      middleCertBound C (middleRepairAdaptPair C (middleCertBounds C bs) p).lowerBound ∈ middleCertBounds C bs ∧
      middleCertBound C (middleRepairAdaptPair C (middleCertBounds C bs) p).upperBound ∈ middleCertBounds C bs := by
  rcases hh with ⟨hv,hl,hu,hstrict⟩
  refine ⟨?_, ref_mem C bs p.lowerBound hl, ref_mem C bs p.upperBound hu⟩
  rcases hv with ⟨h1,h2,h3,h4,h5,h6,h7,_⟩
  refine ⟨h1,h2,h3,h4,h5,h6,h7,?_⟩
  rcases hstrict with hpos | hlow | hupp
  · simpa only [middleRepairAdaptPair, hpos.1, ↓reduceIte] using
      (Or.inl hpos.2 : 0 < (middleCertWitness C p.witness).lowerNumerator ∨
        (middleRepairStrengthen C (middleCertBounds C bs) p.lowerBound).strict = true ∨
        (middleRepairStrengthen C (middleCertBounds C bs) p.upperBound).strict = true)
  · have he := ref_strict C bs p.lowerBound hlow
    dsimp only [middleRepairAdaptPair]
    split_ifs <;> simp [he]
  · have he := ref_strict C bs p.upperBound hupp
    dsimp only [middleRepairAdaptPair]
    split_ifs <;> simp [he]

private def proofReady (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) : MiddleCertProof → Prop
  | .pair p => pairReady C bs p 0
  | .diagonal a b => pairReady C bs a 1 ∧ pairReady C bs b (-1)

private def adaptProof (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) : MiddleCertProof → MiddleCertProof
  | .pair p => .pair (middleRepairAdaptPair C (middleCertBounds C bs) p)
  | .diagonal a b => .diagonal (middleRepairAdaptPair C (middleCertBounds C bs) a)
      (middleRepairAdaptPair C (middleCertBounds C bs) b)

private theorem proof_ready (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) (p : MiddleCertProof)
    (hh : proofReady C bs p) :
    middleCertProofValid C (adaptProof C bs p) ∧
      ∀ q ∈ middleCertProofPairs (adaptProof C bs p),
        middleCertBound C q.lowerBound ∈ middleCertBounds C bs ∧
        middleCertBound C q.upperBound ∈ middleCertBounds C bs := by
  cases p with
  | pair p =>
    have h := pair_ready C bs p 0 hh
    exact ⟨h.1, by simpa only [adaptProof, middleCertProofPairs, List.mem_singleton, forall_eq] using h.2⟩
  | diagonal a b =>
    have ha := pair_ready C bs a 1 hh.1
    have hb := pair_ready C bs b (-1) hh.2
    refine ⟨⟨ha.1,hb.1⟩,?_⟩
    intro q hq
    simp only [adaptProof, middleCertProofPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ha.2
    · exact hb.2


private inductive RefComparison where
  | automatic | impossible | bound (b : MiddleCertBoundRef)
  deriving DecidableEq
private def decodeComparison : RefComparison → LowerHistoryComparison
  | .automatic => .automatic
  | .impossible => .impossible
  | .bound b => .bound (middleCertBound middleCertData b)
private def decodeBranch (p : List MiddleCertBoundRef × RefComparison) : List CertBound × LowerHistoryComparison :=
  (middleCertBounds middleCertData p.1,decodeComparison p.2)

local instance (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) (p : MiddleCertProof) :
    Decidable (proofReady C bs p) := by
  cases p <;> unfold proofReady pairReady refMatches refStrict <;> infer_instance

private theorem wlen : middleCertData.witnesses.length = 1260 := by
  decide +kernel

/-- `middleCertPairValid` with the catalog's witness count replaced by its value, so that
deciding it does not traverse the whole witness list. -/
private def pairOK (p : MiddleCertPair) (direction : ℤ) : Prop :=
  0 < p.witness ∧ p.witness ≤ 1260 ∧
  p.lowerBound.lower = true ∧ p.upperBound.lower = false ∧
  p.lowerBound.threshold = (middleCertWitness middleCertData p.witness).first ∧
  p.upperBound.threshold = (middleCertWitness middleCertData p.witness).second ∧
  (middleCertWitness middleCertData p.witness).direction = direction ∧
  (if direction = 0 then 0 < (middleCertWitness middleCertData p.witness).lowerNumerator ∨
    p.lowerBound.strict = true ∨ p.upperBound.strict = true
   else p.lowerBound.strict = true ∨ p.upperBound.strict = true)

private theorem pairOK_valid (p : MiddleCertPair) (direction : ℤ) (h : pairOK p direction) :
    middleCertPairValid middleCertData p direction := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h8⟩
  rw [wlen]
  exact h2

/-- Part of readiness that does not mention the premise list. -/
private def proofFixed (pf : MiddleCertProof) (pos : Bool) : Prop :=
  match pf with
  | .pair p => pairOK p 0 ∧
      (pos = true → 0 < (middleCertWitness middleCertData p.witness).lowerNumerator)
  | .diagonal a b => pairOK a 1 ∧ pairOK b (-1)

/-- Part of readiness that mentions only the premise list, at the level of references. -/
private def proofFits (bs : List MiddleCertBoundRef) (pf : MiddleCertProof) (pos : Bool) : Prop :=
  match pf with
  | .pair p => refMatches bs p.lowerBound ∧ refMatches bs p.upperBound ∧
      (pos = true ∨ refStrict bs p.lowerBound ∨ refStrict bs p.upperBound)
  | .diagonal a b =>
      ((refMatches bs a.lowerBound ∧ refMatches bs a.upperBound) ∧
        (refStrict bs a.lowerBound ∨ refStrict bs a.upperBound)) ∧
      ((refMatches bs b.lowerBound ∧ refMatches bs b.upperBound) ∧
        (refStrict bs b.lowerBound ∨ refStrict bs b.upperBound))

private instance (p : MiddleCertPair) (direction : ℤ) : Decidable (pairOK p direction) := by
  unfold pairOK
  infer_instance
private instance (pf : MiddleCertProof) (pos : Bool) : Decidable (proofFixed pf pos) := by
  cases pf <;> unfold proofFixed <;> infer_instance
private instance (bs : List MiddleCertBoundRef) (pf : MiddleCertProof) (pos : Bool) :
    Decidable (proofFits bs pf pos) := by
  cases pf <;> unfold proofFits refMatches refStrict <;> infer_instance

private theorem fits_ready (bs : List MiddleCertBoundRef)
    (pf : MiddleCertProof) (pos : Bool)
    (hx : proofFixed pf pos) (hy : proofFits bs pf pos) :
    proofReady middleCertData bs pf := by
  cases pf with
  | pair p =>
    obtain ⟨hv, hn⟩ := hx
    obtain ⟨hl, hu, hs⟩ := hy
    refine ⟨pairOK_valid p 0 hv, hl, hu, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl ⟨rfl, hn hs⟩
    · exact Or.inr hs
  | diagonal a b =>
    obtain ⟨hva, hvb⟩ := hx
    obtain ⟨⟨⟨hla, hua⟩, hsa⟩, ⟨⟨hlb, hub⟩, hsb⟩⟩ := hy
    exact ⟨⟨pairOK_valid a 1 hva, hla, hua, Or.inr hsa⟩,
      ⟨pairOK_valid b (-1) hvb, hlb, hub, Or.inr hsb⟩⟩

/-- A record together with the cached data attached to its goal and branch. -/
private structure Row where
  record : MiddleCertRecord
  hyp : List MiddleCertBoundRef
  brc : List MiddleCertBoundRef
  cmp : RefComparison
  prf : MiddleCertProof
  pos : Bool
  pars : List ℤ
  excl : List ℤ

private def branches_83 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],(.bound ⟨true,false,538⟩)),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],(.bound ⟨true,false,538⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,580⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,580⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,763⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],(.bound ⟨false,false,639⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],(.bound ⟨false,false,560⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,763⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],(.bound ⟨false,false,639⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],(.bound ⟨false,false,560⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic)
]

private def branches_84 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],(.bound ⟨false,false,645⟩)),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],(.bound ⟨false,false,635⟩)),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],(.bound ⟨true,false,645⟩)),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],(.bound ⟨true,false,635⟩)),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],(.bound ⟨false,false,645⟩)),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],(.bound ⟨false,false,635⟩)),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],(.bound ⟨true,false,645⟩)),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],(.bound ⟨true,false,635⟩)),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.automatic)
]

private def branches_85 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic)
]

private def branches_86 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,221⟩,⟨true,false,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,442⟩)),
([⟨false,false,221⟩,⟨true,false,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,385⟩)),
([⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩)),
([⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩)),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩)),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩)),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩)),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩)),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,331⟩)),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,353⟩)),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,368⟩)),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,270⟩)),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,428⟩)),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,397⟩)),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,389⟩)),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,421⟩))
]

private def branches_87 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,613⟩,⟨true,false,528⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,284⟩)),
([⟨false,true,613⟩,⟨true,false,528⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,244⟩)),
([⟨false,true,613⟩,⟨true,false,528⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,228⟩)),
([⟨false,true,613⟩,⟨true,false,528⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,256⟩)),
([⟨false,true,613⟩,⟨false,true,528⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,371⟩)),
([⟨false,true,613⟩,⟨false,true,528⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,722⟩)),
([⟨false,true,613⟩,⟨false,true,528⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,647⟩)),
([⟨false,true,613⟩,⟨false,true,528⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,281⟩)),
([⟨true,false,613⟩,⟨false,false,579⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,343⟩)),
([⟨true,false,613⟩,⟨false,false,579⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,720⟩)),
([⟨true,false,613⟩,⟨false,false,579⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,592⟩)),
([⟨true,false,613⟩,⟨false,false,579⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,349⟩)),
([⟨true,false,613⟩,⟨true,true,579⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,257⟩)),
([⟨true,false,613⟩,⟨true,true,579⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,99⟩)),
([⟨true,false,613⟩,⟨true,true,579⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,362⟩)),
([⟨true,false,613⟩,⟨true,true,579⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,242⟩))
]

private def branches_88 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic)
]

private def branches_89 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,254⟩,⟨true,false,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,468⟩)),
([⟨false,false,254⟩,⟨true,false,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,390⟩)),
([⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩)),
([⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩)),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩)),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩)),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩)),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩)),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,294⟩)),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,332⟩)),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,358⟩)),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,214⟩)),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,448⟩)),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,407⟩)),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,396⟩)),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,441⟩))
]

private def branches_90 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,640⟩,⟨true,false,612⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,258⟩)),
([⟨false,true,640⟩,⟨true,false,612⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,191⟩)),
([⟨false,true,640⟩,⟨true,false,612⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,179⟩)),
([⟨false,true,640⟩,⟨true,false,612⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,219⟩)),
([⟨false,true,640⟩,⟨false,true,612⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,398⟩)),
([⟨false,true,640⟩,⟨false,true,612⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,725⟩)),
([⟨false,true,640⟩,⟨false,true,612⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,706⟩)),
([⟨false,true,640⟩,⟨false,true,612⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,164⟩)),
([⟨true,false,640⟩,⟨false,false,675⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,324⟩)),
([⟨true,false,640⟩,⟨false,false,675⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,709⟩)),
([⟨true,false,640⟩,⟨false,false,675⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,657⟩)),
([⟨true,false,640⟩,⟨false,false,675⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,301⟩)),
([⟨true,false,640⟩,⟨true,true,675⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,220⟩)),
([⟨true,false,640⟩,⟨true,true,675⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,158⟩)),
([⟨true,false,640⟩,⟨true,true,675⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,380⟩)),
([⟨true,false,640⟩,⟨true,true,675⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,196⟩))
]

private def branches_91 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],.automatic)
]

private def branches_92 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,223⟩,⟨true,false,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,524⟩)),
([⟨false,false,223⟩,⟨true,false,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,404⟩)),
([⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩)),
([⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩)),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩)),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩)),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩)),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩)),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,218⟩)),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,290⟩)),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,335⟩)),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,106⟩)),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,499⟩)),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,425⟩)),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,412⟩)),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,484⟩))
]

private def branches_93 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,200⟩)),
([⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,128⟩)),
([⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,115⟩)),
([⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,153⟩)),
([⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,236⟩)),
([⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,15⟩)),
([⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,11⟩)),
([⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,716⟩)),
([⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,267⟩)),
([⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,746⟩)),
([⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,731⟩)),
([⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,121⟩)),
([⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,154⟩)),
([⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,208⟩)),
([⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,476⟩)),
([⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,130⟩))
]

private def branches_94 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩)),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩)),
([⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩)),
([⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩)),
([⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩))
]

private def branches_95 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],.automatic)
]

private def branches_96 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩)),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩)),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩)),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩)),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩))
]

private def branches_97 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],.automatic)
]

private def parentRefs : List (List MiddleCertBoundRef) := [
  [⟨true,false,583⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,416⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,561⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,583⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,416⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,561⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,117⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,147⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,70⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,117⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,147⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,70⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,161⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,202⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,74⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,161⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,202⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,74⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,546⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,463⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,530⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,546⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,463⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,530⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,583⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,416⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,561⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,583⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,416⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,561⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,117⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,147⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,70⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,117⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,147⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,70⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,161⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,202⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,74⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,161⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,202⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,74⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨true,false,546⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
  [⟨true,false,463⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],
  [⟨true,false,530⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],
  [⟨true,false,546⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],
  [⟨true,false,463⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],
  [⟨true,false,530⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],
  [⟨false,false,48⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,314⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,213⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,34⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,48⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,314⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,213⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,34⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,17⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,31⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,21⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,718⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,17⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,31⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,21⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,718⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨false,false,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,19⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,762⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,753⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,123⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,19⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,762⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,753⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,123⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,35⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,239⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,438⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,24⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,35⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,239⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,438⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,24⟩,⟨true,true,633⟩,⟨false,true,695⟩,⟨true,true,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,48⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,314⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,213⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,34⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,48⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,314⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,213⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,34⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,17⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,31⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,21⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,718⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,17⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,31⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,21⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,718⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,19⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,762⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,753⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,123⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,19⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,762⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,753⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,123⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],
  [⟨false,false,35⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],
  [⟨false,false,239⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨false,false,438⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],
  [⟨false,false,24⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],
  [⟨false,false,35⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],
  [⟨false,false,239⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],
  [⟨false,false,438⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],
  [⟨false,false,24⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩]
]

private theorem parents_eq :
    middleRepairCertParents false = parentRefs.map (middleCertBounds middleCertData) := by
  decide +kernel

private def cachedBranches (g : ℕ) : List (List MiddleCertBoundRef × RefComparison) :=
  if g = 83 then branches_83 else
  if g = 84 then branches_84 else
  if g = 85 then branches_85 else
  if g = 86 then branches_86 else
  if g = 87 then branches_87 else
  if g = 88 then branches_88 else
  if g = 89 then branches_89 else
  if g = 90 then branches_90 else
  if g = 91 then branches_91 else
  if g = 92 then branches_92 else
  if g = 93 then branches_93 else
  if g = 94 then branches_94 else
  if g = 95 then branches_95 else
  if g = 96 then branches_96 else
  if g = 97 then branches_97 else
  []

private def selectedGoals : List ℕ := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]

private theorem branches_eq_all : ∀ g ∈ selectedGoals,
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData g)
      = (cachedBranches g).map decodeBranch := by
  decide +kernel

private def refComplement (b : MiddleCertBoundRef) : MiddleCertBoundRef :=
  ⟨!b.lower, !b.strict, b.threshold⟩

private def rowConds (r : Row) (parent : ℤ) : List MiddleCertBoundRef :=
  r.hyp ++ r.brc ++ (if parent < 0 then [] else parentRefs[parent.toNat]?.getD []) ++
    (match r.cmp with | .bound t => [refComplement t] | _ => [])

private theorem conditions_eq (r : Row) (parent : ℤ)
    (hg : r.record.goal ∈ selectedGoals)
    (hh : (middleCertGoal middleCertData r.record.goal).hypotheses = r.hyp)
    (hb : (cachedBranches r.record.goal)[r.record.branch]?.getD ([], RefComparison.impossible)
      = (r.brc, r.cmp))
    (hpar : middleCertParity (middleCertGoal middleCertData r.record.goal).family = false) :
    middleRepairCertConditions middleCertData r.record parent
      = middleCertBounds middleCertData (rowConds r parent) := by
  have hbr := branches_eq_all r.record.goal hg
  have hget : ((cachedBranches r.record.goal).map decodeBranch)[r.record.branch]?.getD ([], .impossible)
      = decodeBranch ((cachedBranches r.record.goal)[r.record.branch]?.getD
        ([], RefComparison.impossible)) := by
    simp only [List.getElem?_map]
    exact Option.getD_map decodeBranch ([], RefComparison.impossible)
      ((cachedBranches r.record.goal)[r.record.branch]?)
  have hpget : (parentRefs.map (middleCertBounds middleCertData))[parent.toNat]?.getD []
      = middleCertBounds middleCertData (parentRefs[parent.toNat]?.getD []) := by
    simp only [List.getElem?_map]
    exact Option.getD_map (middleCertBounds middleCertData) [] (parentRefs[parent.toNat]?)
  simp only [middleRepairCertConditions, middleRepairCertBranch, hbr, hget, hb, decodeBranch,
    hpar, parents_eq, hpget, rowConds, hh, middleCertBounds, List.map_append]
  split_ifs <;> cases hcmp : r.cmp <;>
    simp [hcmp, decodeComparison, middleCertBounds, refComplement, middleCertBound,
      lowerHistoryComplement]

private def rowGood (r : Row) : Prop :=
  r.record.goal ∈ selectedGoals ∧
  (middleCertGoal middleCertData r.record.goal).hypotheses = r.hyp ∧
  (cachedBranches r.record.goal)[r.record.branch]?.getD ([], RefComparison.impossible) = (r.brc, r.cmp) ∧
  middleCertParity (middleCertGoal middleCertData r.record.goal).family = false ∧
  middleCertProof middleCertData r.record.proof = r.prf ∧
  proofFixed r.prf r.pos ∧
  (∀ parent ∈ r.record.parents, parent ∈ r.pars ∨ parent ∈ r.excl) ∧
  (∀ parent ∈ r.excl,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a r.record parent) ≠ none) ∧
  ∀ parent ∈ r.pars, proofFits (rowConds r parent) r.prf r.pos

private instance (r : Row) : Decidable (rowGood r) := by
  unfold rowGood
  infer_instance

private theorem from_row (r : Row) (parent : ℤ) (hr : rowGood r) (hp : parent ∈ r.record.parents)
    (hn : middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a r.record parent) = none) :
    middleRepairRecordValid middleCertData middleRepairRedirects r.record parent := by
  obtain ⟨hg, hh, hb, hpar, hpf, hx, hsplit, hexcl, hy⟩ := hr
  have hin : parent ∈ r.pars := by
    rcases hsplit parent hp with h | h
    · exact h
    · exact absurd hn (hexcl parent h)
  have hc : middleRepairCertConditions middleCertData r.record parent
      = middleCertBounds middleCertData (rowConds r parent) := conditions_eq r parent hg hh hb hpar
  have hready : proofReady middleCertData (rowConds r parent)
      (middleCertProof middleCertData r.record.proof) := by
    rw [hpf]
    exact fits_ready _ _ _ hx (hy parent hin)
  have he : middleRepairEffectiveProof middleCertData middleRepairRedirects r.record parent
      = adaptProof middleCertData (rowConds r parent)
        (middleCertProof middleCertData r.record.proof) := by
    simp only [middleRepairEffectiveProof, hn, hc]
    cases middleCertProof middleCertData r.record.proof <;> rfl
  simpa only [middleRepairRecordValid, he, hc] using proof_ready _ _ _ hready

private def chunk_0 : List Row := [
⟨⟨83,8,[10,42],29⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,false,203⟩,⟨false,false,221⟩,165⟩),true,[10,42],[]⟩,
⟨⟨83,8,[9,41],51⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,false,147⟩,⟨false,false,221⟩,98⟩),true,[9,41],[]⟩,
⟨⟨83,8,[2,34],107⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,false,376⟩,⟨false,false,221⟩,323⟩),true,[2,34],[]⟩,
⟨⟨83,8,[8,40],149⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,false,117⟩,⟨false,false,221⟩,66⟩),true,[8,40],[]⟩,
⟨⟨83,8,[0,32],184⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,false,583⟩,⟨false,false,221⟩,776⟩),true,[0,32],[]⟩,
⟨⟨83,8,[1,3,33,35],503⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,false,433⟩,⟨false,false,221⟩,424⟩),true,[1,3,33,35],[]⟩,
⟨⟨83,8,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],541⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,true,296⟩,⟨false,false,221⟩,260⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨83,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨83,8,[11,43],859⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,true,569⟩,⟨false,false,221⟩,674⟩),true,[11,43],[]⟩,
⟨⟨83,8,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],954⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,true,453⟩,⟨false,false,221⟩,486⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨83,8,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1201⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,false,221⟩,1003⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨83,10,[10,42],32⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,false,203⟩,⟨false,false,591⟩,180⟩),true,[10,42],[]⟩,
⟨⟨83,10,[9,41],58⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,false,147⟩,⟨false,false,591⟩,131⟩),true,[9,41],[]⟩,
⟨⟨83,10,[2,34],110⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,false,376⟩,⟨false,false,591⟩,338⟩),true,[2,34],[]⟩,
⟨⟨83,10,[8,40],153⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,false,117⟩,⟨false,false,591⟩,85⟩),true,[8,40],[]⟩,
⟨⟨83,10,[0,32],193⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,false,583⟩,⟨false,false,591⟩,811⟩),true,[0,32],[]⟩,
⟨⟨83,10,[1,3,33,35],510⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,false,433⟩,⟨false,false,591⟩,449⟩),true,[1,3,33,35],[]⟩,
⟨⟨83,10,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],548⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,true,296⟩,⟨false,false,591⟩,284⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨83,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨83,10,[11,43],864⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,true,569⟩,⟨false,false,591⟩,691⟩),true,[11,43],[]⟩,
⟨⟨83,10,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],961⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,true,453⟩,⟨false,false,591⟩,510⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨83,10,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1213⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,false,591⟩,1038⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨83,11,[-1],903⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],(.bound ⟨true,false,538⟩),(.pair ⟨⟨true,true,591⟩,⟨false,true,538⟩,817⟩),true,[-1],[]⟩,
⟨⟨83,12,[-1],583⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],.impossible,(.pair ⟨⟨true,true,215⟩,⟨false,false,221⟩,181⟩),true,[-1],[]⟩,
⟨⟨83,14,[-1],584⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],.impossible,(.pair ⟨⟨true,true,215⟩,⟨false,false,591⟩,185⟩),true,[-1],[]⟩,
⟨⟨83,15,[-1],586⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨true,true,591⟩],(.bound ⟨true,false,538⟩),(.pair ⟨⟨true,true,215⟩,⟨false,true,538⟩,184⟩),true,[-1],[]⟩,
⟨⟨83,16,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,580⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,20,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,580⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,24,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,763⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,25,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],(.bound ⟨false,false,639⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,26,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],(.bound ⟨false,false,560⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,28,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨true,false,535⟩],(.bound ⟨false,false,763⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,29,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨false,true,221⟩,⟨false,true,535⟩],(.bound ⟨false,false,639⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨83,30,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨true,false,221⟩,⟨false,false,591⟩],(.bound ⟨false,false,560⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,1,[-1],407⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible,(.pair ⟨⟨true,false,601⟩,⟨false,true,601⟩,837⟩),false,[-1],[]⟩,
⟨⟨84,2,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],(.bound ⟨false,false,645⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,3,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,7,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],(.bound ⟨false,false,635⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,8,[-1],745⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],(.bound ⟨true,false,645⟩),(.pair ⟨⟨true,true,634⟩,⟨false,false,629⟩,1054⟩),true,[-1],[]⟩,
⟨⟨84,9,[-1],745⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible,(.pair ⟨⟨true,true,634⟩,⟨false,false,629⟩,1054⟩),true,[-1],[]⟩,
⟨⟨84,11,[-1],1137⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible,(.pair ⟨⟨true,true,664⟩,⟨false,false,664⟩,1100⟩),false,[-1],[]⟩,
⟨⟨84,13,[-1],1138⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],(.bound ⟨true,false,635⟩),(.pair ⟨⟨true,true,664⟩,⟨false,false,629⟩,1099⟩),true,[-1],[]⟩,
⟨⟨84,17,[-1],407⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible,(.pair ⟨⟨true,false,601⟩,⟨false,true,601⟩,837⟩),false,[-1],[]⟩,
⟨⟨84,18,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],(.bound ⟨false,false,645⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,19,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,23,[-1],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],(.bound ⟨false,false,635⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨84,24,[-1],749⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],(.bound ⟨true,false,645⟩),(.pair ⟨⟨true,true,634⟩,⟨false,true,534⟩,1049⟩),true,[-1],[]⟩,
⟨⟨84,25,[-1],749⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible,(.pair ⟨⟨true,true,634⟩,⟨false,true,534⟩,1049⟩),true,[-1],[]⟩,
⟨⟨84,27,[-1],1137⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible,(.pair ⟨⟨true,true,664⟩,⟨false,false,664⟩,1100⟩),false,[-1],[]⟩,
⟨⟨84,29,[-1],1139⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,629⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],(.bound ⟨true,false,635⟩),(.pair ⟨⟨true,true,664⟩,⟨false,true,534⟩,1096⟩),true,[-1],[]⟩,
⟨⟨86,0,[-1],533⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,442⟩),(.pair ⟨⟨true,false,382⟩,⟨false,false,348⟩,352⟩),true,[-1],[]⟩,
⟨⟨86,1,[-1],534⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,385⟩),(.pair ⟨⟨true,false,382⟩,⟨false,true,414⟩,353⟩),true,[-1],[]⟩,
⟨⟨86,2,[10,42],33⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,435⟩,174⟩),true,[10,42],[]⟩,
⟨⟨86,2,[9,41],59⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,435⟩,115⟩),true,[9,41],[]⟩,
⟨⟨86,2,[2,34],111⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,435⟩,332⟩),true,[2,34],[]⟩,
⟨⟨86,2,[8,40],154⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,435⟩,76⟩),true,[8,40],[]⟩,
⟨⟨86,2,[0,32],194⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,435⟩,794⟩),true,[0,32],[]⟩,
⟨⟨86,2,[1,3,33,35],511⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,435⟩,437⟩),true,[1,3,33,35],[]⟩,
⟨⟨86,2,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],549⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,435⟩,273⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨86,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨86,2,[11,43],865⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,435⟩,684⟩),true,[11,43],[]⟩,
⟨⟨86,2,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],962⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,435⟩,498⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨86,2,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1214⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,381⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,435⟩,1021⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨86,3,[10,42],41⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,436⟩,175⟩),true,[10,42],[]⟩,
⟨⟨86,3,[9,41],74⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,436⟩,116⟩),true,[9,41],[]⟩,
⟨⟨86,3,[2,34],118⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,436⟩,333⟩),true,[2,34],[]⟩,
⟨⟨86,3,[8,40],164⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,436⟩,77⟩),true,[8,40],[]⟩,
⟨⟨86,3,[0,32],210⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,436⟩,795⟩),true,[0,32],[]⟩,
⟨⟨86,3,[1,3,33,35],520⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,436⟩,438⟩),true,[1,3,33,35],[]⟩,
⟨⟨86,3,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],559⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,436⟩,274⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨86,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨86,3,[11,43],872⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,436⟩,685⟩),true,[11,43],[]⟩,
⟨⟨86,3,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],972⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,436⟩,499⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨86,3,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1229⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨true,false,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,436⟩,1022⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨86,4,[10,42],31⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,348⟩,169⟩),true,[10,42],[]⟩,
⟨⟨86,4,[9,41],54⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,348⟩,108⟩),true,[9,41],[]⟩,
⟨⟨86,4,[2,34],109⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,348⟩,327⟩),true,[2,34],[]⟩,
⟨⟨86,4,[8,40],151⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,348⟩,71⟩),true,[8,40],[]⟩,
⟨⟨86,4,[0,32],187⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,348⟩,787⟩),true,[0,32],[]⟩,
⟨⟨86,4,[1,3,33,35],507⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,348⟩,431⟩),true,[1,3,33,35],[]⟩,
⟨⟨86,4,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],545⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,348⟩,268⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨86,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨86,4,[11,43],862⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,348⟩,679⟩),true,[11,43],[]⟩,
⟨⟨86,4,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],958⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,348⟩,493⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨86,4,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1206⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,306⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,348⟩,1014⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨86,5,[10,42],44⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,414⟩,172⟩),true,[10,42],[]⟩,
⟨⟨86,5,[9,41],81⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,414⟩,112⟩),true,[9,41],[]⟩,
⟨⟨86,5,[2,34],121⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,414⟩,330⟩),true,[2,34],[]⟩,
⟨⟨86,5,[8,40],167⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,414⟩,74⟩),true,[8,40],[]⟩,
⟨⟨86,5,[0,32],215⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,414⟩,791⟩),true,[0,32],[]⟩,
⟨⟨86,5,[1,3,33,35],525⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,414⟩,434⟩),true,[1,3,33,35],[]⟩,
⟨⟨86,5,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],563⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,414⟩,271⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨86,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨86,5,[11,43],875⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,414⟩,682⟩),true,[11,43],[]⟩,
⟨⟨86,5,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],976⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,414⟩,496⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨86,5,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1236⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,414⟩,1018⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩
]

private theorem good_0 : ∀ r ∈ chunk_0, rowGood r := by
  decide +kernel

private def chunk_1 : List Row := [
⟨⟨86,6,[10,42],46⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,382⟩,171⟩),true,[10,42],[]⟩,
⟨⟨86,6,[9,41],83⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,382⟩,111⟩),true,[9,41],[]⟩,
⟨⟨86,6,[2,34],123⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,382⟩,329⟩),true,[2,34],[]⟩,
⟨⟨86,6,[8,40],169⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,382⟩,73⟩),true,[8,40],[]⟩,
⟨⟨86,6,[0,32],217⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,382⟩,790⟩),true,[0,32],[]⟩,
⟨⟨86,6,[1,3,33,35],528⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,382⟩,433⟩),true,[1,3,33,35],[]⟩,
⟨⟨86,6,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],565⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,382⟩,270⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨86,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨86,6,[11,43],877⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,382⟩,681⟩),true,[11,43],[]⟩,
⟨⟨86,6,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],978⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,382⟩,495⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨86,6,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1238⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,382⟩,1017⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨86,7,[10,42],39⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,262⟩,167⟩),true,[10,42],[]⟩,
⟨⟨86,7,[9,41],70⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,262⟩,102⟩),true,[9,41],[]⟩,
⟨⟨86,7,[2,34],116⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,262⟩,325⟩),true,[2,34],[]⟩,
⟨⟨86,7,[8,40],160⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,262⟩,68⟩),true,[8,40],[]⟩,
⟨⟨86,7,[0,32],205⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,262⟩,781⟩),true,[0,32],[]⟩,
⟨⟨86,7,[1,3,33,35],517⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,262⟩,428⟩),true,[1,3,33,35],[]⟩,
⟨⟨86,7,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],555⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,262⟩,264⟩),true,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],[]⟩,
⟨⟨86,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨86,7,[11,43],870⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,262⟩,677⟩),true,[11,43],[]⟩,
⟨⟨86,7,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],968⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,262⟩,490⟩),true,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨86,7,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1225⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,262⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,262⟩,1009⟩),true,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],[]⟩,
⟨⟨86,8,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨false,false,384⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,331⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨86,9,[-1],630⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨false,false,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,414⟩,193⟩),true,[-1],[]⟩,
⟨⟨86,10,[-1],624⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,368⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,435⟩,195⟩),true,[-1],[]⟩,
⟨⟨86,11,[-1],627⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,270⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,270⟩,188⟩),true,[-1],[]⟩,
⟨⟨86,12,[-1],1185⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨true,true,384⟩,⟨false,false,348⟩,⟨true,false,414⟩],(.bound ⟨true,false,428⟩),(.pair ⟨⟨true,true,384⟩,⟨false,false,348⟩,354⟩),true,[-1],[]⟩,
⟨⟨86,13,[-1],1187⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨true,true,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],(.bound ⟨true,false,397⟩),(.pair ⟨⟨true,true,384⟩,⟨false,true,414⟩,355⟩),true,[-1],[]⟩,
⟨⟨86,14,[-1],1186⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],(.bound ⟨true,false,389⟩),(.pair ⟨⟨true,true,384⟩,⟨false,false,435⟩,357⟩),true,[-1],[]⟩,
⟨⟨86,15,[-1],1188⟩,[⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],(.bound ⟨true,false,421⟩),(.pair ⟨⟨true,true,384⟩,⟨false,true,421⟩,356⟩),true,[-1],[]⟩,
⟨⟨87,0,[-1],337⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨true,false,528⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,284⟩),(.pair ⟨⟨true,false,528⟩,⟨false,false,264⟩,549⟩),true,[-1],[]⟩,
⟨⟨87,1,[-1],339⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨true,false,528⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,244⟩),(.pair ⟨⟨true,false,528⟩,⟨false,true,596⟩,554⟩),true,[-1],[]⟩,
⟨⟨87,2,[-1],341⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨true,false,528⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,228⟩),(.pair ⟨⟨true,false,528⟩,⟨false,true,534⟩,551⟩),true,[-1],[]⟩,
⟨⟨87,3,[-1],922⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨true,false,528⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,256⟩),(.pair ⟨⟨true,true,655⟩,⟨false,true,534⟩,1093⟩),true,[-1],[]⟩,
⟨⟨87,4,[-1],609⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨false,true,528⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,371⟩),(.pair ⟨⟨true,true,371⟩,⟨false,false,264⟩,311⟩),true,[-1],[]⟩,
⟨⟨87,5,[-1],1183⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨false,true,528⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,722⟩),(.pair ⟨⟨true,true,722⟩,⟨false,true,596⟩,1193⟩),true,[-1],[]⟩,
⟨⟨87,6,[-1],775⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨false,true,528⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,647⟩),(.pair ⟨⟨true,true,647⟩,⟨false,true,534⟩,1088⟩),true,[-1],[]⟩,
⟨⟨87,7,[-1],602⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,613⟩,⟨false,true,528⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,281⟩),(.pair ⟨⟨true,true,281⟩,⟨false,true,534⟩,251⟩),true,[-1],[]⟩,
⟨⟨87,8,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨false,false,579⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,343⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨87,9,[-1],843⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨false,false,579⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,720⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,596⟩,976⟩),true,[-1],[]⟩,
⟨⟨87,10,[-1],846⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨false,false,579⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,592⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,534⟩,971⟩),true,[-1],[]⟩,
⟨⟨87,11,[-1],846⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨false,false,579⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,349⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,534⟩,971⟩),true,[-1],[]⟩,
⟨⟨87,12,[-1],1108⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨true,true,579⟩,⟨false,true,264⟩,⟨true,false,596⟩],(.bound ⟨false,false,257⟩),(.pair ⟨⟨true,true,579⟩,⟨false,false,264⟩,763⟩),true,[-1],[]⟩,
⟨⟨87,13,[-1],1110⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨true,true,579⟩,⟨false,true,264⟩,⟨false,true,596⟩],(.bound ⟨false,false,99⟩),(.pair ⟨⟨true,true,579⟩,⟨false,true,596⟩,769⟩),true,[-1],[]⟩,
⟨⟨87,14,[-1],1112⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨true,true,579⟩,⟨true,false,264⟩,⟨false,false,655⟩],(.bound ⟨false,false,362⟩),(.pair ⟨⟨true,true,579⟩,⟨false,true,534⟩,766⟩),true,[-1],[]⟩,
⟨⟨87,15,[-1],1112⟩,[⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,613⟩,⟨true,true,579⟩,⟨true,false,264⟩,⟨true,true,655⟩],(.bound ⟨false,false,242⟩),(.pair ⟨⟨true,true,579⟩,⟨false,true,534⟩,766⟩),true,[-1],[]⟩,
⟨⟨89,0,[-1],87⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,468⟩),(.pair ⟨⟨true,false,375⟩,⟨false,false,321⟩,318⟩),true,[-1],[]⟩,
⟨⟨89,1,[-1],88⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,390⟩),(.pair ⟨⟨true,false,375⟩,⟨false,true,434⟩,319⟩),true,[-1],[]⟩,
⟨⟨89,2,[10],35⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,454⟩,176⟩),true,[10],[]⟩,
⟨⟨89,2,[9],62⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,454⟩,119⟩),true,[9],[]⟩,
⟨⟨89,2,[2],113⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,454⟩,334⟩),true,[2],[]⟩,
⟨⟨89,2,[8],156⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,454⟩,78⟩),true,[8],[]⟩,
⟨⟨89,2,[0],198⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,454⟩,798⟩),true,[0],[]⟩,
⟨⟨89,2,[1,3],513⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,454⟩,439⟩),true,[1,3],[]⟩,
⟨⟨89,2,[16,17,18,19,20,21,22,23],551⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,454⟩,275⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨89,2,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨89,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨89,2,[11],867⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,454⟩,686⟩),true,[11],[]⟩,
⟨⟨89,2,[24,25,26,27,28,29,30,31],964⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,454⟩,500⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨89,2,[4,5,6,7,12,13,14,15],1217⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,383⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,454⟩,1025⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨89,3,[10],45⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,458⟩,177⟩),true,[10],[]⟩,
⟨⟨89,3,[9],82⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,458⟩,120⟩),true,[9],[]⟩,
⟨⟨89,3,[2],122⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,458⟩,335⟩),true,[2],[]⟩,
⟨⟨89,3,[8],168⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,458⟩,79⟩),true,[8],[]⟩,
⟨⟨89,3,[0],216⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,458⟩,799⟩),true,[0],[]⟩,
⟨⟨89,3,[1,3],527⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,458⟩,440⟩),true,[1,3],[]⟩,
⟨⟨89,3,[16,17,18,19,20,21,22,23],564⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,458⟩,276⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨89,3,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨89,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨89,3,[11],876⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,458⟩,687⟩),true,[11],[]⟩,
⟨⟨89,3,[24,25,26,27,28,29,30,31],977⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,458⟩,501⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨89,3,[4,5,6,7,12,13,14,15],1237⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨true,false,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,458⟩,1026⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨89,4,[10],30⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,321⟩,168⟩),true,[10],[]⟩,
⟨⟨89,4,[9],52⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,321⟩,104⟩),true,[9],[]⟩,
⟨⟨89,4,[2],108⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,321⟩,326⟩),true,[2],[]⟩,
⟨⟨89,4,[8],150⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,321⟩,69⟩),true,[8],[]⟩,
⟨⟨89,4,[0],185⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,321⟩,783⟩),true,[0],[]⟩,
⟨⟨89,4,[1,3],506⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,321⟩,429⟩),true,[1,3],[]⟩,
⟨⟨89,4,[16,17,18,19,20,21,22,23],544⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,321⟩,266⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨89,4,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨89,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨89,4,[11],861⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,321⟩,678⟩),true,[11],[]⟩,
⟨⟨89,4,[24,25,26,27,28,29,30,31],957⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,321⟩,491⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨89,4,[4,5,6,7,12,13,14,15],1204⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,261⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,321⟩,1011⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨89,5,[10],43⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,434⟩,173⟩),true,[10],[]⟩,
⟨⟨89,5,[9],80⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,434⟩,114⟩),true,[9],[]⟩,
⟨⟨89,5,[2],120⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,434⟩,331⟩),true,[2],[]⟩,
⟨⟨89,5,[8],166⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,434⟩,75⟩),true,[8],[]⟩,
⟨⟨89,5,[0],214⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,434⟩,793⟩),true,[0],[]⟩,
⟨⟨89,5,[1,3],523⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,434⟩,436⟩),true,[1,3],[]⟩,
⟨⟨89,5,[16,17,18,19,20,21,22,23],562⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,434⟩,272⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨89,5,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨89,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨89,5,[11],874⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,434⟩,683⟩),true,[11],[]⟩,
⟨⟨89,5,[24,25,26,27,28,29,30,31],975⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,434⟩,497⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨89,5,[4,5,6,7,12,13,14,15],1234⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,434⟩,1020⟩),true,[4,5,6,7,12,13,14,15],[]⟩
]

private theorem good_1 : ∀ r ∈ chunk_1, rowGood r := by
  decide +kernel

private def chunk_2 : List Row := [
⟨⟨89,6,[10],38⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,375⟩,170⟩),true,[10],[]⟩,
⟨⟨89,6,[9],68⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,375⟩,110⟩),true,[9],[]⟩,
⟨⟨89,6,[2],115⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,375⟩,328⟩),true,[2],[]⟩,
⟨⟨89,6,[8],159⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,375⟩,72⟩),true,[8],[]⟩,
⟨⟨89,6,[0],203⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,375⟩,789⟩),true,[0],[]⟩,
⟨⟨89,6,[1,3],516⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,375⟩,432⟩),true,[1,3],[]⟩,
⟨⟨89,6,[16,17,18,19,20,21,22,23],554⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,375⟩,269⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨89,6,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨89,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨89,6,[11],869⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,375⟩,680⟩),true,[11],[]⟩,
⟨⟨89,6,[24,25,26,27,28,29,30,31],967⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,375⟩,494⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨89,6,[4,5,6,7,12,13,14,15],1222⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,375⟩,1016⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨89,7,[10],36⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,206⟩,163⟩),true,[10],[]⟩,
⟨⟨89,7,[9],65⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,206⟩,95⟩),true,[9],[]⟩,
⟨⟨89,7,[2],114⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,206⟩,321⟩),true,[2],[]⟩,
⟨⟨89,7,[8],158⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,206⟩,63⟩),true,[8],[]⟩,
⟨⟨89,7,[0],201⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,206⟩,773⟩),true,[0],[]⟩,
⟨⟨89,7,[1,3],515⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,206⟩,421⟩),true,[1,3],[]⟩,
⟨⟨89,7,[16,17,18,19,20,21,22,23],553⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,206⟩,257⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨89,7,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨89,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨89,7,[11],868⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,206⟩,672⟩),true,[11],[]⟩,
⟨⟨89,7,[24,25,26,27,28,29,30,31],966⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,206⟩,483⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨89,7,[4,5,6,7,12,13,14,15],1220⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,206⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,206⟩,1001⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨89,8,[-1],568⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨false,false,373⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,294⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,321⟩,229⟩),true,[-1],[]⟩,
⟨⟨89,9,[-1],575⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨false,false,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,434⟩,231⟩),true,[-1],[]⟩,
⟨⟨89,10,[-1],571⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,358⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,454⟩,233⟩),true,[-1],[]⟩,
⟨⟨89,11,[-1],572⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,214⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,214⟩,227⟩),true,[-1],[]⟩,
⟨⟨89,12,[-1],700⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨true,true,373⟩,⟨false,false,321⟩,⟨true,false,434⟩],(.bound ⟨true,false,448⟩),(.pair ⟨⟨true,true,373⟩,⟨false,false,321⟩,314⟩),true,[-1],[]⟩,
⟨⟨89,13,[-1],703⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨true,true,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],(.bound ⟨true,false,407⟩),(.pair ⟨⟨true,true,373⟩,⟨false,true,434⟩,315⟩),true,[-1],[]⟩,
⟨⟨89,14,[-1],701⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],(.bound ⟨true,false,396⟩),(.pair ⟨⟨true,true,373⟩,⟨false,false,454⟩,317⟩),true,[-1],[]⟩,
⟨⟨89,15,[-1],702⟩,[⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],(.bound ⟨true,false,441⟩),(.pair ⟨⟨true,true,373⟩,⟨false,true,441⟩,316⟩),true,[-1],[]⟩,
⟨⟨90,0,[-1],470⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨true,false,612⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,258⟩),(.pair ⟨⟨true,false,612⟩,⟨false,true,534⟩,962⟩),true,[-1],[]⟩,
⟨⟨90,1,[-1],469⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨true,false,612⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,191⟩),(.pair ⟨⟨true,false,612⟩,⟨false,true,563⟩,963⟩),true,[-1],[]⟩,
⟨⟨90,2,[-1],470⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨true,false,612⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,179⟩),(.pair ⟨⟨true,false,612⟩,⟨false,true,534⟩,962⟩),true,[-1],[]⟩,
⟨⟨90,3,[-1],470⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨true,false,612⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,219⟩),(.pair ⟨⟨true,false,612⟩,⟨false,true,534⟩,962⟩),true,[-1],[]⟩,
⟨⟨90,4,[-1],1083⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨false,true,612⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,398⟩),(.pair ⟨⟨true,true,398⟩,⟨false,true,534⟩,364⟩),true,[-1],[]⟩,
⟨⟨90,5,[-1],1032⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨false,true,612⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,725⟩),(.pair ⟨⟨true,true,725⟩,⟨false,true,563⟩,1198⟩),true,[-1],[]⟩,
⟨⟨90,6,[-1],907⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨false,true,612⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,706⟩),(.pair ⟨⟨true,true,706⟩,⟨false,true,534⟩,1166⟩),true,[-1],[]⟩,
⟨⟨90,7,[-1],615⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,640⟩,⟨false,true,612⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,164⟩),(.pair ⟨⟨true,true,164⟩,⟨false,true,534⟩,133⟩),true,[-1],[]⟩,
⟨⟨90,8,[-1],722⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨false,false,675⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,324⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,534⟩,1065⟩),true,[-1],[]⟩,
⟨⟨90,9,[-1],720⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨false,false,675⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,709⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,563⟩,1067⟩),true,[-1],[]⟩,
⟨⟨90,10,[-1],722⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨false,false,675⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,657⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,534⟩,1065⟩),true,[-1],[]⟩,
⟨⟨90,11,[-1],722⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨false,false,675⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,301⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,534⟩,1065⟩),true,[-1],[]⟩,
⟨⟨90,12,[-1],1166⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨true,true,675⟩,⟨false,true,296⟩,⟨true,false,563⟩],(.bound ⟨false,false,220⟩),(.pair ⟨⟨true,true,675⟩,⟨false,true,534⟩,1127⟩),true,[-1],[]⟩,
⟨⟨90,13,[-1],1165⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨true,true,675⟩,⟨false,true,296⟩,⟨false,true,563⟩],(.bound ⟨false,false,158⟩),(.pair ⟨⟨true,true,675⟩,⟨false,true,563⟩,1128⟩),true,[-1],[]⟩,
⟨⟨90,14,[-1],1166⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨true,true,675⟩,⟨true,false,296⟩,⟨false,false,631⟩],(.bound ⟨false,false,380⟩),(.pair ⟨⟨true,true,675⟩,⟨false,true,534⟩,1127⟩),true,[-1],[]⟩,
⟨⟨90,15,[-1],1166⟩,[⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,640⟩,⟨true,true,675⟩,⟨true,false,296⟩,⟨true,true,631⟩],(.bound ⟨false,false,196⟩),(.pair ⟨⟨true,true,675⟩,⟨false,true,534⟩,1127⟩),true,[-1],[]⟩,
⟨⟨92,0,[-1],12⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,524⟩),(.pair ⟨⟨true,false,347⟩,⟨false,false,216⟩,297⟩),true,[-1],[]⟩,
⟨⟨92,1,[-1],13⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,404⟩),(.pair ⟨⟨true,false,347⟩,⟨false,true,466⟩,298⟩),true,[-1],[]⟩,
⟨⟨92,2,[9,41],56⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,497⟩,124⟩),true,[9,41],[]⟩,
⟨⟨92,2,[8,40],152⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,497⟩,81⟩),true,[8,40],[]⟩,
⟨⟨92,2,[0,32],190⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,497⟩,804⟩),true,[0,32],[]⟩,
⟨⟨92,2,[1,33],508⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,497⟩,442⟩),true,[1,33],[]⟩,
⟨⟨92,2,[16,17,48,49],546⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,497⟩,278⟩),true,[16,17,48,49],[]⟩,
⟨⟨92,2,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨92,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨92,2,[24,25,56,57],959⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,497⟩,503⟩),true,[24,25,56,57],[]⟩,
⟨⟨92,2,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,395⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],[]⟩,
⟨⟨92,3,[9,41],86⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,512⟩,127⟩),true,[9,41],[]⟩,
⟨⟨92,3,[8,40],171⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,512⟩,83⟩),true,[8,40],[]⟩,
⟨⟨92,3,[0,32],220⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,512⟩,808⟩),true,[0,32],[]⟩,
⟨⟨92,3,[1,33],530⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,512⟩,444⟩),true,[1,33],[]⟩,
⟨⟨92,3,[16,17,48,49],567⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,512⟩,280⟩),true,[16,17,48,49],[]⟩,
⟨⟨92,3,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨92,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨92,3,[24,25,56,57],980⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,512⟩,505⟩),true,[24,25,56,57],[]⟩,
⟨⟨92,3,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨true,false,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],[]⟩,
⟨⟨92,4,[9,41],50⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,216⟩,97⟩),true,[9,41],[]⟩,
⟨⟨92,4,[8,40],148⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,216⟩,65⟩),true,[8,40],[]⟩,
⟨⟨92,4,[0,32],183⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,216⟩,775⟩),true,[0,32],[]⟩,
⟨⟨92,4,[1,33],502⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,216⟩,423⟩),true,[1,33],[]⟩,
⟨⟨92,4,[16,17,48,49],540⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,216⟩,259⟩),true,[16,17,48,49],[]⟩,
⟨⟨92,4,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨92,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨92,4,[24,25,56,57],953⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,216⟩,485⟩),true,[24,25,56,57],[]⟩,
⟨⟨92,4,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,140⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],[]⟩,
⟨⟨92,5,[9,41],84⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,466⟩,122⟩),true,[9,41],[]⟩,
⟨⟨92,5,[8,40],170⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,466⟩,80⟩),true,[8,40],[]⟩,
⟨⟨92,5,[0,32],218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,466⟩,801⟩),true,[0,32],[]⟩,
⟨⟨92,5,[1,33],529⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,466⟩,441⟩),true,[1,33],[]⟩,
⟨⟨92,5,[16,17,48,49],566⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,466⟩,277⟩),true,[16,17,48,49],[]⟩,
⟨⟨92,5,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨92,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨92,5,[24,25,56,57],979⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,466⟩,502⟩),true,[24,25,56,57],[]⟩,
⟨⟨92,5,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],[]⟩,
⟨⟨92,6,[9,41],64⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,347⟩,107⟩),true,[9,41],[]⟩,
⟨⟨92,6,[8,40],157⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,347⟩,70⟩),true,[8,40],[]⟩,
⟨⟨92,6,[0,32],200⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,347⟩,786⟩),true,[0,32],[]⟩,
⟨⟨92,6,[1,33],514⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,347⟩,430⟩),true,[1,33],[]⟩,
⟨⟨92,6,[16,17,48,49],552⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,347⟩,267⟩),true,[16,17,48,49],[]⟩,
⟨⟨92,6,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨92,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨92,6,[24,25,56,57],965⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,347⟩,492⟩),true,[24,25,56,57],[]⟩,
⟨⟨92,6,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],[]⟩,
⟨⟨92,7,[9,41],71⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,95⟩,92⟩),true,[9,41],[]⟩
]

private theorem good_2 : ∀ r ∈ chunk_2, rowGood r := by
  decide +kernel

private def chunk_3 : List Row := [
⟨⟨92,7,[8,40],161⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,95⟩,60⟩),true,[8,40],[]⟩,
⟨⟨92,7,[0,32],206⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,95⟩,770⟩),true,[0,32],[]⟩,
⟨⟨92,7,[1,33],518⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,95⟩,419⟩),true,[1,33],[]⟩,
⟨⟨92,7,[16,17,48,49],556⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,95⟩,255⟩),true,[16,17,48,49],[]⟩,
⟨⟨92,7,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨92,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨92,7,[24,25,56,57],969⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,95⟩,481⟩),true,[24,25,56,57],[]⟩,
⟨⟨92,7,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,95⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],[]⟩,
⟨⟨92,8,[-1],644⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨false,false,328⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,218⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,216⟩,212⟩),true,[-1],[]⟩,
⟨⟨92,9,[-1],651⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨false,false,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,466⟩,215⟩),true,[-1],[]⟩,
⟨⟨92,10,[-1],646⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,335⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,497⟩,216⟩),true,[-1],[]⟩,
⟨⟨92,11,[-1],648⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,106⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,106⟩,210⟩),true,[-1],[]⟩,
⟨⟨92,12,[-1],693⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨true,true,328⟩,⟨false,false,216⟩,⟨true,false,466⟩],(.bound ⟨true,false,499⟩),(.pair ⟨⟨true,true,328⟩,⟨false,false,216⟩,291⟩),true,[-1],[]⟩,
⟨⟨92,13,[-1],696⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨true,true,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],(.bound ⟨true,false,425⟩),(.pair ⟨⟨true,true,328⟩,⟨false,true,466⟩,292⟩),true,[-1],[]⟩,
⟨⟨92,14,[-1],694⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],(.bound ⟨true,false,412⟩),(.pair ⟨⟨true,true,328⟩,⟨false,false,497⟩,294⟩),true,[-1],[]⟩,
⟨⟨92,15,[-1],695⟩,[⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],(.bound ⟨true,false,484⟩),(.pair ⟨⟨true,true,328⟩,⟨false,true,484⟩,293⟩),true,[-1],[]⟩,
⟨⟨93,0,[-1],9⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,200⟩),(.pair ⟨⟨true,false,177⟩,⟨false,true,534⟩,146⟩),true,[-1],[]⟩,
⟨⟨93,1,[-1],9⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨true,false,177⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,128⟩),(.pair ⟨⟨true,false,177⟩,⟨false,true,534⟩,146⟩),true,[-1],[]⟩,
⟨⟨93,2,[-1],9⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,115⟩),(.pair ⟨⟨true,false,177⟩,⟨false,true,534⟩,146⟩),true,[-1],[]⟩,
⟨⟨93,3,[-1],9⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨true,false,177⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,153⟩),(.pair ⟨⟨true,false,177⟩,⟨false,true,534⟩,146⟩),true,[-1],[]⟩,
⟨⟨93,4,[-1],593⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,236⟩),(.pair ⟨⟨true,true,236⟩,⟨false,true,534⟩,220⟩),true,[-1],[]⟩,
⟨⟨93,5,[-1],706⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨false,true,177⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,15⟩),(.pair ⟨⟨true,true,15⟩,⟨false,true,534⟩,11⟩),true,[-1],[]⟩,
⟨⟨93,6,[-1],600⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,11⟩),(.pair ⟨⟨true,true,11⟩,⟨false,true,534⟩,5⟩),true,[-1],[]⟩,
⟨⟨93,7,[-1],1003⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,true,567⟩,⟨false,true,177⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,716⟩),(.pair ⟨⟨true,true,716⟩,⟨false,true,534⟩,1184⟩),true,[-1],[]⟩,
⟨⟨93,8,[-1],764⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,267⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,534⟩,657⟩),true,[-1],[]⟩,
⟨⟨93,9,[-1],764⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨false,false,110⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,746⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,534⟩,657⟩),true,[-1],[]⟩,
⟨⟨93,10,[-1],764⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,731⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,534⟩,657⟩),true,[-1],[]⟩,
⟨⟨93,11,[-1],764⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨false,false,110⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,121⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,534⟩,657⟩),true,[-1],[]⟩,
⟨⟨93,12,[-1],688⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,634⟩,⟨true,false,605⟩],(.bound ⟨false,false,154⟩),(.pair ⟨⟨true,true,110⟩,⟨false,true,534⟩,36⟩),true,[-1],[]⟩,
⟨⟨93,13,[-1],688⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨true,true,110⟩,⟨false,true,634⟩,⟨false,true,605⟩],(.bound ⟨false,false,208⟩),(.pair ⟨⟨true,true,110⟩,⟨false,true,534⟩,36⟩),true,[-1],[]⟩,
⟨⟨93,14,[-1],688⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,634⟩,⟨false,false,668⟩],(.bound ⟨false,false,476⟩),(.pair ⟨⟨true,true,110⟩,⟨false,true,534⟩,36⟩),true,[-1],[]⟩,
⟨⟨93,15,[-1],688⟩,[⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,634⟩,⟨true,true,668⟩],(.bound ⟨false,false,130⟩),(.pair ⟨⟨true,true,110⟩,⟨false,true,534⟩,36⟩),true,[-1],[]⟩,
⟨⟨94,0,[-1],278⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩),(.pair ⟨⟨true,false,426⟩,⟨false,false,254⟩,406⟩),true,[-1],[]⟩,
⟨⟨94,1,[-1],281⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩),(.pair ⟨⟨true,false,426⟩,⟨false,true,508⟩,407⟩),true,[-1],[]⟩,
⟨⟨94,2,[-1],279⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩),(.pair ⟨⟨true,false,426⟩,⟨false,false,215⟩,405⟩),true,[-1],[]⟩,
⟨⟨94,3,[-1],279⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,false,426⟩,⟨false,false,215⟩,405⟩),true,[-1],[]⟩,
⟨⟨94,4,[-1],631⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,254⟩,203⟩),true,[-1],[]⟩,
⟨⟨94,5,[-1],639⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,508⟩,206⟩),true,[-1],[]⟩,
⟨⟨94,6,[-1],632⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,215⟩,200⟩),true,[-1],[]⟩,
⟨⟨94,7,[-1],632⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,215⟩,200⟩),true,[-1],[]⟩,
⟨⟨94,8,[10],27⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,254⟩,166⟩),true,[10],[]⟩,
⟨⟨94,8,[9],47⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,254⟩,100⟩),true,[9],[]⟩,
⟨⟨94,8,[2],105⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,254⟩,324⟩),true,[2],[]⟩,
⟨⟨94,8,[8],146⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,254⟩,67⟩),true,[8],[]⟩,
⟨⟨94,8,[0],180⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,254⟩,778⟩),true,[0],[]⟩,
⟨⟨94,8,[1,3],500⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,254⟩,427⟩),true,[1,3],[]⟩,
⟨⟨94,8,[16,17,18,19,20,21,22,23],538⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,254⟩,263⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨94,8,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨94,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨94,8,[11],857⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,254⟩,676⟩),true,[11],[]⟩,
⟨⟨94,8,[24,25,26,27,28,29,30,31],951⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,254⟩,489⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨94,8,[4,5,6,7,12,13,14,15],1199⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,254⟩,1007⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨94,9,[10],42⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,508⟩,178⟩),true,[10],[]⟩,
⟨⟨94,9,[9],75⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,508⟩,125⟩),true,[9],[]⟩,
⟨⟨94,9,[2],119⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,508⟩,336⟩),true,[2],[]⟩,
⟨⟨94,9,[8],165⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,508⟩,82⟩),true,[8],[]⟩,
⟨⟨94,9,[0],211⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,508⟩,805⟩),true,[0],[]⟩,
⟨⟨94,9,[1,3],521⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,508⟩,443⟩),true,[1,3],[]⟩,
⟨⟨94,9,[16,17,18,19,20,21,22,23],560⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,508⟩,279⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨94,9,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨94,9,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨94,9,[11],873⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,508⟩,688⟩),true,[11],[]⟩,
⟨⟨94,9,[24,25,26,27,28,29,30,31],973⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,508⟩,504⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨94,9,[4,5,6,7,12,13,14,15],1230⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,508⟩,1030⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨94,10,[10],28⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,215⟩,164⟩),true,[10],[]⟩,
⟨⟨94,10,[9],49⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,215⟩,96⟩),true,[9],[]⟩,
⟨⟨94,10,[2],106⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,215⟩,322⟩),true,[2],[]⟩,
⟨⟨94,10,[8],147⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,215⟩,64⟩),true,[8],[]⟩,
⟨⟨94,10,[0],182⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,215⟩,774⟩),true,[0],[]⟩,
⟨⟨94,10,[1,3],501⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,215⟩,422⟩),true,[1,3],[]⟩,
⟨⟨94,10,[16,17,18,19,20,21,22,23],539⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,215⟩,258⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨94,10,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨94,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨94,10,[11],858⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,215⟩,673⟩),true,[11],[]⟩,
⟨⟨94,10,[24,25,26,27,28,29,30,31],952⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,215⟩,484⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨94,10,[4,5,6,7,12,13,14,15],1200⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,215⟩,1002⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨94,11,[10],28⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,215⟩,164⟩),true,[10],[]⟩,
⟨⟨94,11,[9],49⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,215⟩,96⟩),true,[9],[]⟩,
⟨⟨94,11,[2],106⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,215⟩,322⟩),true,[2],[]⟩,
⟨⟨94,11,[8],147⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,215⟩,64⟩),true,[8],[]⟩,
⟨⟨94,11,[0],182⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,215⟩,774⟩),true,[0],[]⟩,
⟨⟨94,11,[1,3],501⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,215⟩,422⟩),true,[1,3],[]⟩,
⟨⟨94,11,[16,17,18,19,20,21,22,23],539⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,215⟩,258⟩),true,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨94,11,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨94,11,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨94,11,[11],858⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,215⟩,673⟩),true,[11],[]⟩,
⟨⟨94,11,[24,25,26,27,28,29,30,31],952⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,215⟩,484⟩),true,[24,25,26,27,28,29,30,31],[]⟩,
⟨⟨94,11,[4,5,6,7,12,13,14,15],1200⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,215⟩,1002⟩),true,[4,5,6,7,12,13,14,15],[]⟩,
⟨⟨94,12,[-1],631⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,254⟩,203⟩),true,[-1],[]⟩,
⟨⟨94,13,[-1],639⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,508⟩,206⟩),true,[-1],[]⟩,
⟨⟨94,14,[-1],632⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,215⟩,200⟩),true,[-1],[]⟩,
⟨⟨94,15,[-1],632⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,215⟩,200⟩),true,[-1],[]⟩,
⟨⟨94,16,[-1],653⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,254⟩,239⟩),true,[-1],[]⟩,
⟨⟨94,17,[-1],657⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,264⟩,⟨false,true,508⟩,240⟩),true,[-1],[]⟩,
⟨⟨94,18,[-1],654⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,215⟩,238⟩),true,[-1],[]⟩,
⟨⟨94,19,[-1],654⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,215⟩,238⟩),true,[-1],[]⟩
]

private theorem good_3 : ∀ r ∈ chunk_3, rowGood r := by
  decide +kernel

private def chunk_4 : List Row := [
⟨⟨94,20,[-1],653⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,254⟩,239⟩),true,[-1],[]⟩,
⟨⟨94,21,[-1],657⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,264⟩,⟨false,true,508⟩,240⟩),true,[-1],[]⟩,
⟨⟨94,22,[-1],654⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,215⟩,238⟩),true,[-1],[]⟩,
⟨⟨94,23,[-1],654⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,215⟩,238⟩),true,[-1],[]⟩,
⟨⟨94,24,[-1],986⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,254⟩,452⟩),true,[-1],[]⟩,
⟨⟨94,25,[-1],989⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩),(.pair ⟨⟨true,true,446⟩,⟨false,true,508⟩,454⟩),true,[-1],[]⟩,
⟨⟨94,26,[-1],987⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,215⟩,451⟩),true,[-1],[]⟩,
⟨⟨94,27,[-1],987⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,215⟩,451⟩),true,[-1],[]⟩,
⟨⟨94,28,[-1],986⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,254⟩,452⟩),true,[-1],[]⟩,
⟨⟨94,29,[-1],989⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩),(.pair ⟨⟨true,true,446⟩,⟨false,true,508⟩,454⟩),true,[-1],[]⟩,
⟨⟨94,30,[-1],987⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,215⟩,451⟩),true,[-1],[]⟩,
⟨⟨94,31,[-1],987⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,215⟩,451⟩),true,[-1],[]⟩,
⟨⟨94,32,[-1],278⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩),(.pair ⟨⟨true,false,426⟩,⟨false,false,254⟩,406⟩),true,[-1],[]⟩,
⟨⟨94,33,[-1],281⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩),(.pair ⟨⟨true,false,426⟩,⟨false,true,508⟩,407⟩),true,[-1],[]⟩,
⟨⟨94,34,[-1],280⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩),(.pair ⟨⟨true,false,426⟩,⟨false,false,552⟩,409⟩),true,[-1],[]⟩,
⟨⟨94,35,[-1],282⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,false,426⟩,⟨false,true,511⟩,408⟩),true,[-1],[]⟩,
⟨⟨94,36,[-1],631⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,523⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,254⟩,203⟩),true,[-1],[]⟩,
⟨⟨94,37,[-1],639⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,419⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,508⟩,206⟩),true,[-1],[]⟩,
⟨⟨94,38,[-1],636⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,365⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,552⟩,209⟩),true,[-1],[]⟩,
⟨⟨94,39,[-1],642⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨true,false,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,511⟩,207⟩),true,[-1],[]⟩,
⟨⟨94,40,[-1],582⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,215⟩,⟨false,false,254⟩,182⟩),true,[-1],[]⟩,
⟨⟨94,41,[-1],585⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,215⟩,⟨false,true,508⟩,183⟩),true,[-1],[]⟩,
⟨⟨94,42,[10],34⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,203⟩,⟨false,false,552⟩,179⟩),true,[10],[]⟩,
⟨⟨94,42,[9],77⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,516⟩,128⟩),true,[9],[]⟩,
⟨⟨94,42,[2],112⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,376⟩,⟨false,false,552⟩,337⟩),true,[2],[]⟩,
⟨⟨94,42,[8],155⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,117⟩,⟨false,false,552⟩,84⟩),true,[8],[]⟩,
⟨⟨94,42,[0],195⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,552⟩,809⟩),true,[0],[]⟩,
⟨⟨94,42,[3],512⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,552⟩,446⟩),true,[3],[]⟩,
⟨⟨94,42,[1],522⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,516⟩,445⟩),true,[1],[]⟩,
⟨⟨94,42,[16,18,19,20,22,23],550⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,552⟩,282⟩),true,[16,18,19,20,22,23],[]⟩,
⟨⟨94,42,[17,21],561⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,516⟩,281⟩),true,[17,21],[]⟩,
⟨⟨94,42,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨94,42,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨94,42,[11],866⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,552⟩,689⟩),true,[11],[]⟩,
⟨⟨94,42,[24,26,27,28,30,31],963⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,552⟩,508⟩),true,[24,26,27,28,30,31],[]⟩,
⟨⟨94,42,[25,29],974⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,516⟩,506⟩),true,[25,29],[]⟩,
⟨⟨94,42,[4,6,7,12,14,15],1215⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,552⟩,1034⟩),true,[4,6,7,12,14,15],[]⟩,
⟨⟨94,42,[5,13],1231⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,516⟩,1032⟩),true,[5,13],[]⟩,
⟨⟨94,43,[10],40⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,137⟩,161⟩),true,[10],[]⟩,
⟨⟨94,43,[9],77⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,516⟩,128⟩),true,[9],[]⟩,
⟨⟨94,43,[2],117⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,376⟩,⟨false,true,137⟩,320⟩),true,[2],[]⟩,
⟨⟨94,43,[8],163⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,137⟩,62⟩),true,[8],[]⟩,
⟨⟨94,43,[0],207⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,137⟩,771⟩),true,[0],[]⟩,
⟨⟨94,43,[3],519⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,137⟩,420⟩),true,[3],[]⟩,
⟨⟨94,43,[1],522⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,516⟩,445⟩),true,[1],[]⟩,
⟨⟨94,43,[16,18,19,20,22,23],558⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,137⟩,256⟩),true,[16,18,19,20,22,23],[]⟩,
⟨⟨94,43,[17,21],561⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,516⟩,281⟩),true,[17,21],[]⟩,
⟨⟨94,43,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],[]⟩,
⟨⟨94,43,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨94,43,[11],871⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,569⟩,⟨false,true,137⟩,671⟩),true,[11],[]⟩,
⟨⟨94,43,[24,26,27,28,30,31],970⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,137⟩,482⟩),true,[24,26,27,28,30,31],[]⟩,
⟨⟨94,43,[25,29],974⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,516⟩,506⟩),true,[25,29],[]⟩,
⟨⟨94,43,[4,6,7,12,14,15],1227⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,137⟩,1000⟩),true,[4,6,7,12,14,15],[]⟩,
⟨⟨94,43,[5,13],1231⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,516⟩,1032⟩),true,[5,13],[]⟩,
⟨⟨94,44,[-1],631⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,224⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,254⟩,203⟩),true,[-1],[]⟩,
⟨⟨94,45,[-1],639⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,508⟩,206⟩),true,[-1],[]⟩,
⟨⟨94,46,[-1],636⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,552⟩,209⟩),true,[-1],[]⟩,
⟨⟨94,47,[-1],638⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨false,true,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,137⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,137⟩,199⟩),true,[-1],[]⟩,
⟨⟨94,48,[-1],653⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,254⟩,239⟩),true,[-1],[]⟩,
⟨⟨94,49,[-1],657⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,264⟩,⟨false,true,508⟩,240⟩),true,[-1],[]⟩,
⟨⟨94,50,[-1],655⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,552⟩,241⟩),true,[-1],[]⟩,
⟨⟨94,51,[-1],656⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩),(.pair ⟨⟨true,true,264⟩,⟨false,true,142⟩,237⟩),true,[-1],[]⟩,
⟨⟨94,52,[-1],653⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,249⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,254⟩,239⟩),true,[-1],[]⟩,
⟨⟨94,53,[-1],657⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,264⟩,⟨false,true,508⟩,240⟩),true,[-1],[]⟩,
⟨⟨94,54,[-1],655⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,334⟩),(.pair ⟨⟨true,true,264⟩,⟨false,false,552⟩,241⟩),true,[-1],[]⟩,
⟨⟨94,55,[-1],656⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,142⟩),(.pair ⟨⟨true,true,264⟩,⟨false,true,142⟩,237⟩),true,[-1],[]⟩,
⟨⟨94,56,[-1],986⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,254⟩,452⟩),true,[-1],[]⟩,
⟨⟨94,57,[-1],989⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩),(.pair ⟨⟨true,true,446⟩,⟨false,true,508⟩,454⟩),true,[-1],[]⟩,
⟨⟨94,58,[-1],988⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,552⟩,455⟩),true,[-1],[]⟩,
⟨⟨94,59,[-1],990⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩),(.pair ⟨⟨true,true,446⟩,⟨false,true,483⟩,453⟩),true,[-1],[]⟩,
⟨⟨94,60,[-1],986⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,498⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,254⟩,452⟩),true,[-1],[]⟩,
⟨⟨94,61,[-1],989⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,460⟩),(.pair ⟨⟨true,true,446⟩,⟨false,true,508⟩,454⟩),true,[-1],[]⟩,
⟨⟨94,62,[-1],988⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,405⟩),(.pair ⟨⟨true,true,446⟩,⟨false,false,552⟩,455⟩),true,[-1],[]⟩,
⟨⟨94,63,[-1],990⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,215⟩,⟨true,false,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,483⟩),(.pair ⟨⟨true,true,446⟩,⟨false,true,483⟩,453⟩),true,[-1],[]⟩,
⟨⟨96,0,[-1],505⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,223⟩,426⟩),true,[-1],[]⟩,
⟨⟨96,1,[-1],522⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,516⟩,445⟩),true,[-1],[]⟩,
⟨⟨96,2,[-1],504⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,222⟩,425⟩),true,[-1],[]⟩,
⟨⟨96,3,[-1],504⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,222⟩,425⟩),true,[-1],[]⟩,
⟨⟨96,4,[-1],1203⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,223⟩,1005⟩),true,[-1],[]⟩,
⟨⟨96,5,[-1],1231⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,516⟩,1032⟩),true,[-1],[]⟩,
⟨⟨96,6,[-1],1202⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,222⟩,1004⟩),true,[-1],[]⟩,
⟨⟨96,7,[-1],1202⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,222⟩,1004⟩),true,[-1],[]⟩,
⟨⟨96,8,[8,12,40,44],162⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,false,117⟩,⟨false,true,117⟩,61⟩),false,[8,12,40,44],[]⟩,
⟨⟨96,8,[1,9],283⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,false,516⟩,⟨false,true,516⟩,522⟩),false,[1,9],[]⟩,
⟨⟨96,8,[0],526⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,433⟩,435⟩),false,[0],[]⟩,
⟨⟨96,8,[16,17,20,21,24,25,28,29],537⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,296⟩,265⟩),false,[16,17,20,21,24,25,28,29],[]⟩,
⟨⟨96,8,[32,33,36,37,41,45,48,49,52,53,56,57,60,61],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,36,37,41,45,48,49,52,53,56,57,60,61],[]⟩,
⟨⟨96,8,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩,
⟨⟨96,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨96,8,[4,5,13],1218⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,13],[]⟩,
⟨⟨96,9,[9],66⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,147⟩,94⟩),false,[9],[]⟩,
⟨⟨96,9,[0,8],283⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,false,516⟩,⟨false,true,516⟩,522⟩),false,[0,8],[]⟩,
⟨⟨96,9,[1],526⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,433⟩,435⟩),false,[1],[]⟩,
⟨⟨96,9,[16,17,20,21,24,25,28,29],537⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,296⟩,265⟩),false,[16,17,20,21,24,25,28,29],[]⟩,
⟨⟨96,9,[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],[]⟩,
⟨⟨96,9,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59],[6,7,14,15,22,23,30,31,38,39,46,47,54,55,62,63]⟩
]

private theorem good_4 : ∀ r ∈ chunk_4, rowGood r := by
  decide +kernel

private def chunk_5 : List Row := [
⟨⟨96,9,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨96,9,[4,5,12,13],1218⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[4,5,12,13],[]⟩,
⟨⟨96,10,[10,14,42,46],37⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,203⟩,162⟩),false,[10,14,42,46],[]⟩,
⟨⟨96,10,[2],526⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,433⟩,435⟩),false,[2],[]⟩,
⟨⟨96,10,[18,22,26,30],537⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,296⟩,265⟩),false,[18,22,26,30],[]⟩,
⟨⟨96,10,[34,35,38,39,43,47,50,54,58,59,62,63],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[34,35,38,39,43,47,50,54,58,59,62,63],[]⟩,
⟨⟨96,10,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],[]⟩,
⟨⟨96,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨96,10,[3,7,11,15,19,23,27,31,51,55],863⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,569⟩,690⟩),false,[3,7,11,15,19,23,27,31,51,55],[]⟩,
⟨⟨96,10,[6],1218⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[6],[]⟩,
⟨⟨96,11,[-1],860⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,222⟩,675⟩),true,[-1],[]⟩,
⟨⟨96,12,[-1],1203⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,223⟩,1005⟩),true,[-1],[]⟩,
⟨⟨96,13,[-1],1231⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,516⟩,1032⟩),true,[-1],[]⟩,
⟨⟨96,14,[-1],1202⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,222⟩,1004⟩),true,[-1],[]⟩,
⟨⟨96,15,[-1],1202⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,222⟩,1004⟩),true,[-1],[]⟩,
⟨⟨96,16,[-1],543⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,223⟩,262⟩),true,[-1],[]⟩,
⟨⟨96,17,[-1],561⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,516⟩,281⟩),true,[-1],[]⟩,
⟨⟨96,18,[-1],542⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,222⟩,261⟩),true,[-1],[]⟩,
⟨⟨96,19,[-1],542⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,222⟩,261⟩),true,[-1],[]⟩,
⟨⟨96,20,[-1],543⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,223⟩,262⟩),true,[-1],[]⟩,
⟨⟨96,21,[-1],561⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,516⟩,281⟩),true,[-1],[]⟩,
⟨⟨96,22,[-1],542⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,222⟩,261⟩),true,[-1],[]⟩,
⟨⟨96,23,[-1],542⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,222⟩,261⟩),true,[-1],[]⟩,
⟨⟨96,24,[-1],956⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,223⟩,488⟩),true,[-1],[]⟩,
⟨⟨96,25,[-1],974⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,516⟩,506⟩),true,[-1],[]⟩,
⟨⟨96,26,[-1],955⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,222⟩,487⟩),true,[-1],[]⟩,
⟨⟨96,27,[-1],955⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,222⟩,487⟩),true,[-1],[]⟩,
⟨⟨96,28,[-1],956⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,223⟩,488⟩),true,[-1],[]⟩,
⟨⟨96,29,[-1],974⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,516⟩,506⟩),true,[-1],[]⟩,
⟨⟨96,30,[-1],955⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,222⟩,487⟩),true,[-1],[]⟩,
⟨⟨96,31,[-1],955⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,222⟩,487⟩),true,[-1],[]⟩,
⟨⟨96,32,[-1],505⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,223⟩,426⟩),true,[-1],[]⟩,
⟨⟨96,33,[-1],522⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,516⟩,445⟩),true,[-1],[]⟩,
⟨⟨96,34,[-1],509⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩),(.pair ⟨⟨true,false,433⟩,⟨false,false,569⟩,448⟩),true,[-1],[]⟩,
⟨⟨96,35,[-1],524⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,561⟩,447⟩),true,[-1],[]⟩,
⟨⟨96,36,[-1],1203⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,583⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,223⟩,1005⟩),true,[-1],[]⟩,
⟨⟨96,37,[-1],1231⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,416⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,516⟩,1032⟩),true,[-1],[]⟩,
⟨⟨96,38,[-1],1211⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,376⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,569⟩,1036⟩),true,[-1],[]⟩,
⟨⟨96,39,[-1],1235⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,561⟩,1035⟩),true,[-1],[]⟩,
⟨⟨96,40,[-1],634⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,223⟩,202⟩),true,[-1],[]⟩,
⟨⟨96,41,[-1],640⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,516⟩,208⟩),true,[-1],[]⟩,
⟨⟨96,42,[10,14,42,46],37⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,false,203⟩,⟨false,true,203⟩,162⟩),false,[10,14,42,46],[]⟩,
⟨⟨96,42,[34],526⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,433⟩,435⟩),false,[34],[]⟩,
⟨⟨96,42,[50,54,58,62],537⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,296⟩,265⟩),false,[50,54,58,62],[]⟩,
⟨⟨96,42,[2,3,6,7,11,15,18,22,26,27,30,31],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[2,3,6,7,11,15,18,22,26,27,30,31],[]⟩,
⟨⟨96,42,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],[]⟩,
⟨⟨96,42,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨96,42,[19,23,35,39,43,47,51,55,59,63],863⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,569⟩,690⟩),false,[19,23,35,39,43,47,51,55,59,63],[]⟩,
⟨⟨96,42,[38],1218⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[38],[]⟩,
⟨⟨96,43,[43],91⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,false,70⟩,⟨false,true,70⟩,24⟩),false,[43],[]⟩,
⟨⟨96,43,[35],526⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,false,433⟩,⟨false,true,433⟩,435⟩),false,[35],[]⟩,
⟨⟨96,43,[51,55,59,63],537⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,296⟩,265⟩),false,[51,55,59,63],[]⟩,
⟨⟨96,43,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],633⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],[]⟩,
⟨⟨96,43,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,223⟩,213⟩),false,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],[]⟩,
⟨⟨96,43,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],[]⟩,
⟨⟨96,43,[34,38,42,46,50,54,58,62],863⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,569⟩,⟨false,false,569⟩,690⟩),false,[34,38,42,46,50,54,58,62],[]⟩,
⟨⟨96,43,[39,47],1218⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[39,47],[]⟩,
⟨⟨96,44,[-1],1203⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,117⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,223⟩,1005⟩),true,[-1],[]⟩,
⟨⟨96,45,[-1],1231⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,516⟩,1032⟩),true,[-1],[]⟩,
⟨⟨96,46,[-1],1211⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,569⟩,1036⟩),true,[-1],[]⟩,
⟨⟨96,47,[-1],1223⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,70⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,70⟩,998⟩),true,[-1],[]⟩,
⟨⟨96,48,[-1],543⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,223⟩,262⟩),true,[-1],[]⟩,
⟨⟨96,49,[-1],561⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,516⟩,281⟩),true,[-1],[]⟩,
⟨⟨96,50,[-1],547⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,569⟩,283⟩),true,[-1],[]⟩,
⟨⟨96,51,[-1],557⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,74⟩,254⟩),true,[-1],[]⟩,
⟨⟨96,52,[-1],543⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,161⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,223⟩,262⟩),true,[-1],[]⟩,
⟨⟨96,53,[-1],561⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,516⟩,281⟩),true,[-1],[]⟩,
⟨⟨96,54,[-1],547⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,304⟩),(.pair ⟨⟨true,true,296⟩,⟨false,false,569⟩,283⟩),true,[-1],[]⟩,
⟨⟨96,55,[-1],557⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,74⟩),(.pair ⟨⟨true,true,296⟩,⟨false,true,74⟩,254⟩),true,[-1],[]⟩,
⟨⟨96,56,[-1],956⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,223⟩,488⟩),true,[-1],[]⟩,
⟨⟨96,57,[-1],974⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,516⟩,506⟩),true,[-1],[]⟩,
⟨⟨96,58,[-1],960⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,569⟩,509⟩),true,[-1],[]⟩,
⟨⟨96,59,[-1],971⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,530⟩,507⟩),true,[-1],[]⟩,
⟨⟨96,60,[-1],956⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨true,false,516⟩],(.bound ⟨true,false,546⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,223⟩,488⟩),true,[-1],[]⟩,
⟨⟨96,61,[-1],974⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,true,223⟩,⟨false,true,516⟩],(.bound ⟨true,false,463⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,516⟩,506⟩),true,[-1],[]⟩,
⟨⟨96,62,[-1],960⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨false,false,569⟩],(.bound ⟨true,false,429⟩),(.pair ⟨⟨true,true,453⟩,⟨false,false,569⟩,509⟩),true,[-1],[]⟩,
⟨⟨96,63,[-1],971⟩,[⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],[⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨true,false,223⟩,⟨true,true,569⟩],(.bound ⟨true,false,530⟩),(.pair ⟨⟨true,true,453⟩,⟨false,true,530⟩,507⟩),true,[-1],[]⟩
]

private theorem good_5 : ∀ r ∈ chunk_5, rowGood r := by
  decide +kernel

private def allRows : List Row := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5].flatten

private theorem rows_good : ∀ r ∈ allRows, rowGood r := by
  intro r hr
  simp only [allRows] at hr
  obtain ⟨c, hc, hr⟩ := List.mem_flatten.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_0 r hr
  · exact good_1 r hr
  · exact good_2 r hr
  · exact good_3 r hr
  · exact good_4 r hr
  · exact good_5 r hr

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([5] : List ℕ)))
      = allRows.map Row.record := by
  decide +kernel

end Row5D

open Row5D

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([5] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ allRows.map Row.record := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  obtain ⟨r, hrr, hre⟩ := List.mem_map.mp hs
  subst hre
  exact from_row r parent (rows_good r hrr) hp hn

#print axioms solution
