-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_mixed_B_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T18:24:10.076971+00:00
-- url     : https://prove2.me/submissions/72fb7685-aff2-4fbf-8ce2-4561b528c533

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

namespace Row1

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

private def branches_11 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,215⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,215⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic)
]

private def branches_12 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨true,false,148⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],.impossible),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨false,false,90⟩],(.bound ⟨false,false,617⟩)),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],.impossible),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨true,false,148⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],.impossible),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨false,false,90⟩],(.bound ⟨false,false,617⟩)),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],.impossible),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨true,false,148⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨false,false,90⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],(.bound ⟨false,false,134⟩)),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨true,false,148⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨false,false,90⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],(.bound ⟨false,false,134⟩)),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨true,false,148⟩],(.bound ⟨true,false,617⟩)),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],.impossible),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨false,false,90⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],.impossible),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨true,false,148⟩],(.bound ⟨true,false,617⟩)),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],.impossible),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨false,false,90⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],.impossible),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨true,false,148⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],(.bound ⟨true,false,134⟩)),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨false,false,90⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨true,false,148⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],(.bound ⟨true,false,134⟩)),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨false,false,90⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],.automatic)
]

private def branches_13 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,215⟩,⟨true,false,465⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,215⟩,⟨true,false,465⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic)
]

private def branches_14 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩)),
([⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩)),
([⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩)),
([⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩)),
([⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩))
]

private def branches_15 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩)),
([⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩)),
([⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩)),
([⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩)),
([⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩))
]

private def branches_16 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic)
]

private def branches_17 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩)),
([⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩)),
([⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩)),
([⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩)),
([⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩))
]

private def branches_18 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩)),
([⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩)),
([⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩)),
([⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩)),
([⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩))
]

private def branches_19 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic)
]

private def branches_20 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩)),
([⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩)),
([⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩)),
([⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩)),
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩))
]

private def branches_21 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩)),
([⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩)),
([⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩)),
([⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩)),
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩))
]

private def branches_22 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,523⟩)),
([⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩)),
([⟨false,false,215⟩,⟨true,false,465⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,217⟩)),
([⟨false,false,215⟩,⟨true,false,465⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,498⟩)),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,403⟩)),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩)),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,289⟩)),
([⟨false,false,215⟩,⟨false,true,465⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,424⟩)),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩)),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩)),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,334⟩)),
([⟨true,true,215⟩,⟨false,false,496⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,411⟩)),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩)),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,94⟩)),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,105⟩)),
([⟨true,true,215⟩,⟨true,true,496⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,483⟩))
]

private def branches_23 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,215⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,215⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,215⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,215⟩,⟨true,true,259⟩],.automatic)
]

private def branches_24 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,583⟩)),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩)),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,160⟩)),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,546⟩)),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,417⟩)),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩)),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,203⟩)),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,464⟩)),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩)),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩)),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,304⟩)),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,430⟩)),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩)),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩)),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,73⟩)),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,530⟩))
]

private def branches_25 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,222⟩,⟨true,false,346⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,222⟩,⟨false,true,346⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,222⟩,⟨false,false,327⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,222⟩,⟨true,true,327⟩],.automatic)
]

private def parentRefs : List (List MiddleCertBoundRef) := [
  [⟨true,false,583⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],
  [⟨true,false,116⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],
  [⟨true,false,160⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,629⟩,⟨false,false,452⟩],
  [⟨true,false,546⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,629⟩,⟨true,true,452⟩],
  [⟨true,false,417⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],
  [⟨true,false,147⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],
  [⟨true,false,203⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,629⟩,⟨false,false,452⟩],
  [⟨true,false,464⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,629⟩,⟨true,true,452⟩],
  [⟨true,false,377⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],
  [⟨true,false,202⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],
  [⟨true,false,304⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,629⟩,⟨false,false,452⟩],
  [⟨true,false,430⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,629⟩,⟨true,true,452⟩],
  [⟨true,false,561⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],
  [⟨true,false,69⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],
  [⟨true,false,73⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,629⟩,⟨false,false,452⟩],
  [⟨true,false,530⟩,⟨false,false,633⟩,⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,629⟩,⟨true,true,452⟩],
  [⟨false,false,48⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,176⟩,⟨false,true,695⟩,⟨true,false,698⟩],
  [⟨false,false,313⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,176⟩,⟨false,true,695⟩,⟨false,true,698⟩],
  [⟨false,false,212⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,176⟩,⟨true,false,695⟩,⟨false,false,724⟩],
  [⟨false,false,35⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,176⟩,⟨true,false,695⟩,⟨true,true,724⟩],
  [⟨false,false,18⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,176⟩,⟨false,true,695⟩,⟨true,false,698⟩],
  [⟨false,false,31⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,176⟩,⟨false,true,695⟩,⟨false,true,698⟩],
  [⟨false,false,21⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,176⟩,⟨true,false,695⟩,⟨false,false,724⟩],
  [⟨false,false,719⟩,⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,176⟩,⟨true,false,695⟩,⟨true,true,724⟩],
  [⟨false,false,20⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,109⟩,⟨false,true,695⟩,⟨true,false,698⟩],
  [⟨false,false,762⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,109⟩,⟨false,true,695⟩,⟨false,true,698⟩],
  [⟨false,false,753⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,109⟩,⟨true,false,695⟩,⟨false,false,724⟩],
  [⟨false,false,124⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,109⟩,⟨true,false,695⟩,⟨true,true,724⟩],
  [⟨false,false,34⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,109⟩,⟨false,true,695⟩,⟨true,false,698⟩],
  [⟨false,false,238⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,109⟩,⟨false,true,695⟩,⟨false,true,698⟩],
  [⟨false,false,437⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,109⟩,⟨true,false,695⟩,⟨false,false,724⟩],
  [⟨false,false,24⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,109⟩,⟨true,false,695⟩,⟨true,true,724⟩]
]

private theorem parents_eq :
    middleRepairCertParents true = parentRefs.map (middleCertBounds middleCertData) := by
  decide +kernel

private def cachedBranches (g : ℕ) : List (List MiddleCertBoundRef × RefComparison) :=
  if g = 11 then branches_11 else
  if g = 12 then branches_12 else
  if g = 13 then branches_13 else
  if g = 14 then branches_14 else
  if g = 15 then branches_15 else
  if g = 16 then branches_16 else
  if g = 17 then branches_17 else
  if g = 18 then branches_18 else
  if g = 19 then branches_19 else
  if g = 20 then branches_20 else
  if g = 21 then branches_21 else
  if g = 22 then branches_22 else
  if g = 23 then branches_23 else
  if g = 24 then branches_24 else
  if g = 25 then branches_25 else
  []

private def selectedGoals : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
    (hpar : middleCertParity (middleCertGoal middleCertData r.record.goal).family = true) :
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
  middleCertParity (middleCertGoal middleCertData r.record.goal).family = true ∧
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
⟨⟨11,4,[9],15⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,false,202⟩,⟨false,false,215⟩,150⟩),true,[9],[]⟩,
⟨⟨11,4,[5],49⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,false,147⟩,⟨false,false,215⟩,96⟩),true,[5],[]⟩,
⟨⟨11,4,[8],93⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,false,377⟩,⟨false,false,215⟩,340⟩),true,[8],[]⟩,
⟨⟨11,4,[1],125⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,false,116⟩,⟨false,false,215⟩,40⟩),true,[1],[]⟩,
⟨⟨11,4,[0],182⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,false,583⟩,⟨false,false,215⟩,774⟩),true,[0],[]⟩,
⟨⟨11,4,[4],472⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,false,417⟩,⟨false,false,215⟩,387⟩),true,[4],[]⟩,
⟨⟨11,4,[16,17,18,19,20,21,22,23],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨11,4,[12,13],879⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,true,570⟩,⟨false,false,215⟩,693⟩),true,[12,13],[]⟩,
⟨⟨11,4,[24,25,26,27,28,29,30,31],917⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,true,681⟩,⟨false,false,681⟩,1142⟩),false,[],[24,25,26,27,28,29,30,31]⟩,
⟨⟨11,4,[3,7,11,15],931⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,true,452⟩,⟨false,false,215⟩,461⟩),true,[3,7,11,15],[]⟩,
⟨⟨11,4,[2,6,10,14],1200⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,false,215⟩,1002⟩),true,[2,6,10,14],[]⟩,
⟨⟨11,6,[9],18⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,202⟩,⟨false,false,259⟩,153⟩),true,[9],[]⟩,
⟨⟨11,6,[5],78⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,147⟩,⟨false,true,517⟩,129⟩),true,[5],[]⟩,
⟨⟨11,6,[13],89⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,69⟩,⟨false,false,259⟩,23⟩),true,[13],[]⟩,
⟨⟨11,6,[8],96⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,377⟩,⟨false,false,259⟩,343⟩),true,[8],[]⟩,
⟨⟨11,6,[1],130⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,116⟩,⟨false,false,259⟩,44⟩),true,[1],[]⟩,
⟨⟨11,6,[0],188⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,583⟩,⟨false,false,259⟩,780⟩),true,[0],[]⟩,
⟨⟨11,6,[4],487⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,417⟩,⟨false,true,517⟩,403⟩),true,[4],[]⟩,
⟨⟨11,6,[12],491⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,false,561⟩,⟨false,false,259⟩,655⟩),true,[12],[]⟩,
⟨⟨11,6,[16,17,18,19,20,21,22,23],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23],[]⟩,
⟨⟨11,6,[24,25,26,27,28,29,30,31],917⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,681⟩,⟨false,false,681⟩,1142⟩),false,[],[24,25,26,27,28,29,30,31]⟩,
⟨⟨11,6,[3,11,15],936⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,452⟩,⟨false,false,259⟩,464⟩),true,[3,11,15],[]⟩,
⟨⟨11,6,[7],947⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,452⟩,⟨false,true,517⟩,478⟩),true,[7],[]⟩,
⟨⟨11,6,[2,10,14],1207⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,false,259⟩,1008⟩),true,[2,10,14],[]⟩,
⟨⟨11,6,[6],1232⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,true,517⟩,1033⟩),true,[6],[]⟩,
⟨⟨11,7,[-1],715⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩),(.pair ⟨⟨true,true,259⟩,⟨false,true,277⟩,236⟩),true,[-1],[]⟩,
⟨⟨11,8,[-1],1030⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩),(.pair ⟨⟨true,true,599⟩,⟨false,false,215⟩,829⟩),true,[-1],[]⟩,
⟨⟨11,12,[-1],811⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩),(.pair ⟨⟨true,true,626⟩,⟨false,false,215⟩,989⟩),true,[-1],[]⟩,
⟨⟨11,13,[-1],815⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩),(.pair ⟨⟨true,true,626⟩,⟨false,true,298⟩,992⟩),true,[-1],[]⟩,
⟨⟨11,14,[-1],813⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,215⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩),(.pair ⟨⟨true,true,626⟩,⟨false,false,259⟩,991⟩),true,[-1],[]⟩,
⟨⟨11,20,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,215⟩,⟨true,false,298⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨11,22,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨false,false,259⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨11,23,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,215⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨11,24,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨11,28,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨11,29,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,215⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨11,30,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,215⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,1,[-1],172⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],.impossible,(.pair ⟨⟨true,false,148⟩,⟨false,true,148⟩,132⟩),false,[-1],[]⟩,
⟨⟨12,2,[-1],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨false,false,90⟩],(.bound ⟨false,false,617⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[-1],[]⟩,
⟨⟨12,3,[-1],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[-1],[]⟩,
⟨⟨12,5,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,6,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨false,false,90⟩],(.bound ⟨false,false,617⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,7,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,11,[-1],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],(.bound ⟨false,false,134⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[-1],[]⟩,
⟨⟨12,15,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],(.bound ⟨false,false,134⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,16,[-1],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨true,false,148⟩],(.bound ⟨true,false,617⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[-1],[]⟩,
⟨⟨12,17,[-1],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],.impossible,(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[-1],[]⟩,
⟨⟨12,19,[-1],699⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,633⟩,⟨true,true,629⟩,⟨true,true,90⟩],.impossible,(.pair ⟨⟨true,true,90⟩,⟨false,false,90⟩,29⟩),false,[-1],[]⟩,
⟨⟨12,20,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨true,false,148⟩],(.bound ⟨true,false,617⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,21,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,23,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],.impossible,(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨12,25,[-1],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨false,true,148⟩],(.bound ⟨true,false,134⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[-1],[]⟩,
⟨⟨12,29,[-1],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,633⟩,⟨false,true,629⟩,⟨false,true,148⟩],(.bound ⟨true,false,134⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[-1],[]⟩,
⟨⟨14,0,[-1],174⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩),(.pair ⟨⟨true,false,391⟩,⟨false,false,354⟩,359⟩),true,[-1],[]⟩,
⟨⟨14,1,[9],19⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,false,202⟩,⟨false,false,354⟩,156⟩),true,[9],[]⟩,
⟨⟨14,1,[5],55⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,354⟩,109⟩),true,[5],[]⟩,
⟨⟨14,1,[8],97⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,false,377⟩,⟨false,false,354⟩,346⟩),true,[8],[]⟩,
⟨⟨14,1,[1],131⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,354⟩,50⟩),true,[1],[]⟩,
⟨⟨14,1,[0],189⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,354⟩,788⟩),true,[0],[]⟩,
⟨⟨14,1,[4],477⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,354⟩,396⟩),true,[4],[]⟩,
⟨⟨14,1,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨14,1,[12,13],882⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,354⟩,698⟩),true,[12,13],[]⟩,
⟨⟨14,1,[3,7,11,15],937⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,354⟩,470⟩),true,[3,7,11,15],[]⟩,
⟨⟨14,1,[2,6,10,14],1208⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,354⟩,1015⟩),true,[2,6,10,14],[]⟩,
⟨⟨14,2,[-1],578⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩),(.pair ⟨⟨true,true,364⟩,⟨false,false,354⟩,308⟩),true,[-1],[]⟩,
⟨⟨14,3,[-1],1026⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,354⟩,368⟩),true,[-1],[]⟩,
⟨⟨14,4,[-1],174⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩),(.pair ⟨⟨true,false,391⟩,⟨false,false,354⟩,359⟩),true,[-1],[]⟩,
⟨⟨14,5,[-1],697⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,348⟩,⟨false,false,354⟩,299⟩),true,[-1],[]⟩,
⟨⟨14,6,[-1],578⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩),(.pair ⟨⟨true,true,364⟩,⟨false,false,354⟩,308⟩),true,[-1],[]⟩,
⟨⟨14,7,[-1],1026⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,354⟩,368⟩),true,[-1],[]⟩,
⟨⟨14,8,[-1],176⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩),(.pair ⟨⟨true,false,391⟩,⟨false,true,422⟩,360⟩),true,[-1],[]⟩,
⟨⟨14,9,[9],25⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,202⟩,⟨false,true,422⟩,157⟩),true,[9],[]⟩,
⟨⟨14,9,[5],73⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,422⟩,113⟩),true,[5],[]⟩,
⟨⟨14,9,[8],103⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,377⟩,⟨false,true,422⟩,348⟩),true,[8],[]⟩,
⟨⟨14,9,[1],141⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,422⟩,51⟩),true,[1],[]⟩,
⟨⟨14,9,[0],209⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,422⟩,792⟩),true,[0],[]⟩,
⟨⟨14,9,[4],485⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,422⟩,397⟩),true,[4],[]⟩,
⟨⟨14,9,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨14,9,[12,13],888⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,570⟩,⟨false,true,422⟩,699⟩),true,[12,13],[]⟩,
⟨⟨14,9,[3,7,11,15],945⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,422⟩,471⟩),true,[3,7,11,15],[]⟩,
⟨⟨14,9,[2,6,10,14],1228⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,422⟩,1019⟩),true,[2,6,10,14],[]⟩,
⟨⟨14,10,[-1],581⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,364⟩,⟨false,true,422⟩,309⟩),true,[-1],[]⟩,
⟨⟨14,11,[-1],1028⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩),(.pair ⟨⟨true,true,400⟩,⟨false,true,422⟩,370⟩),true,[-1],[]⟩,
⟨⟨14,12,[-1],176⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩),(.pair ⟨⟨true,false,391⟩,⟨false,true,422⟩,360⟩),true,[-1],[]⟩,
⟨⟨14,13,[-1],698⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,348⟩,⟨false,true,422⟩,300⟩),true,[-1],[]⟩,
⟨⟨14,14,[-1],581⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,364⟩,⟨false,true,422⟩,309⟩),true,[-1],[]⟩,
⟨⟨14,15,[-1],1028⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨false,false,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩),(.pair ⟨⟨true,true,400⟩,⟨false,true,422⟩,370⟩),true,[-1],[]⟩,
⟨⟨14,16,[-1],173⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩),(.pair ⟨⟨true,false,391⟩,⟨false,false,348⟩,358⟩),true,[-1],[]⟩,
⟨⟨14,17,[9],17⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,202⟩,⟨false,false,348⟩,155⟩),true,[9],[]⟩,
⟨⟨14,17,[5],54⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,348⟩,108⟩),true,[5],[]⟩,
⟨⟨14,17,[8],95⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,377⟩,⟨false,false,348⟩,345⟩),true,[8],[]⟩,
⟨⟨14,17,[1],129⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,348⟩,49⟩),true,[1],[]⟩,
⟨⟨14,17,[0],187⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,348⟩,787⟩),true,[0],[]⟩,
⟨⟨14,17,[4],476⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,348⟩,395⟩),true,[4],[]⟩,
⟨⟨14,17,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨14,17,[12,13],881⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,348⟩,697⟩),true,[12,13],[]⟩
]

private theorem good_0 : ∀ r ∈ chunk_0, rowGood r := by
  decide +kernel

private def chunk_1 : List Row := [
⟨⟨14,17,[3,7,11,15],935⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,348⟩,469⟩),true,[3,7,11,15],[]⟩,
⟨⟨14,17,[2,6,10,14],1206⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,348⟩,1014⟩),true,[2,6,10,14],[]⟩,
⟨⟨14,18,[-1],577⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩),(.pair ⟨⟨true,true,364⟩,⟨false,false,348⟩,307⟩),true,[-1],[]⟩,
⟨⟨14,19,[-1],1025⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,348⟩,367⟩),true,[-1],[]⟩,
⟨⟨14,20,[-1],175⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩),(.pair ⟨⟨true,false,391⟩,⟨false,false,444⟩,362⟩),true,[-1],[]⟩,
⟨⟨14,21,[9],20⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,202⟩,⟨false,false,444⟩,158⟩),true,[9],[]⟩,
⟨⟨14,21,[5],57⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,444⟩,117⟩),true,[5],[]⟩,
⟨⟨14,21,[8],98⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,377⟩,⟨false,false,444⟩,349⟩),true,[8],[]⟩,
⟨⟨14,21,[1],133⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,444⟩,52⟩),true,[1],[]⟩,
⟨⟨14,21,[0],192⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,444⟩,796⟩),true,[0],[]⟩,
⟨⟨14,21,[4],478⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,444⟩,398⟩),true,[4],[]⟩,
⟨⟨14,21,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨14,21,[12,13],883⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,444⟩,700⟩),true,[12,13],[]⟩,
⟨⟨14,21,[3,7,11,15],939⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,444⟩,472⟩),true,[3,7,11,15],[]⟩,
⟨⟨14,21,[2,6,10,14],1210⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,444⟩,1023⟩),true,[2,6,10,14],[]⟩,
⟨⟨14,22,[-1],579⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩),(.pair ⟨⟨true,true,364⟩,⟨false,false,444⟩,310⟩),true,[-1],[]⟩,
⟨⟨14,23,[-1],1027⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,444⟩,371⟩),true,[-1],[]⟩,
⟨⟨14,24,[-1],173⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,391⟩,⟨false,false,348⟩,358⟩),true,[-1],[]⟩,
⟨⟨14,25,[-1],816⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,444⟩,⟨false,false,348⟩,450⟩),true,[-1],[]⟩,
⟨⟨14,26,[-1],577⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩),(.pair ⟨⟨true,true,364⟩,⟨false,false,348⟩,307⟩),true,[-1],[]⟩,
⟨⟨14,27,[-1],1025⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,348⟩,367⟩),true,[-1],[]⟩,
⟨⟨14,28,[-1],177⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,false,391⟩,⟨false,true,436⟩,361⟩),true,[-1],[]⟩,
⟨⟨14,29,[9],23⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,false,202⟩,⟨false,true,276⟩,154⟩),true,[9],[]⟩,
⟨⟨14,29,[5],67⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,276⟩,103⟩),true,[5],[]⟩,
⟨⟨14,29,[8],100⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,false,377⟩,⟨false,true,276⟩,344⟩),true,[8],[]⟩,
⟨⟨14,29,[1],137⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,276⟩,45⟩),true,[1],[]⟩,
⟨⟨14,29,[0],202⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,276⟩,782⟩),true,[0],[]⟩,
⟨⟨14,29,[4],482⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,276⟩,391⟩),true,[4],[]⟩,
⟨⟨14,29,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨14,29,[12,13],886⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,570⟩,⟨false,true,276⟩,696⟩),true,[12,13],[]⟩,
⟨⟨14,29,[3,7,11,15],943⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,276⟩,465⟩),true,[3,7,11,15],[]⟩,
⟨⟨14,29,[2,6,10,14],1221⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,276⟩,1010⟩),true,[2,6,10,14],[]⟩,
⟨⟨14,30,[-1],580⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩),(.pair ⟨⟨true,true,364⟩,⟨false,true,278⟩,306⟩),true,[-1],[]⟩,
⟨⟨14,31,[-1],1029⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,221⟩,⟨true,true,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩),(.pair ⟨⟨true,true,400⟩,⟨false,true,421⟩,369⟩),true,[-1],[]⟩,
⟨⟨14,32,[-1],622⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,354⟩,192⟩),true,[-1],[]⟩,
⟨⟨14,33,[-1],622⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,354⟩,192⟩),true,[-1],[]⟩,
⟨⟨14,34,[-1],622⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,354⟩,192⟩),true,[-1],[]⟩,
⟨⟨14,35,[-1],1026⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,354⟩,368⟩),true,[-1],[]⟩,
⟨⟨14,36,[-1],622⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,442⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,354⟩,192⟩),true,[-1],[]⟩,
⟨⟨14,37,[-1],622⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,323⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,354⟩,192⟩),true,[-1],[]⟩,
⟨⟨14,38,[-1],622⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,333⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,354⟩,192⟩),true,[-1],[]⟩,
⟨⟨14,39,[-1],1026⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨true,false,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,428⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,354⟩,368⟩),true,[-1],[]⟩,
⟨⟨14,40,[-1],628⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,422⟩,194⟩),true,[-1],[]⟩,
⟨⟨14,41,[-1],628⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,422⟩,194⟩),true,[-1],[]⟩,
⟨⟨14,42,[-1],628⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,422⟩,194⟩),true,[-1],[]⟩,
⟨⟨14,43,[-1],1028⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩),(.pair ⟨⟨true,true,400⟩,⟨false,true,422⟩,370⟩),true,[-1],[]⟩,
⟨⟨14,44,[-1],628⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,386⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,422⟩,194⟩),true,[-1],[]⟩,
⟨⟨14,45,[-1],628⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,329⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,422⟩,194⟩),true,[-1],[]⟩,
⟨⟨14,46,[-1],628⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,340⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,422⟩,194⟩),true,[-1],[]⟩,
⟨⟨14,47,[-1],1028⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨false,true,354⟩,⟨false,true,422⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,401⟩),(.pair ⟨⟨true,true,400⟩,⟨false,true,422⟩,370⟩),true,[-1],[]⟩,
⟨⟨14,48,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨14,49,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨14,50,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨14,51,[-1],1025⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,348⟩,367⟩),true,[-1],[]⟩,
⟨⟨14,52,[-1],623⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,378⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,444⟩,197⟩),true,[-1],[]⟩,
⟨⟨14,53,[-1],623⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,353⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,444⟩,197⟩),true,[-1],[]⟩,
⟨⟨14,54,[-1],623⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,368⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,444⟩,197⟩),true,[-1],[]⟩,
⟨⟨14,55,[-1],1027⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨false,false,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,387⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,444⟩,371⟩),true,[-1],[]⟩,
⟨⟨14,56,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨14,57,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨14,58,[-1],621⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩),(.pair ⟨⟨true,true,221⟩,⟨false,false,348⟩,191⟩),true,[-1],[]⟩,
⟨⟨14,59,[-1],1025⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨false,false,348⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩),(.pair ⟨⟨true,true,400⟩,⟨false,false,348⟩,367⟩),true,[-1],[]⟩,
⟨⟨14,60,[-1],629⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,436⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,436⟩,196⟩),true,[-1],[]⟩,
⟨⟨14,61,[-1],625⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨false,true,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,276⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,276⟩,189⟩),true,[-1],[]⟩,
⟨⟨14,62,[-1],626⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,278⟩),(.pair ⟨⟨true,true,221⟩,⟨false,true,278⟩,190⟩),true,[-1],[]⟩,
⟨⟨14,63,[-1],1029⟩,[⟨false,false,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,221⟩,⟨true,false,354⟩,⟨true,true,444⟩,⟨true,true,348⟩,⟨true,false,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,421⟩),(.pair ⟨⟨true,true,400⟩,⟨false,true,421⟩,369⟩),true,[-1],[]⟩,
⟨⟨15,0,[-1],327⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩),(.pair ⟨⟨true,false,527⟩,⟨false,false,264⟩,539⟩),true,[-1],[]⟩,
⟨⟨15,1,[-1],332⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩),(.pair ⟨⟨true,false,527⟩,⟨false,true,597⟩,545⟩),true,[-1],[]⟩,
⟨⟨15,2,[-1],327⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩),(.pair ⟨⟨true,false,527⟩,⟨false,false,264⟩,539⟩),true,[-1],[]⟩,
⟨⟨15,3,[-1],327⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩),(.pair ⟨⟨true,false,527⟩,⟨false,false,264⟩,539⟩),true,[-1],[]⟩,
⟨⟨15,4,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨15,5,[-1],844⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,597⟩,977⟩),true,[-1],[]⟩,
⟨⟨15,6,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨15,7,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨15,8,[-1],607⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩),(.pair ⟨⟨true,true,372⟩,⟨false,false,264⟩,312⟩),true,[-1],[]⟩,
⟨⟨15,9,[-1],1184⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩),(.pair ⟨⟨true,true,722⟩,⟨false,true,597⟩,1194⟩),true,[-1],[]⟩,
⟨⟨15,10,[-1],773⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩),(.pair ⟨⟨true,true,647⟩,⟨false,false,264⟩,1087⟩),true,[-1],[]⟩,
⟨⟨15,11,[-1],603⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩),(.pair ⟨⟨true,true,282⟩,⟨false,false,264⟩,252⟩),true,[-1],[]⟩,
⟨⟨15,12,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨15,13,[-1],844⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,597⟩,977⟩),true,[-1],[]⟩,
⟨⟨15,14,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨15,15,[-1],836⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,264⟩,968⟩),true,[-1],[]⟩,
⟨⟨15,16,[-1],849⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,264⟩,981⟩),true,[-1],[]⟩,
⟨⟨15,17,[-1],855⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩),(.pair ⟨⟨true,true,614⟩,⟨false,true,597⟩,986⟩),true,[-1],[]⟩,
⟨⟨15,18,[-1],849⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,264⟩,981⟩),true,[-1],[]⟩,
⟨⟨15,19,[-1],849⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,264⟩,981⟩),true,[-1],[]⟩,
⟨⟨15,20,[-1],849⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,264⟩,981⟩),true,[-1],[]⟩,
⟨⟨15,21,[-1],855⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩),(.pair ⟨⟨true,true,614⟩,⟨false,true,597⟩,986⟩),true,[-1],[]⟩,
⟨⟨15,22,[-1],849⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,264⟩,981⟩),true,[-1],[]⟩,
⟨⟨15,23,[-1],849⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,264⟩,981⟩),true,[-1],[]⟩,
⟨⟨15,24,[-1],1098⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,264⟩,753⟩),true,[-1],[]⟩,
⟨⟨15,25,[-1],1104⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩),(.pair ⟨⟨true,true,578⟩,⟨false,true,597⟩,759⟩),true,[-1],[]⟩,
⟨⟨15,26,[-1],1098⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,264⟩,753⟩),true,[-1],[]⟩,
⟨⟨15,27,[-1],1098⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,264⟩,753⟩),true,[-1],[]⟩,
⟨⟨15,28,[-1],1098⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,264⟩,753⟩),true,[-1],[]⟩,
⟨⟨15,29,[-1],1104⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩),(.pair ⟨⟨true,true,578⟩,⟨false,true,597⟩,759⟩),true,[-1],[]⟩
]

private theorem good_1 : ∀ r ∈ chunk_1, rowGood r := by
  decide +kernel

private def chunk_2 : List Row := [
⟨⟨15,30,[-1],1098⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,264⟩,753⟩),true,[-1],[]⟩,
⟨⟨15,31,[-1],1098⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,264⟩,753⟩),true,[-1],[]⟩,
⟨⟨15,32,[-1],329⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩),(.pair ⟨⟨true,false,527⟩,⟨false,false,572⟩,544⟩),true,[-1],[]⟩,
⟨⟨15,33,[-1],332⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩),(.pair ⟨⟨true,false,527⟩,⟨false,true,597⟩,545⟩),true,[-1],[]⟩,
⟨⟨15,34,[-1],330⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩),(.pair ⟨⟨true,false,527⟩,⟨false,false,656⟩,546⟩),true,[-1],[]⟩,
⟨⟨15,35,[-1],334⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩),(.pair ⟨⟨true,false,527⟩,⟨false,true,537⟩,542⟩),true,[-1],[]⟩,
⟨⟨15,36,[-1],837⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,284⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,572⟩,975⟩),true,[-1],[]⟩,
⟨⟨15,37,[-1],844⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,243⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,597⟩,977⟩),true,[-1],[]⟩,
⟨⟨15,38,[-1],838⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,227⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,656⟩,978⟩),true,[-1],[]⟩,
⟨⟨15,39,[-1],847⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,257⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,537⟩,972⟩),true,[-1],[]⟩,
⟨⟨15,40,[-1],608⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩),(.pair ⟨⟨true,true,372⟩,⟨false,false,572⟩,313⟩),true,[-1],[]⟩,
⟨⟨15,41,[-1],1184⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩),(.pair ⟨⟨true,true,722⟩,⟨false,true,597⟩,1194⟩),true,[-1],[]⟩,
⟨⟨15,42,[-1],774⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩),(.pair ⟨⟨true,true,647⟩,⟨false,false,656⟩,1089⟩),true,[-1],[]⟩,
⟨⟨15,43,[-1],604⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩),(.pair ⟨⟨true,true,282⟩,⟨false,true,537⟩,253⟩),true,[-1],[]⟩,
⟨⟨15,44,[-1],837⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,372⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,572⟩,975⟩),true,[-1],[]⟩,
⟨⟨15,45,[-1],844⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,722⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,597⟩,977⟩),true,[-1],[]⟩,
⟨⟨15,46,[-1],838⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,647⟩),(.pair ⟨⟨true,true,613⟩,⟨false,false,656⟩,978⟩),true,[-1],[]⟩,
⟨⟨15,47,[-1],847⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,282⟩),(.pair ⟨⟨true,true,613⟩,⟨false,true,537⟩,972⟩),true,[-1],[]⟩,
⟨⟨15,48,[-1],851⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,572⟩,985⟩),true,[-1],[]⟩,
⟨⟨15,49,[-1],855⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩),(.pair ⟨⟨true,true,614⟩,⟨false,true,597⟩,986⟩),true,[-1],[]⟩,
⟨⟨15,50,[-1],852⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,656⟩,987⟩),true,[-1],[]⟩,
⟨⟨15,51,[-1],856⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩),(.pair ⟨⟨true,true,614⟩,⟨false,true,537⟩,984⟩),true,[-1],[]⟩,
⟨⟨15,52,[-1],851⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,344⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,572⟩,985⟩),true,[-1],[]⟩,
⟨⟨15,53,[-1],855⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,720⟩),(.pair ⟨⟨true,true,614⟩,⟨false,true,597⟩,986⟩),true,[-1],[]⟩,
⟨⟨15,54,[-1],852⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,592⟩),(.pair ⟨⟨true,true,614⟩,⟨false,false,656⟩,987⟩),true,[-1],[]⟩,
⟨⟨15,55,[-1],856⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,350⟩),(.pair ⟨⟨true,true,614⟩,⟨false,true,537⟩,984⟩),true,[-1],[]⟩,
⟨⟨15,56,[-1],1100⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,572⟩,758⟩),true,[-1],[]⟩,
⟨⟨15,57,[-1],1104⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨false,false,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩),(.pair ⟨⟨true,true,578⟩,⟨false,true,597⟩,759⟩),true,[-1],[]⟩,
⟨⟨15,58,[-1],1101⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,656⟩,760⟩),true,[-1],[]⟩,
⟨⟨15,59,[-1],1105⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,true,613⟩,⟨true,true,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩),(.pair ⟨⟨true,true,578⟩,⟨false,true,537⟩,756⟩),true,[-1],[]⟩,
⟨⟨15,60,[-1],1100⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨true,false,597⟩],(.bound ⟨false,false,256⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,572⟩,758⟩),true,[-1],[]⟩,
⟨⟨15,61,[-1],1104⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨false,true,572⟩,⟨false,true,597⟩],(.bound ⟨false,false,98⟩),(.pair ⟨⟨true,true,578⟩,⟨false,true,597⟩,759⟩),true,[-1],[]⟩,
⟨⟨15,62,[-1],1101⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨false,false,656⟩],(.bound ⟨false,false,361⟩),(.pair ⟨⟨true,true,578⟩,⟨false,false,656⟩,760⟩),true,[-1],[]⟩,
⟨⟨15,63,[-1],1105⟩,[⟨true,true,215⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,false,613⟩,⟨true,false,572⟩,⟨true,true,656⟩],(.bound ⟨false,false,242⟩),(.pair ⟨⟨true,true,578⟩,⟨false,true,537⟩,756⟩),true,[-1],[]⟩,
⟨⟨17,0,[-1],322⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩),(.pair ⟨⟨true,false,402⟩,⟨false,false,330⟩,373⟩),true,[-1],[]⟩,
⟨⟨17,1,[5],53⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,330⟩,105⟩),true,[5],[]⟩,
⟨⟨17,1,[1],128⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,330⟩,47⟩),true,[1],[]⟩,
⟨⟨17,1,[0],186⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,330⟩,784⟩),true,[0],[]⟩,
⟨⟨17,1,[4],475⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,330⟩,393⟩),true,[4],[]⟩,
⟨⟨17,1,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨17,1,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨17,1,[3,7],934⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,330⟩,467⟩),true,[3,7],[]⟩,
⟨⟨17,1,[2,6],1205⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,330⟩,1012⟩),true,[2,6],[]⟩,
⟨⟨17,2,[-1],672⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,330⟩,303⟩),true,[-1],[]⟩,
⟨⟨17,3,[-1],1014⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,330⟩,382⟩),true,[-1],[]⟩,
⟨⟨17,4,[-1],322⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩),(.pair ⟨⟨true,false,402⟩,⟨false,false,330⟩,373⟩),true,[-1],[]⟩,
⟨⟨17,5,[-1],678⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,321⟩,⟨false,false,330⟩,285⟩),true,[-1],[]⟩,
⟨⟨17,6,[-1],672⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,330⟩,303⟩),true,[-1],[]⟩,
⟨⟨17,7,[-1],1014⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,330⟩,382⟩),true,[-1],[]⟩,
⟨⟨17,8,[-1],324⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩),(.pair ⟨⟨true,false,402⟩,⟨false,true,445⟩,374⟩),true,[-1],[]⟩,
⟨⟨17,9,[5],79⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,445⟩,118⟩),true,[5],[]⟩,
⟨⟨17,9,[1],143⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,445⟩,53⟩),true,[1],[]⟩,
⟨⟨17,9,[0],213⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,445⟩,797⟩),true,[0],[]⟩,
⟨⟨17,9,[4],488⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,445⟩,399⟩),true,[4],[]⟩,
⟨⟨17,9,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨17,9,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨17,9,[3,7],948⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,445⟩,473⟩),true,[3,7],[]⟩,
⟨⟨17,9,[2,6],1233⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,445⟩,1024⟩),true,[2,6],[]⟩,
⟨⟨17,10,[-1],675⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,352⟩,⟨false,true,445⟩,304⟩),true,[-1],[]⟩,
⟨⟨17,11,[-1],1017⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩),(.pair ⟨⟨true,true,413⟩,⟨false,true,445⟩,384⟩),true,[-1],[]⟩,
⟨⟨17,12,[-1],324⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩),(.pair ⟨⟨true,false,402⟩,⟨false,true,445⟩,374⟩),true,[-1],[]⟩,
⟨⟨17,13,[-1],679⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,321⟩,⟨false,true,445⟩,286⟩),true,[-1],[]⟩,
⟨⟨17,14,[-1],675⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,352⟩,⟨false,true,445⟩,304⟩),true,[-1],[]⟩,
⟨⟨17,15,[-1],1017⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨false,false,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩),(.pair ⟨⟨true,true,413⟩,⟨false,true,445⟩,384⟩),true,[-1],[]⟩,
⟨⟨17,16,[-1],321⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩),(.pair ⟨⟨true,false,402⟩,⟨false,false,321⟩,372⟩),true,[-1],[]⟩,
⟨⟨17,17,[5],52⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,321⟩,104⟩),true,[5],[]⟩,
⟨⟨17,17,[1],127⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,321⟩,46⟩),true,[1],[]⟩,
⟨⟨17,17,[0],185⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,321⟩,783⟩),true,[0],[]⟩,
⟨⟨17,17,[4],474⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,321⟩,392⟩),true,[4],[]⟩,
⟨⟨17,17,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨17,17,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨17,17,[3,7],933⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,321⟩,466⟩),true,[3,7],[]⟩,
⟨⟨17,17,[2,6],1204⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,321⟩,1011⟩),true,[2,6],[]⟩,
⟨⟨17,18,[-1],671⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,321⟩,302⟩),true,[-1],[]⟩,
⟨⟨17,19,[-1],1013⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,321⟩,381⟩),true,[-1],[]⟩,
⟨⟨17,20,[-1],323⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩),(.pair ⟨⟨true,false,402⟩,⟨false,false,472⟩,376⟩),true,[-1],[]⟩,
⟨⟨17,21,[5],61⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,472⟩,123⟩),true,[5],[]⟩,
⟨⟨17,21,[1],135⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,472⟩,55⟩),true,[1],[]⟩,
⟨⟨17,21,[0],197⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,472⟩,802⟩),true,[0],[]⟩,
⟨⟨17,21,[4],480⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,472⟩,401⟩),true,[4],[]⟩,
⟨⟨17,21,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨17,21,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨17,21,[3,7],941⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,472⟩,475⟩),true,[3,7],[]⟩,
⟨⟨17,21,[2,6],1216⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,472⟩,1028⟩),true,[2,6],[]⟩,
⟨⟨17,22,[-1],673⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,472⟩,305⟩),true,[-1],[]⟩,
⟨⟨17,23,[-1],1015⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,472⟩,385⟩),true,[-1],[]⟩,
⟨⟨17,24,[-1],321⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,402⟩,⟨false,false,321⟩,372⟩),true,[-1],[]⟩,
⟨⟨17,25,[-1],1167⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,472⟩,⟨false,false,321⟩,512⟩),true,[-1],[]⟩,
⟨⟨17,26,[-1],671⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,321⟩,302⟩),true,[-1],[]⟩,
⟨⟨17,27,[-1],1013⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,321⟩,381⟩),true,[-1],[]⟩,
⟨⟨17,28,[-1],325⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,false,402⟩,⟨false,true,458⟩,375⟩),true,[-1],[]⟩,
⟨⟨17,29,[5],69⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,230⟩,99⟩),true,[5],[]⟩,
⟨⟨17,29,[1],138⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,230⟩,42⟩),true,[1],[]⟩,
⟨⟨17,29,[0],204⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,230⟩,777⟩),true,[0],[]⟩,
⟨⟨17,29,[4],483⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,230⟩,389⟩),true,[4],[]⟩,
⟨⟨17,29,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩
]

private theorem good_2 : ∀ r ∈ chunk_2, rowGood r := by
  decide +kernel

private def chunk_3 : List Row := [
⟨⟨17,29,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨17,29,[3,7],944⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,230⟩,463⟩),true,[3,7],[]⟩,
⟨⟨17,29,[2,6],1224⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,230⟩,1006⟩),true,[2,6],[]⟩,
⟨⟨17,30,[-1],674⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩),(.pair ⟨⟨true,true,352⟩,⟨false,true,235⟩,301⟩),true,[-1],[]⟩,
⟨⟨17,31,[-1],1016⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,254⟩,⟨true,true,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩),(.pair ⟨⟨true,true,413⟩,⟨false,true,441⟩,383⟩),true,[-1],[]⟩,
⟨⟨17,32,[-1],569⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,330⟩,230⟩),true,[-1],[]⟩,
⟨⟨17,33,[-1],569⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,330⟩,230⟩),true,[-1],[]⟩,
⟨⟨17,34,[-1],672⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,330⟩,303⟩),true,[-1],[]⟩,
⟨⟨17,35,[-1],1014⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,330⟩,382⟩),true,[-1],[]⟩,
⟨⟨17,36,[-1],569⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,468⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,330⟩,230⟩),true,[-1],[]⟩,
⟨⟨17,37,[-1],569⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,286⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,330⟩,230⟩),true,[-1],[]⟩,
⟨⟨17,38,[-1],672⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,309⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,330⟩,303⟩),true,[-1],[]⟩,
⟨⟨17,39,[-1],1014⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨true,false,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,448⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,330⟩,382⟩),true,[-1],[]⟩,
⟨⟨17,40,[-1],574⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,445⟩,232⟩),true,[-1],[]⟩,
⟨⟨17,41,[-1],574⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,445⟩,232⟩),true,[-1],[]⟩,
⟨⟨17,42,[-1],675⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,352⟩,⟨false,true,445⟩,304⟩),true,[-1],[]⟩,
⟨⟨17,43,[-1],1017⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩),(.pair ⟨⟨true,true,413⟩,⟨false,true,445⟩,384⟩),true,[-1],[]⟩,
⟨⟨17,44,[-1],574⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,392⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,445⟩,232⟩),true,[-1],[]⟩,
⟨⟨17,45,[-1],574⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,285⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,445⟩,232⟩),true,[-1],[]⟩,
⟨⟨17,46,[-1],675⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,307⟩),(.pair ⟨⟨true,true,352⟩,⟨false,true,445⟩,304⟩),true,[-1],[]⟩,
⟨⟨17,47,[-1],1017⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨false,true,330⟩,⟨false,true,445⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,415⟩),(.pair ⟨⟨true,true,413⟩,⟨false,true,445⟩,384⟩),true,[-1],[]⟩,
⟨⟨17,48,[-1],568⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,321⟩,229⟩),true,[-1],[]⟩,
⟨⟨17,49,[-1],568⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,321⟩,229⟩),true,[-1],[]⟩,
⟨⟨17,50,[-1],671⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,321⟩,302⟩),true,[-1],[]⟩,
⟨⟨17,51,[-1],1013⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,321⟩,381⟩),true,[-1],[]⟩,
⟨⟨17,52,[-1],570⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,374⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,472⟩,235⟩),true,[-1],[]⟩,
⟨⟨17,53,[-1],570⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,332⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,472⟩,235⟩),true,[-1],[]⟩,
⟨⟨17,54,[-1],673⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,358⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,472⟩,305⟩),true,[-1],[]⟩,
⟨⟨17,55,[-1],1015⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨false,false,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,393⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,472⟩,385⟩),true,[-1],[]⟩,
⟨⟨17,56,[-1],568⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,321⟩,229⟩),true,[-1],[]⟩,
⟨⟨17,57,[-1],568⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨false,false,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,254⟩,⟨false,false,321⟩,229⟩),true,[-1],[]⟩,
⟨⟨17,58,[-1],671⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩),(.pair ⟨⟨true,true,352⟩,⟨false,false,321⟩,302⟩),true,[-1],[]⟩,
⟨⟨17,59,[-1],1013⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨false,false,321⟩,⟨true,true,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩),(.pair ⟨⟨true,true,413⟩,⟨false,false,321⟩,381⟩),true,[-1],[]⟩,
⟨⟨17,60,[-1],576⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨true,false,402⟩],(.bound ⟨true,false,458⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,458⟩,234⟩),true,[-1],[]⟩,
⟨⟨17,61,[-1],573⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨false,true,352⟩,⟨false,true,402⟩],(.bound ⟨true,false,230⟩),(.pair ⟨⟨true,true,254⟩,⟨false,true,230⟩,228⟩),true,[-1],[]⟩,
⟨⟨17,62,[-1],674⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨false,false,413⟩],(.bound ⟨true,false,235⟩),(.pair ⟨⟨true,true,352⟩,⟨false,true,235⟩,301⟩),true,[-1],[]⟩,
⟨⟨17,63,[-1],1016⟩,[⟨false,false,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,254⟩,⟨true,false,330⟩,⟨true,true,472⟩,⟨true,true,321⟩,⟨true,false,352⟩,⟨true,true,413⟩],(.bound ⟨true,false,441⟩),(.pair ⟨⟨true,true,413⟩,⟨false,true,441⟩,383⟩),true,[-1],[]⟩,
⟨⟨18,0,[-1],465⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,537⟩,956⟩),true,[-1],[]⟩,
⟨⟨18,1,[-1],464⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,564⟩,957⟩),true,[-1],[]⟩,
⟨⟨18,2,[-1],465⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,537⟩,956⟩),true,[-1],[]⟩,
⟨⟨18,3,[-1],465⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,537⟩,956⟩),true,[-1],[]⟩,
⟨⟨18,4,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,5,[-1],721⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,564⟩,1068⟩),true,[-1],[]⟩,
⟨⟨18,6,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,7,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,8,[-1],1081⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩),(.pair ⟨⟨true,true,399⟩,⟨false,true,537⟩,365⟩),true,[-1],[]⟩,
⟨⟨18,9,[-1],1033⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩),(.pair ⟨⟨true,true,725⟩,⟨false,true,564⟩,1199⟩),true,[-1],[]⟩,
⟨⟨18,10,[-1],908⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩),(.pair ⟨⟨true,true,706⟩,⟨false,true,537⟩,1167⟩),true,[-1],[]⟩,
⟨⟨18,11,[-1],618⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩),(.pair ⟨⟨true,true,165⟩,⟨false,true,537⟩,136⟩),true,[-1],[]⟩,
⟨⟨18,12,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,13,[-1],721⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,564⟩,1068⟩),true,[-1],[]⟩,
⟨⟨18,14,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,15,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,16,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,17,[-1],730⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,564⟩,1078⟩),true,[-1],[]⟩,
⟨⟨18,18,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,19,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,20,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,21,[-1],730⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,564⟩,1078⟩),true,[-1],[]⟩,
⟨⟨18,22,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,23,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,24,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,25,[-1],1160⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,564⟩,1122⟩),true,[-1],[]⟩,
⟨⟨18,26,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,27,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,28,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,29,[-1],1160⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,564⟩,1122⟩),true,[-1],[]⟩,
⟨⟨18,30,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,31,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,32,[-1],465⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,537⟩,956⟩),true,[-1],[]⟩,
⟨⟨18,33,[-1],464⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,564⟩,957⟩),true,[-1],[]⟩,
⟨⟨18,34,[-1],465⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,537⟩,956⟩),true,[-1],[]⟩,
⟨⟨18,35,[-1],465⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩),(.pair ⟨⟨true,false,611⟩,⟨false,true,537⟩,956⟩),true,[-1],[]⟩,
⟨⟨18,36,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,258⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,37,[-1],721⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,190⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,564⟩,1068⟩),true,[-1],[]⟩,
⟨⟨18,38,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,178⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,39,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,220⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,40,[-1],1081⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩),(.pair ⟨⟨true,true,399⟩,⟨false,true,537⟩,365⟩),true,[-1],[]⟩,
⟨⟨18,41,[-1],1033⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩),(.pair ⟨⟨true,true,725⟩,⟨false,true,564⟩,1199⟩),true,[-1],[]⟩,
⟨⟨18,42,[-1],908⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩),(.pair ⟨⟨true,true,706⟩,⟨false,true,537⟩,1167⟩),true,[-1],[]⟩,
⟨⟨18,43,[-1],618⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩),(.pair ⟨⟨true,true,165⟩,⟨false,true,537⟩,136⟩),true,[-1],[]⟩,
⟨⟨18,44,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,399⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,45,[-1],721⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,725⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,564⟩,1068⟩),true,[-1],[]⟩,
⟨⟨18,46,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,706⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,47,[-1],723⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,165⟩),(.pair ⟨⟨true,true,640⟩,⟨false,true,537⟩,1066⟩),true,[-1],[]⟩,
⟨⟨18,48,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,49,[-1],730⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,564⟩,1078⟩),true,[-1],[]⟩,
⟨⟨18,50,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,51,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,52,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,325⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,53,[-1],730⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,709⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,564⟩,1078⟩),true,[-1],[]⟩,
⟨⟨18,54,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,657⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,55,[-1],731⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,302⟩),(.pair ⟨⟨true,true,641⟩,⟨false,true,537⟩,1077⟩),true,[-1],[]⟩,
⟨⟨18,56,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,57,[-1],1160⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨false,false,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,564⟩,1122⟩),true,[-1],[]⟩,
⟨⟨18,58,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩
]

private theorem good_3 : ∀ r ∈ chunk_3, rowGood r := by
  decide +kernel

private def chunk_4 : List Row := [
⟨⟨18,59,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,true,640⟩,⟨true,true,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,60,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨true,false,564⟩],(.bound ⟨false,false,219⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,61,[-1],1160⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨false,true,566⟩,⟨false,true,564⟩],(.bound ⟨false,false,157⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,564⟩,1122⟩),true,[-1],[]⟩,
⟨⟨18,62,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨false,false,632⟩],(.bound ⟨false,false,379⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨18,63,[-1],1161⟩,[⟨true,true,222⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,false,640⟩,⟨true,false,566⟩,⟨true,true,632⟩],(.bound ⟨false,false,196⟩),(.pair ⟨⟨true,true,674⟩,⟨false,true,537⟩,1121⟩),true,[-1],[]⟩,
⟨⟨20,0,[-1],273⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩),(.pair ⟨⟨true,false,427⟩,⟨false,false,255⟩,411⟩),true,[-1],[]⟩,
⟨⟨20,1,[9],14⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,false,202⟩,⟨false,false,255⟩,152⟩),true,[9],[]⟩,
⟨⟨20,1,[5],48⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,255⟩,101⟩),true,[5],[]⟩,
⟨⟨20,1,[8],92⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,false,377⟩,⟨false,false,255⟩,342⟩),true,[8],[]⟩,
⟨⟨20,1,[1],124⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,255⟩,43⟩),true,[1],[]⟩,
⟨⟨20,1,[0],181⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,255⟩,779⟩),true,[0],[]⟩,
⟨⟨20,1,[4],471⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,255⟩,390⟩),true,[4],[]⟩,
⟨⟨20,1,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨20,1,[12,13],878⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,255⟩,695⟩),true,[12,13],[]⟩,
⟨⟨20,1,[2,3,6,7,10,11,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6,7,10,11,14,15],[]⟩,
⟨⟨20,2,[-1],658⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,255⟩,244⟩),true,[-1],[]⟩,
⟨⟨20,3,[-1],981⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,255⟩,457⟩),true,[-1],[]⟩,
⟨⟨20,4,[-1],273⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩),(.pair ⟨⟨true,false,427⟩,⟨false,false,255⟩,411⟩),true,[-1],[]⟩,
⟨⟨20,5,[-1],587⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,true,216⟩,⟨false,false,255⟩,186⟩),true,[-1],[]⟩,
⟨⟨20,6,[-1],658⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,255⟩,244⟩),true,[-1],[]⟩,
⟨⟨20,7,[-1],981⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,255⟩,457⟩),true,[-1],[]⟩,
⟨⟨20,8,[-1],276⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩),(.pair ⟨⟨true,false,427⟩,⟨false,true,509⟩,412⟩),true,[-1],[]⟩,
⟨⟨20,9,[9],26⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,202⟩,⟨false,true,509⟩,159⟩),true,[9],[]⟩,
⟨⟨20,9,[5],76⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,509⟩,126⟩),true,[5],[]⟩,
⟨⟨20,9,[8],104⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,377⟩,⟨false,true,509⟩,350⟩),true,[8],[]⟩,
⟨⟨20,9,[1],142⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,509⟩,57⟩),true,[1],[]⟩,
⟨⟨20,9,[0],212⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,509⟩,806⟩),true,[0],[]⟩,
⟨⟨20,9,[4],486⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,509⟩,402⟩),true,[4],[]⟩,
⟨⟨20,9,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨20,9,[12,13],889⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,570⟩,⟨false,true,509⟩,701⟩),true,[12,13],[]⟩,
⟨⟨20,9,[2,3,6,7,10,11,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6,7,10,11,14,15],[]⟩,
⟨⟨20,10,[-1],662⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,265⟩,⟨false,true,509⟩,245⟩),true,[-1],[]⟩,
⟨⟨20,11,[-1],984⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩),(.pair ⟨⟨true,true,447⟩,⟨false,true,509⟩,459⟩),true,[-1],[]⟩,
⟨⟨20,12,[-1],276⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩),(.pair ⟨⟨true,false,427⟩,⟨false,true,509⟩,412⟩),true,[-1],[]⟩,
⟨⟨20,13,[-1],588⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,216⟩,⟨false,true,509⟩,187⟩),true,[-1],[]⟩,
⟨⟨20,14,[-1],662⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,265⟩,⟨false,true,509⟩,245⟩),true,[-1],[]⟩,
⟨⟨20,15,[-1],984⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨false,false,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩),(.pair ⟨⟨true,true,447⟩,⟨false,true,509⟩,459⟩),true,[-1],[]⟩,
⟨⟨20,16,[-1],274⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩),(.pair ⟨⟨true,false,427⟩,⟨false,false,216⟩,410⟩),true,[-1],[]⟩,
⟨⟨20,17,[9],16⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,202⟩,⟨false,false,216⟩,151⟩),true,[9],[]⟩,
⟨⟨20,17,[5],50⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,216⟩,97⟩),true,[5],[]⟩,
⟨⟨20,17,[8],94⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,377⟩,⟨false,false,216⟩,341⟩),true,[8],[]⟩,
⟨⟨20,17,[1],126⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,216⟩,41⟩),true,[1],[]⟩,
⟨⟨20,17,[0],183⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,216⟩,775⟩),true,[0],[]⟩,
⟨⟨20,17,[4],473⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,216⟩,388⟩),true,[4],[]⟩,
⟨⟨20,17,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨20,17,[12,13],880⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,216⟩,694⟩),true,[12,13],[]⟩,
⟨⟨20,17,[2,3,6,7,10,11,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6,7,10,11,14,15],[]⟩,
⟨⟨20,18,[-1],659⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,216⟩,243⟩),true,[-1],[]⟩,
⟨⟨20,19,[-1],982⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,216⟩,456⟩),true,[-1],[]⟩,
⟨⟨20,20,[-1],275⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩),(.pair ⟨⟨true,false,427⟩,⟨false,false,553⟩,414⟩),true,[-1],[]⟩,
⟨⟨20,21,[9],21⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,202⟩,⟨false,false,553⟩,160⟩),true,[9],[]⟩,
⟨⟨20,21,[5],60⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,553⟩,130⟩),true,[5],[]⟩,
⟨⟨20,21,[8],99⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,377⟩,⟨false,false,553⟩,351⟩),true,[8],[]⟩,
⟨⟨20,21,[1],134⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,553⟩,59⟩),true,[1],[]⟩,
⟨⟨20,21,[0],196⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,553⟩,810⟩),true,[0],[]⟩,
⟨⟨20,21,[4],479⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,553⟩,404⟩),true,[4],[]⟩,
⟨⟨20,21,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨20,21,[12,13],885⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,553⟩,702⟩),true,[12,13],[]⟩,
⟨⟨20,21,[2,3,6,7,10,11,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6,7,10,11,14,15],[]⟩,
⟨⟨20,22,[-1],660⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,553⟩,246⟩),true,[-1],[]⟩,
⟨⟨20,23,[-1],983⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,553⟩,460⟩),true,[-1],[]⟩,
⟨⟨20,24,[-1],274⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,false,427⟩,⟨false,false,216⟩,410⟩),true,[-1],[]⟩,
⟨⟨20,25,[-1],1132⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,true,553⟩,⟨false,false,216⟩,651⟩),true,[-1],[]⟩,
⟨⟨20,26,[-1],659⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,216⟩,243⟩),true,[-1],[]⟩,
⟨⟨20,27,[-1],982⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,216⟩,456⟩),true,[-1],[]⟩,
⟨⟨20,28,[-1],277⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,false,427⟩,⟨false,true,512⟩,413⟩),true,[-1],[]⟩,
⟨⟨20,29,[9],24⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,false,202⟩,⟨false,true,138⟩,148⟩),true,[9],[]⟩,
⟨⟨20,29,[5],72⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,138⟩,93⟩),true,[5],[]⟩,
⟨⟨20,29,[8],102⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,false,377⟩,⟨false,true,138⟩,339⟩),true,[8],[]⟩,
⟨⟨20,29,[1],140⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,138⟩,39⟩),true,[1],[]⟩,
⟨⟨20,29,[0],208⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,138⟩,772⟩),true,[0],[]⟩,
⟨⟨20,29,[4],484⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,138⟩,386⟩),true,[4],[]⟩,
⟨⟨20,29,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨20,29,[12,13],887⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,true,570⟩,⟨false,true,138⟩,692⟩),true,[12,13],[]⟩,
⟨⟨20,29,[2,3,6,7,10,11,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6,7,10,11,14,15],[]⟩,
⟨⟨20,30,[-1],661⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩),(.pair ⟨⟨true,true,265⟩,⟨false,true,143⟩,242⟩),true,[-1],[]⟩,
⟨⟨20,31,[-1],985⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,223⟩,⟨true,true,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩),(.pair ⟨⟨true,true,447⟩,⟨false,true,484⟩,458⟩),true,[-1],[]⟩,
⟨⟨20,32,[-1],643⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,255⟩,214⟩),true,[-1],[]⟩,
⟨⟨20,33,[-1],643⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,255⟩,214⟩),true,[-1],[]⟩,
⟨⟨20,34,[-1],658⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,255⟩,244⟩),true,[-1],[]⟩,
⟨⟨20,35,[-1],981⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,255⟩,457⟩),true,[-1],[]⟩,
⟨⟨20,36,[-1],643⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,255⟩,214⟩),true,[-1],[]⟩,
⟨⟨20,37,[-1],643⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,225⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,255⟩,214⟩),true,[-1],[]⟩,
⟨⟨20,38,[-1],658⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,250⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,255⟩,244⟩),true,[-1],[]⟩,
⟨⟨20,39,[-1],981⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨true,false,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,499⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,255⟩,457⟩),true,[-1],[]⟩,
⟨⟨20,40,[-1],650⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,509⟩,217⟩),true,[-1],[]⟩,
⟨⟨20,41,[-1],650⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,509⟩,217⟩),true,[-1],[]⟩,
⟨⟨20,42,[-1],662⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,265⟩,⟨false,true,509⟩,245⟩),true,[-1],[]⟩,
⟨⟨20,43,[-1],984⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩),(.pair ⟨⟨true,true,447⟩,⟨false,true,509⟩,459⟩),true,[-1],[]⟩,
⟨⟨20,44,[-1],650⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,420⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,509⟩,217⟩),true,[-1],[]⟩,
⟨⟨20,45,[-1],650⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,186⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,509⟩,217⟩),true,[-1],[]⟩,
⟨⟨20,46,[-1],662⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,205⟩),(.pair ⟨⟨true,true,265⟩,⟨false,true,509⟩,245⟩),true,[-1],[]⟩,
⟨⟨20,47,[-1],984⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨false,true,255⟩,⟨false,true,509⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,461⟩),(.pair ⟨⟨true,true,447⟩,⟨false,true,509⟩,459⟩),true,[-1],[]⟩,
⟨⟨20,48,[-1],644⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,216⟩,212⟩),true,[-1],[]⟩,
⟨⟨20,49,[-1],644⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,216⟩,212⟩),true,[-1],[]⟩,
⟨⟨20,50,[-1],659⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,216⟩,243⟩),true,[-1],[]⟩
]

private theorem good_4 : ∀ r ∈ chunk_4, rowGood r := by
  decide +kernel

private def chunk_5 : List Row := [
⟨⟨20,51,[-1],982⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,216⟩,456⟩),true,[-1],[]⟩,
⟨⟨20,52,[-1],647⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,366⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,553⟩,219⟩),true,[-1],[]⟩,
⟨⟨20,53,[-1],647⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,290⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,553⟩,219⟩),true,[-1],[]⟩,
⟨⟨20,54,[-1],660⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,335⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,553⟩,246⟩),true,[-1],[]⟩,
⟨⟨20,55,[-1],983⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨false,false,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,406⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,553⟩,460⟩),true,[-1],[]⟩,
⟨⟨20,56,[-1],644⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,216⟩,212⟩),true,[-1],[]⟩,
⟨⟨20,57,[-1],644⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,true,223⟩,⟨false,false,216⟩,212⟩),true,[-1],[]⟩,
⟨⟨20,58,[-1],659⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩),(.pair ⟨⟨true,true,265⟩,⟨false,false,216⟩,243⟩),true,[-1],[]⟩,
⟨⟨20,59,[-1],982⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨false,false,216⟩,⟨true,true,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩),(.pair ⟨⟨true,true,447⟩,⟨false,false,216⟩,456⟩),true,[-1],[]⟩,
⟨⟨20,60,[-1],652⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,512⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,512⟩,218⟩),true,[-1],[]⟩,
⟨⟨20,61,[-1],649⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨false,true,265⟩,⟨false,true,427⟩],(.bound ⟨true,false,138⟩),(.pair ⟨⟨true,true,223⟩,⟨false,true,138⟩,211⟩),true,[-1],[]⟩,
⟨⟨20,62,[-1],661⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨false,false,447⟩],(.bound ⟨true,false,143⟩),(.pair ⟨⟨true,true,265⟩,⟨false,true,143⟩,242⟩),true,[-1],[]⟩,
⟨⟨20,63,[-1],985⟩,[⟨false,false,577⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩),(.pair ⟨⟨true,true,447⟩,⟨false,true,484⟩,458⟩),true,[-1],[]⟩,
⟨⟨21,0,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,1,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,2,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,3,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,4,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,5,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,6,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,7,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,8,[-1],591⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩),(.pair ⟨⟨true,true,237⟩,⟨false,true,537⟩,222⟩),true,[-1],[]⟩,
⟨⟨21,9,[-1],707⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩),(.pair ⟨⟨true,true,15⟩,⟨false,true,537⟩,12⟩),true,[-1],[]⟩,
⟨⟨21,10,[-1],601⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩),(.pair ⟨⟨true,true,11⟩,⟨false,true,537⟩,6⟩),true,[-1],[]⟩,
⟨⟨21,11,[-1],1007⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩),(.pair ⟨⟨true,true,717⟩,⟨false,true,537⟩,1186⟩),true,[-1],[]⟩,
⟨⟨21,12,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,13,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,14,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,15,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨false,false,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,16,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,17,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,18,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,19,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,20,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,21,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,22,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,23,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,24,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,25,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,26,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,27,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,28,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,29,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,30,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,31,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,true,634⟩,⟨true,true,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,32,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,33,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,34,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,35,[-1],6⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩),(.pair ⟨⟨true,false,176⟩,⟨false,true,537⟩,140⟩),true,[-1],[]⟩,
⟨⟨21,36,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,37,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,127⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,38,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,114⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,39,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨true,false,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,154⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,40,[-1],591⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩),(.pair ⟨⟨true,true,237⟩,⟨false,true,537⟩,222⟩),true,[-1],[]⟩,
⟨⟨21,41,[-1],707⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩),(.pair ⟨⟨true,true,15⟩,⟨false,true,537⟩,12⟩),true,[-1],[]⟩,
⟨⟨21,42,[-1],601⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩),(.pair ⟨⟨true,true,11⟩,⟨false,true,537⟩,6⟩),true,[-1],[]⟩,
⟨⟨21,43,[-1],1007⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩),(.pair ⟨⟨true,true,717⟩,⟨false,true,537⟩,1186⟩),true,[-1],[]⟩,
⟨⟨21,44,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,237⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,45,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,15⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,46,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,11⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,47,[-1],765⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨false,true,568⟩,⟨false,true,176⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,717⟩),(.pair ⟨⟨true,true,567⟩,⟨false,true,537⟩,658⟩),true,[-1],[]⟩,
⟨⟨21,48,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,49,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,50,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,51,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,52,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,268⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,53,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,746⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,54,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,731⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,55,[-1],771⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨false,false,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,122⟩),(.pair ⟨⟨true,true,568⟩,⟨false,true,537⟩,665⟩),true,[-1],[]⟩,
⟨⟨21,56,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,57,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,58,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,59,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨false,true,567⟩,⟨true,true,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,60,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,153⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,61,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨false,true,642⟩,⟨false,true,606⟩],(.bound ⟨false,false,207⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,62,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨false,false,669⟩],(.bound ⟨false,false,475⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨21,63,[-1],685⟩,[⟨true,true,629⟩,⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩),(.pair ⟨⟨true,true,109⟩,⟨false,true,537⟩,30⟩),true,[-1],[]⟩,
⟨⟨22,0,[-1],10⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,523⟩),(.pair ⟨⟨true,false,346⟩,⟨false,false,215⟩,295⟩),true,[-1],[]⟩,
⟨⟨22,1,[5],49⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,false,147⟩,⟨false,false,215⟩,96⟩),true,[5],[]⟩,
⟨⟨22,1,[1],125⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,215⟩,40⟩),true,[1],[]⟩,
⟨⟨22,1,[0],182⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,215⟩,774⟩),true,[0],[]⟩,
⟨⟨22,1,[4],472⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,false,417⟩,⟨false,false,215⟩,387⟩),true,[4],[]⟩,
⟨⟨22,1,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨22,1,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨22,1,[3,7],931⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,215⟩,461⟩),true,[3,7],[]⟩,
⟨⟨22,1,[2,6],1200⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,139⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,215⟩,1002⟩),true,[2,6],[]⟩,
⟨⟨22,2,[-1],632⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,217⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,215⟩,200⟩),true,[-1],[]⟩,
⟨⟨22,3,[-1],689⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨true,false,465⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,498⟩),(.pair ⟨⟨true,true,327⟩,⟨false,false,215⟩,287⟩),true,[-1],[]⟩,
⟨⟨22,4,[-1],11⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,403⟩),(.pair ⟨⟨true,false,346⟩,⟨false,true,465⟩,296⟩),true,[-1],[]⟩,
⟨⟨22,5,[5],85⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,465⟩,121⟩),true,[5],[]⟩,
⟨⟨22,5,[1],144⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,465⟩,54⟩),true,[1],[]⟩,
⟨⟨22,5,[0],219⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,465⟩,800⟩),true,[0],[]⟩,
⟨⟨22,5,[4],489⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,465⟩,400⟩),true,[4],[]⟩,
⟨⟨22,5,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨22,5,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨22,5,[3,7],949⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,465⟩,474⟩),true,[3,7],[]⟩
]

private theorem good_5 : ∀ r ∈ chunk_5, rowGood r := by
  decide +kernel

private def chunk_6 : List Row := [
⟨⟨22,5,[2,6],1239⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,185⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,465⟩,1027⟩),true,[2,6],[]⟩,
⟨⟨22,6,[-1],641⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,289⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,465⟩,204⟩),true,[-1],[]⟩,
⟨⟨22,7,[-1],692⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,215⟩,⟨false,true,465⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,424⟩),(.pair ⟨⟨true,true,327⟩,⟨false,true,465⟩,289⟩),true,[-1],[]⟩,
⟨⟨22,8,[5],78⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,517⟩,129⟩),true,[5],[]⟩,
⟨⟨22,8,[1],132⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,false,116⟩,⟨false,false,496⟩,56⟩),true,[1],[]⟩,
⟨⟨22,8,[0],191⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,false,583⟩,⟨false,false,496⟩,803⟩),true,[0],[]⟩,
⟨⟨22,8,[4],487⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,517⟩,403⟩),true,[4],[]⟩,
⟨⟨22,8,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨22,8,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨22,8,[3],938⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,496⟩,476⟩),true,[3],[]⟩,
⟨⟨22,8,[7],947⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,517⟩,478⟩),true,[7],[]⟩,
⟨⟨22,8,[2],1209⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,496⟩,1029⟩),true,[2],[]⟩,
⟨⟨22,8,[6],1232⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,394⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,517⟩,1033⟩),true,[6],[]⟩,
⟨⟨22,9,[5],63⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,346⟩,106⟩),true,[5],[]⟩,
⟨⟨22,9,[1],136⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,346⟩,48⟩),true,[1],[]⟩,
⟨⟨22,9,[0],199⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,346⟩,785⟩),true,[0],[]⟩,
⟨⟨22,9,[4],481⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,346⟩,394⟩),true,[4],[]⟩,
⟨⟨22,9,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨22,9,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨22,9,[3,7],942⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,346⟩,468⟩),true,[3,7],[]⟩,
⟨⟨22,9,[2,6],1219⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,204⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,346⟩,1013⟩),true,[2,6],[]⟩,
⟨⟨22,10,[-1],635⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,334⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,496⟩,205⟩),true,[-1],[]⟩,
⟨⟨22,11,[-1],690⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨false,false,496⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,411⟩),(.pair ⟨⟨true,true,327⟩,⟨false,true,411⟩,288⟩),true,[-1],[]⟩,
⟨⟨22,12,[5],78⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,517⟩,129⟩),true,[5],[]⟩,
⟨⟨22,12,[1],145⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,511⟩,58⟩),true,[1],[]⟩,
⟨⟨22,12,[0],221⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,false,583⟩,⟨false,true,511⟩,807⟩),true,[0],[]⟩,
⟨⟨22,12,[4],487⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,false,417⟩,⟨false,true,517⟩,403⟩),true,[4],[]⟩,
⟨⟨22,12,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨22,12,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨22,12,[7],947⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,517⟩,478⟩),true,[7],[]⟩,
⟨⟨22,12,[3],950⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,511⟩,477⟩),true,[3],[]⟩,
⟨⟨22,12,[6],1232⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,517⟩,1033⟩),true,[6],[]⟩,
⟨⟨22,12,[2],1240⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,511⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,511⟩,1031⟩),true,[2],[]⟩,
⟨⟨22,13,[-1],795⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,94⟩),(.pair ⟨⟨true,true,496⟩,⟨false,true,94⟩,519⟩),true,[-1],[]⟩,
⟨⟨22,14,[-1],637⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,105⟩),(.pair ⟨⟨true,true,222⟩,⟨false,true,105⟩,198⟩),true,[-1],[]⟩,
⟨⟨22,15,[-1],691⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,215⟩,⟨true,true,496⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,483⟩),(.pair ⟨⟨true,true,327⟩,⟨false,true,483⟩,290⟩),true,[-1],[]⟩,
⟨⟨24,0,[-1],497⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,583⟩),(.pair ⟨⟨true,false,432⟩,⟨false,false,222⟩,416⟩),true,[-1],[]⟩,
⟨⟨24,1,[1],139⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩),(.pair ⟨⟨true,false,116⟩,⟨false,true,116⟩,38⟩),false,[1],[]⟩,
⟨⟨24,1,[4,5,7],284⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩),(.pair ⟨⟨true,false,517⟩,⟨false,true,517⟩,523⟩),false,[4,5,7],[]⟩,
⟨⟨24,1,[0],499⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,432⟩,417⟩),false,[0],[]⟩,
⟨⟨24,1,[8,9,10,11,12,13,14,15],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,10,11,12,13,14,15],[]⟩,
⟨⟨24,1,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨24,1,[2,3,6],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,116⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6],[]⟩,
⟨⟨24,2,[-1],1202⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,160⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,222⟩,1004⟩),true,[-1],[]⟩,
⟨⟨24,3,[-1],932⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,546⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,222⟩,462⟩),true,[-1],[]⟩,
⟨⟨24,4,[-1],498⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,417⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,517⟩,418⟩),true,[-1],[]⟩,
⟨⟨24,5,[5],66⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,false,147⟩,⟨false,true,147⟩,94⟩),false,[5],[]⟩,
⟨⟨24,5,[0,1],284⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,false,517⟩,⟨false,true,517⟩,523⟩),false,[0,1],[]⟩,
⟨⟨24,5,[4],499⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,432⟩,417⟩),false,[4],[]⟩,
⟨⟨24,5,[8,9,12,13],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[8,9,12,13],[]⟩,
⟨⟨24,5,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨24,5,[2,3,6,7,10,11,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,147⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[2,3,6,7,10,11,14,15],[]⟩,
⟨⟨24,6,[-1],1232⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,203⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,517⟩,1033⟩),true,[-1],[]⟩,
⟨⟨24,7,[-1],947⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,464⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,517⟩,478⟩),true,[-1],[]⟩,
⟨⟨24,8,[8],101⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩),(.pair ⟨⟨true,false,377⟩,⟨false,true,377⟩,347⟩),false,[8],[]⟩,
⟨⟨24,8,[9],499⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,432⟩,417⟩),false,[9],[]⟩,
⟨⟨24,8,[0,1,2,3,4,5,7],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[0,1,2,3,4,5,7],[]⟩,
⟨⟨24,8,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨24,8,[12,13,14,15],884⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,570⟩,703⟩),false,[12,13,14,15],[]⟩,
⟨⟨24,8,[6,10,11],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,377⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[6,10,11],[]⟩,
⟨⟨24,9,[9],22⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,false,202⟩,⟨false,true,202⟩,149⟩),false,[9],[]⟩,
⟨⟨24,9,[8],499⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,432⟩,417⟩),false,[8],[]⟩,
⟨⟨24,9,[0,1,2,3,4,5,7],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[0,1,2,3,4,5,7],[]⟩,
⟨⟨24,9,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨24,9,[12,13,14,15],884⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,570⟩,703⟩),false,[12,13,14,15],[]⟩,
⟨⟨24,9,[6,10,11],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,202⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[6,10,11],[]⟩,
⟨⟨24,10,[-1],1212⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,304⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,570⟩,1037⟩),true,[-1],[]⟩,
⟨⟨24,11,[-1],940⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,430⟩),(.pair ⟨⟨true,true,452⟩,⟨false,false,570⟩,480⟩),true,[-1],[]⟩,
⟨⟨24,12,[12],492⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,false,561⟩,⟨false,true,561⟩,656⟩),false,[12],[]⟩,
⟨⟨24,12,[13],499⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,432⟩,417⟩),false,[13],[]⟩,
⟨⟨24,12,[0,1,2,3,4,5,7],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[0,1,2,3,4,5,7],[]⟩,
⟨⟨24,12,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨24,12,[8,9,10,11],884⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,570⟩,703⟩),false,[8,9,10,11],[]⟩,
⟨⟨24,12,[6,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨true,false,432⟩],(.bound ⟨true,false,561⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[6,14,15],[]⟩,
⟨⟨24,13,[13],90⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩),(.pair ⟨⟨true,false,69⟩,⟨false,true,69⟩,22⟩),false,[13],[]⟩,
⟨⟨24,13,[12],499⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩),(.pair ⟨⟨true,false,432⟩,⟨false,true,432⟩,417⟩),false,[12],[]⟩,
⟨⟨24,13,[0,1,2,3,4,5,7],633⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩),(.pair ⟨⟨true,true,222⟩,⟨false,false,222⟩,201⟩),false,[0,1,2,3,4,5,7],[]⟩,
⟨⟨24,13,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],739⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩),(.pair ⟨⟨true,true,633⟩,⟨false,false,633⟩,1040⟩),false,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[]⟩,
⟨⟨24,13,[8,9,10,11],884⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩),(.pair ⟨⟨true,true,570⟩,⟨false,false,570⟩,703⟩),false,[8,9,10,11],[]⟩,
⟨⟨24,13,[6,14,15],1218⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,629⟩,⟨false,true,432⟩],(.bound ⟨true,false,69⟩),(.pair ⟨⟨true,true,629⟩,⟨false,false,629⟩,1039⟩),false,[6,14,15],[]⟩,
⟨⟨24,14,[-1],1226⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,629⟩,⟨false,false,452⟩],(.bound ⟨true,false,73⟩),(.pair ⟨⟨true,true,629⟩,⟨false,true,73⟩,999⟩),true,[-1],[]⟩,
⟨⟨24,15,[-1],946⟩,[⟨false,false,577⟩,⟨false,false,633⟩,⟨false,true,537⟩],[⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,629⟩,⟨true,true,452⟩],(.bound ⟨true,false,530⟩),(.pair ⟨⟨true,true,452⟩,⟨false,true,530⟩,479⟩),true,[-1],[]⟩
]

private theorem good_6 : ∀ r ∈ chunk_6, rowGood r := by
  decide +kernel

private def allRows : List Row := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6].flatten

private theorem rows_good : ∀ r ∈ allRows, rowGood r := by
  intro r hr
  simp only [allRows] at hr
  obtain ⟨c, hc, hr⟩ := List.mem_flatten.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_0 r hr
  · exact good_1 r hr
  · exact good_2 r hr
  · exact good_3 r hr
  · exact good_4 r hr
  · exact good_5 r hr
  · exact good_6 r hr

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([1] : List ℕ)))
      = allRows.map Row.record := by
  decide +kernel

end Row1

open Row1

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([1] : List ℕ) →
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
