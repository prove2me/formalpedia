-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_mixed_C_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T17:06:08.699979+00:00
-- url     : https://prove2.me/submissions/4cc99beb-e438-4bee-9991-ae0f2fe9982a

import Definitions.Def_Freiman_middleRepairLedger
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

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

namespace RetRow2

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
private def decodeComparison : RefComparison → LowerHistoryComparison
  | .automatic => .automatic
  | .impossible => .impossible
  | .bound b => .bound (middleCertBound middleCertData b)
private def decodeBranch (p : List MiddleCertBoundRef × RefComparison) : List CertBound × LowerHistoryComparison :=
  (middleCertBounds middleCertData p.1,decodeComparison p.2)

private def branches_26 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩)),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩)),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],(.bound ⟨true,false,277⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,599⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],(.bound ⟨false,false,779⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],(.bound ⟨false,false,679⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],(.bound ⟨false,false,658⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic)
]

private theorem branches_26_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 26)
      = (branches_26).map decodeBranch := by
  decide +kernel

private def branches_27 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_27_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 27)
      = (branches_27).map decodeBranch := by
  decide +kernel

private def branches_28 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic)
]

private theorem branches_28_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 28)
      = (branches_28).map decodeBranch := by
  decide +kernel

private def branches_29 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,253⟩,⟨true,false,450⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,473⟩)),
([⟨false,false,253⟩,⟨true,false,450⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,443⟩)),
([⟨false,false,253⟩,⟨true,false,450⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,341⟩)),
([⟨false,false,253⟩,⟨true,false,450⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,457⟩)),
([⟨false,false,253⟩,⟨false,true,450⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,293⟩)),
([⟨false,false,253⟩,⟨false,true,450⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,305⟩)),
([⟨false,false,253⟩,⟨false,true,450⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,320⟩)),
([⟨false,false,253⟩,⟨false,true,450⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,245⟩)),
([⟨true,true,253⟩,⟨false,false,481⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,310⟩)),
([⟨true,true,253⟩,⟨false,false,481⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,337⟩)),
([⟨true,true,253⟩,⟨false,false,481⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,360⟩)),
([⟨true,true,253⟩,⟨false,false,481⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,240⟩)),
([⟨true,true,253⟩,⟨true,true,481⟩,⟨false,false,364⟩,⟨true,false,391⟩],(.bound ⟨true,false,469⟩)),
([⟨true,true,253⟩,⟨true,true,481⟩,⟨false,false,364⟩,⟨false,true,391⟩],(.bound ⟨true,false,342⟩)),
([⟨true,true,253⟩,⟨true,true,481⟩,⟨true,true,364⟩,⟨false,false,400⟩],(.bound ⟨true,false,367⟩)),
([⟨true,true,253⟩,⟨true,true,481⟩,⟨true,true,364⟩,⟨true,true,400⟩],(.bound ⟨true,false,449⟩))
]

private theorem branches_29_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 29)
      = (branches_29).map decodeBranch := by
  decide +kernel

private def branches_30 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,638⟩,⟨true,false,609⟩,⟨false,true,614⟩,⟨true,false,622⟩],(.bound ⟨false,false,234⟩)),
([⟨false,true,638⟩,⟨true,false,609⟩,⟨false,true,614⟩,⟨false,true,622⟩],(.bound ⟨false,false,582⟩)),
([⟨false,true,638⟩,⟨true,false,609⟩,⟨true,false,614⟩,⟨false,false,683⟩],(.bound ⟨false,false,126⟩)),
([⟨false,true,638⟩,⟨true,false,609⟩,⟨true,false,614⟩,⟨true,true,683⟩],(.bound ⟨false,false,183⟩)),
([⟨false,true,638⟩,⟨false,true,609⟩,⟨false,true,614⟩,⟨true,false,622⟩],(.bound ⟨false,false,274⟩)),
([⟨false,true,638⟩,⟨false,true,609⟩,⟨false,true,614⟩,⟨false,true,622⟩],(.bound ⟨false,false,768⟩)),
([⟨false,true,638⟩,⟨false,true,609⟩,⟨true,false,614⟩,⟨false,false,683⟩],(.bound ⟨false,false,694⟩)),
([⟨false,true,638⟩,⟨false,true,609⟩,⟨true,false,614⟩,⟨true,true,683⟩],(.bound ⟨false,false,409⟩)),
([⟨true,false,638⟩,⟨false,false,672⟩,⟨false,true,614⟩,⟨true,false,622⟩],(.bound ⟨false,false,300⟩)),
([⟨true,false,638⟩,⟨false,false,672⟩,⟨false,true,614⟩,⟨false,true,622⟩],(.bound ⟨false,false,760⟩)),
([⟨true,false,638⟩,⟨false,false,672⟩,⟨true,false,614⟩,⟨false,false,683⟩],(.bound ⟨false,false,663⟩)),
([⟨true,false,638⟩,⟨false,false,672⟩,⟨true,false,614⟩,⟨true,true,683⟩],(.bound ⟨false,false,456⟩)),
([⟨true,false,638⟩,⟨true,true,672⟩,⟨false,true,614⟩,⟨true,false,622⟩],(.bound ⟨false,false,194⟩)),
([⟨true,false,638⟩,⟨true,true,672⟩,⟨false,true,614⟩,⟨false,true,622⟩],(.bound ⟨false,false,39⟩)),
([⟨true,false,638⟩,⟨true,true,672⟩,⟨true,false,614⟩,⟨false,false,683⟩],(.bound ⟨false,false,318⟩)),
([⟨true,false,638⟩,⟨true,true,672⟩,⟨true,false,614⟩,⟨true,true,683⟩],(.bound ⟨false,false,169⟩))
]

private theorem branches_30_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 30)
      = (branches_30).map decodeBranch := by
  decide +kernel

private def branches_31 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_31_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 31)
      = (branches_31).map decodeBranch := by
  decide +kernel

private def branches_32 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_32_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 32)
      = (branches_32).map decodeBranch := by
  decide +kernel

private def branches_33 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_33_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 33)
      = (branches_33).map decodeBranch := by
  decide +kernel

private def branches_34 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_34_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 34)
      = (branches_34).map decodeBranch := by
  decide +kernel

private def branches_35 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_35_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 35)
      = (branches_35).map decodeBranch := by
  decide +kernel

private def branches_36 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_36_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 36)
      = (branches_36).map decodeBranch := by
  decide +kernel

private def branches_37 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,590⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,660⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,211⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨true,false,527⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,550⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,199⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,136⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,260⟩)),
([⟨false,false,264⟩,⟨false,false,614⟩,⟨false,true,527⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,108⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,210⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,155⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,316⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨false,false,578⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,104⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,574⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,159⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,319⟩)),
([⟨false,false,264⟩,⟨true,true,614⟩,⟨true,true,578⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,541⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,590⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,660⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,211⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨true,false,527⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,550⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,199⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,136⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,260⟩)),
([⟨true,true,264⟩,⟨false,true,614⟩,⟨false,true,527⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,108⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,210⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,155⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,316⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨false,false,578⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,104⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,false,222⟩,⟨true,false,346⟩],(.bound ⟨true,false,574⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨false,false,222⟩,⟨false,true,346⟩],(.bound ⟨true,false,159⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,true,222⟩,⟨false,false,327⟩],(.bound ⟨true,false,319⟩)),
([⟨true,true,264⟩,⟨true,false,614⟩,⟨true,true,578⟩,⟨true,true,222⟩,⟨true,true,327⟩],(.bound ⟨true,false,541⟩))
]

private theorem branches_37_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 37)
      = (branches_37).map decodeBranch := by
  decide +kernel

private def branches_38 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,222⟩,⟨true,false,517⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨false,false,222⟩,⟨false,true,517⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,570⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,264⟩,⟨false,false,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨false,false,264⟩,⟨true,true,253⟩,⟨true,true,259⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨true,false,298⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,264⟩,⟨false,true,253⟩,⟨false,true,298⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨false,false,259⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,570⟩,⟨true,true,264⟩,⟨true,false,253⟩,⟨true,true,259⟩],.automatic)
]

private theorem branches_38_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 38)
      = (branches_38).map decodeBranch := by
  decide +kernel

private def branches_39 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_39_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 39)
      = (branches_39).map decodeBranch := by
  decide +kernel

private def branches_40 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_40_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 40)
      = (branches_40).map decodeBranch := by
  decide +kernel

private def parents_false : List (List MiddleCertBoundRef) := [
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

private theorem parents_false_eq :
    middleRepairCertParents false = (parents_false).map (middleCertBounds middleCertData) := by
  decide +kernel

private def parents_true : List (List MiddleCertBoundRef) := [
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

private theorem parents_true_eq :
    middleRepairCertParents true = (parents_true).map (middleCertBounds middleCertData) := by
  decide +kernel

private def cachedBranches (g : ℕ) : List (List MiddleCertBoundRef × RefComparison) :=
  if g = 26 then branches_26 else
  if g = 27 then branches_27 else
  if g = 28 then branches_28 else
  if g = 29 then branches_29 else
  if g = 30 then branches_30 else
  if g = 31 then branches_31 else
  if g = 32 then branches_32 else
  if g = 33 then branches_33 else
  if g = 34 then branches_34 else
  if g = 35 then branches_35 else
  if g = 36 then branches_36 else
  if g = 37 then branches_37 else
  if g = 38 then branches_38 else
  if g = 39 then branches_39 else
  if g = 40 then branches_40 else
  []

private theorem cb_26 : cachedBranches 26 = branches_26 := by
  norm_num [cachedBranches]

private theorem cb_27 : cachedBranches 27 = branches_27 := by
  norm_num [cachedBranches]

private theorem cb_28 : cachedBranches 28 = branches_28 := by
  norm_num [cachedBranches]

private theorem cb_29 : cachedBranches 29 = branches_29 := by
  norm_num [cachedBranches]

private theorem cb_30 : cachedBranches 30 = branches_30 := by
  norm_num [cachedBranches]

private theorem cb_31 : cachedBranches 31 = branches_31 := by
  norm_num [cachedBranches]

private theorem cb_32 : cachedBranches 32 = branches_32 := by
  norm_num [cachedBranches]

private theorem cb_33 : cachedBranches 33 = branches_33 := by
  norm_num [cachedBranches]

private theorem cb_34 : cachedBranches 34 = branches_34 := by
  norm_num [cachedBranches]

private theorem cb_35 : cachedBranches 35 = branches_35 := by
  norm_num [cachedBranches]

private theorem cb_36 : cachedBranches 36 = branches_36 := by
  norm_num [cachedBranches]

private theorem cb_37 : cachedBranches 37 = branches_37 := by
  norm_num [cachedBranches]

private theorem cb_38 : cachedBranches 38 = branches_38 := by
  norm_num [cachedBranches]

private theorem cb_39 : cachedBranches 39 = branches_39 := by
  norm_num [cachedBranches]

private theorem cb_40 : cachedBranches 40 = branches_40 := by
  norm_num [cachedBranches]

private def cachedParents (p : Bool) : List (List MiddleCertBoundRef) :=
  if p then parents_true else parents_false

private def refComplement (b : MiddleCertBoundRef) : MiddleCertBoundRef :=
  ⟨!b.lower, !b.strict, b.threshold⟩

private def refConditions (rec : MiddleCertRecord) (parent : ℤ) : List MiddleCertBoundRef :=
  (middleCertGoal middleCertData rec.goal).hypotheses ++
    ((cachedBranches rec.goal)[rec.branch]?.getD ([], RefComparison.impossible)).1 ++
    (if parent < 0 then [] else
      (cachedParents (middleCertParity (middleCertGoal middleCertData rec.goal).family))[parent.toNat]?.getD []) ++
    (match ((cachedBranches rec.goal)[rec.branch]?.getD ([], RefComparison.impossible)).2 with
      | .bound t => [refComplement t] | _ => [])

private def selectedGoals : List ℕ := [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]

private theorem conditions_eq (rec : MiddleCertRecord) (parent : ℤ)
    (hg : rec.goal ∈ selectedGoals) :
    middleRepairCertConditions middleCertData rec parent
      = middleCertBounds middleCertData (refConditions rec parent) := by
  have hp (p : Bool) :
      middleRepairCertParents p = (cachedParents p).map (middleCertBounds middleCertData) := by
    cases p
    · exact parents_false_eq
    · exact parents_true_eq
  have hb : middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData rec.goal)
      = (cachedBranches rec.goal).map decodeBranch := by
    simp only [selectedGoals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
    · simpa only [hg, cb_26] using branches_26_eq
    · simpa only [hg, cb_27] using branches_27_eq
    · simpa only [hg, cb_28] using branches_28_eq
    · simpa only [hg, cb_29] using branches_29_eq
    · simpa only [hg, cb_30] using branches_30_eq
    · simpa only [hg, cb_31] using branches_31_eq
    · simpa only [hg, cb_32] using branches_32_eq
    · simpa only [hg, cb_33] using branches_33_eq
    · simpa only [hg, cb_34] using branches_34_eq
    · simpa only [hg, cb_35] using branches_35_eq
    · simpa only [hg, cb_36] using branches_36_eq
    · simpa only [hg, cb_37] using branches_37_eq
    · simpa only [hg, cb_38] using branches_38_eq
    · simpa only [hg, cb_39] using branches_39_eq
    · simpa only [hg, cb_40] using branches_40_eq
  have hget : ((cachedBranches rec.goal).map decodeBranch)[rec.branch]?.getD ([], .impossible)
      = decodeBranch ((cachedBranches rec.goal)[rec.branch]?.getD ([], RefComparison.impossible)) := by
    simp only [List.getElem?_map]
    exact Option.getD_map decodeBranch ([], RefComparison.impossible)
      ((cachedBranches rec.goal)[rec.branch]?)
  have hpget (p : Bool) :
      ((cachedParents p).map (middleCertBounds middleCertData))[parent.toNat]?.getD []
        = middleCertBounds middleCertData ((cachedParents p)[parent.toNat]?.getD []) := by
    simp only [List.getElem?_map]
    exact Option.getD_map (middleCertBounds middleCertData) [] ((cachedParents p)[parent.toNat]?)
  simp only [middleRepairCertConditions, middleRepairCertBranch, hb, hget, decodeBranch,
    hp, hpget, refConditions, middleCertBounds, List.map_append]
  split_ifs <;>
    cases hc : ((cachedBranches rec.goal)[rec.branch]?.getD ([], RefComparison.impossible)).2 <;>
    simp [decodeComparison, middleCertBounds, refComplement, middleCertBound, lowerHistoryComplement]

local instance (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) (p : MiddleCertProof) :
    Decidable (proofReady C bs p) := by
  cases p <;> unfold proofReady pairReady refMatches refStrict <;> infer_instance

private theorem from_refs (rec : MiddleCertRecord) (parent : ℤ)
    (hg : rec.goal ∈ selectedGoals)
    (hn : middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none)
    (hf : proofReady middleCertData (refConditions rec parent)
      (middleCertProof middleCertData rec.proof)) :
    middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  have he : middleRepairEffectiveProof middleCertData middleRepairRedirects rec parent
      = adaptProof middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
    simp only [middleRepairEffectiveProof, hn, conditions_eq rec parent hg]
    cases middleCertProof middleCertData rec.proof <;> rfl
  simpa only [middleRepairRecordValid, he, conditions_eq rec parent hg] using proof_ready _ _ _ hf

private def chunk_0 : List MiddleCertRecord := [
  ⟨26,8,[-1],288⟩,
  ⟨26,10,[-1],294⟩,
  ⟨26,11,[-1],300⟩,
  ⟨26,12,[-1],288⟩,
  ⟨26,14,[-1],294⟩,
  ⟨26,15,[-1],300⟩,
  ⟨26,16,[-1],1031⟩,
  ⟨26,20,[-1],1031⟩,
  ⟨26,24,[-1],812⟩,
  ⟨26,25,[-1],815⟩,
  ⟨26,26,[-1],813⟩,
  ⟨26,28,[-1],812⟩,
  ⟨26,29,[-1],815⟩,
  ⟨26,30,[-1],813⟩,
  ⟨26,40,[-1],739⟩,
  ⟨26,42,[-1],739⟩
]

private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨26,43,[-1],739⟩,
  ⟨26,44,[-1],739⟩,
  ⟨26,46,[-1],739⟩,
  ⟨26,47,[-1],739⟩,
  ⟨26,48,[-1],739⟩,
  ⟨26,52,[-1],739⟩,
  ⟨26,56,[-1],739⟩,
  ⟨26,57,[-1],739⟩,
  ⟨26,58,[-1],739⟩,
  ⟨26,60,[-1],739⟩,
  ⟨26,61,[-1],739⟩,
  ⟨26,62,[-1],739⟩,
  ⟨27,1,[-1],172⟩,
  ⟨27,2,[-1],1218⟩,
  ⟨27,3,[-1],1218⟩,
  ⟨27,5,[-1],739⟩
]

private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨27,6,[-1],739⟩,
  ⟨27,7,[-1],739⟩,
  ⟨27,11,[-1],1218⟩,
  ⟨27,15,[-1],739⟩,
  ⟨27,16,[-1],1218⟩,
  ⟨27,17,[-1],1218⟩,
  ⟨27,19,[-1],699⟩,
  ⟨27,20,[-1],739⟩,
  ⟨27,21,[-1],739⟩,
  ⟨27,23,[-1],739⟩,
  ⟨27,25,[-1],1218⟩,
  ⟨27,29,[-1],739⟩,
  ⟨29,0,[-1],286⟩,
  ⟨29,1,[-1],310⟩,
  ⟨29,2,[-1],296⟩,
  ⟨29,3,[-1],317⟩
]

private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨29,4,[-1],286⟩,
  ⟨29,5,[-1],310⟩,
  ⟨29,6,[-1],296⟩,
  ⟨29,7,[-1],302⟩,
  ⟨29,8,[-1],286⟩,
  ⟨29,9,[-1],310⟩,
  ⟨29,10,[-1],296⟩,
  ⟨29,11,[-1],304⟩,
  ⟨29,12,[-1],286⟩,
  ⟨29,13,[-1],310⟩,
  ⟨29,14,[-1],296⟩,
  ⟨29,15,[-1],312⟩,
  ⟨30,0,[-1],412⟩,
  ⟨30,1,[-1],413⟩,
  ⟨30,2,[-1],412⟩,
  ⟨30,3,[-1],810⟩
]

private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨30,4,[-1],606⟩,
  ⟨30,5,[-1],826⟩,
  ⟨30,6,[-1],923⟩,
  ⟨30,7,[-1],927⟩,
  ⟨30,8,[-1],737⟩,
  ⟨30,9,[-1],738⟩,
  ⟨30,10,[-1],737⟩,
  ⟨30,11,[-1],737⟩,
  ⟨30,12,[-1],1149⟩,
  ⟨30,13,[-1],1150⟩,
  ⟨30,14,[-1],1149⟩,
  ⟨30,15,[-1],1149⟩,
  ⟨32,0,[-1],293⟩,
  ⟨32,1,[-1],293⟩,
  ⟨32,2,[-1],293⟩,
  ⟨32,3,[-1],293⟩
]

private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨32,4,[-1],293⟩,
  ⟨32,5,[-1],293⟩,
  ⟨32,6,[-1],293⟩,
  ⟨32,7,[-1],293⟩,
  ⟨32,8,[-1],316⟩,
  ⟨32,9,[-1],316⟩,
  ⟨32,10,[-1],316⟩,
  ⟨32,11,[-1],316⟩,
  ⟨32,12,[-1],316⟩,
  ⟨32,13,[-1],316⟩,
  ⟨32,14,[-1],316⟩,
  ⟨32,15,[-1],316⟩,
  ⟨32,16,[-1],291⟩,
  ⟨32,17,[-1],291⟩,
  ⟨32,18,[-1],291⟩,
  ⟨32,19,[-1],291⟩
]

private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨32,20,[-1],298⟩,
  ⟨32,21,[-1],298⟩,
  ⟨32,22,[-1],298⟩,
  ⟨32,23,[-1],298⟩,
  ⟨32,24,[-1],291⟩,
  ⟨32,25,[-1],291⟩,
  ⟨32,26,[-1],291⟩,
  ⟨32,27,[-1],291⟩,
  ⟨32,28,[-1],319⟩,
  ⟨32,29,[-1],306⟩,
  ⟨32,30,[-1],303⟩,
  ⟨32,31,[-1],314⟩,
  ⟨32,32,[-1],293⟩,
  ⟨32,33,[-1],293⟩,
  ⟨32,34,[-1],293⟩,
  ⟨32,35,[-1],293⟩
]

private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨32,36,[-1],293⟩,
  ⟨32,37,[-1],293⟩,
  ⟨32,38,[-1],293⟩,
  ⟨32,39,[-1],293⟩,
  ⟨32,40,[-1],316⟩,
  ⟨32,41,[-1],316⟩,
  ⟨32,42,[-1],316⟩,
  ⟨32,43,[-1],316⟩,
  ⟨32,44,[-1],316⟩,
  ⟨32,45,[-1],316⟩,
  ⟨32,46,[-1],316⟩,
  ⟨32,47,[-1],316⟩,
  ⟨32,48,[-1],291⟩,
  ⟨32,49,[-1],291⟩,
  ⟨32,50,[-1],291⟩,
  ⟨32,51,[-1],291⟩
]

private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨32,52,[-1],298⟩,
  ⟨32,53,[-1],298⟩,
  ⟨32,54,[-1],298⟩,
  ⟨32,55,[-1],298⟩,
  ⟨32,56,[-1],291⟩,
  ⟨32,57,[-1],291⟩,
  ⟨32,58,[-1],291⟩,
  ⟨32,59,[-1],291⟩,
  ⟨32,60,[-1],319⟩,
  ⟨32,61,[-1],306⟩,
  ⟨32,62,[-1],303⟩,
  ⟨32,63,[-1],314⟩,
  ⟨33,0,[-1],460⟩,
  ⟨33,1,[-1],464⟩,
  ⟨33,2,[-1],458⟩,
  ⟨33,3,[-1],458⟩
]

private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨33,4,[-1],717⟩,
  ⟨33,5,[-1],721⟩,
  ⟨33,6,[-1],716⟩,
  ⟨33,7,[-1],716⟩,
  ⟨33,8,[-1],1080⟩,
  ⟨33,9,[-1],1033⟩,
  ⟨33,10,[-1],904⟩,
  ⟨33,11,[-1],616⟩,
  ⟨33,12,[-1],717⟩,
  ⟨33,13,[-1],721⟩,
  ⟨33,14,[-1],716⟩,
  ⟨33,15,[-1],716⟩,
  ⟨33,16,[-1],726⟩,
  ⟨33,17,[-1],730⟩,
  ⟨33,18,[-1],724⟩,
  ⟨33,19,[-1],724⟩
]

private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨33,20,[-1],726⟩,
  ⟨33,21,[-1],730⟩,
  ⟨33,22,[-1],724⟩,
  ⟨33,23,[-1],724⟩,
  ⟨33,24,[-1],1156⟩,
  ⟨33,25,[-1],1160⟩,
  ⟨33,26,[-1],1154⟩,
  ⟨33,27,[-1],1154⟩,
  ⟨33,28,[-1],1156⟩,
  ⟨33,29,[-1],1160⟩,
  ⟨33,30,[-1],1154⟩,
  ⟨33,31,[-1],1154⟩,
  ⟨33,32,[-1],460⟩,
  ⟨33,33,[-1],464⟩,
  ⟨33,34,[-1],461⟩,
  ⟨33,35,[-1],461⟩
]

private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨33,36,[-1],717⟩,
  ⟨33,37,[-1],721⟩,
  ⟨33,38,[-1],718⟩,
  ⟨33,39,[-1],718⟩,
  ⟨33,40,[-1],1080⟩,
  ⟨33,41,[-1],1033⟩,
  ⟨33,42,[-1],906⟩,
  ⟨33,43,[-1],617⟩,
  ⟨33,44,[-1],717⟩,
  ⟨33,45,[-1],721⟩,
  ⟨33,46,[-1],718⟩,
  ⟨33,47,[-1],718⟩,
  ⟨33,48,[-1],726⟩,
  ⟨33,49,[-1],730⟩,
  ⟨33,50,[-1],727⟩,
  ⟨33,51,[-1],727⟩
]

private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨33,52,[-1],726⟩,
  ⟨33,53,[-1],730⟩,
  ⟨33,54,[-1],727⟩,
  ⟨33,55,[-1],727⟩,
  ⟨33,56,[-1],1156⟩,
  ⟨33,57,[-1],1160⟩,
  ⟨33,58,[-1],1157⟩,
  ⟨33,59,[-1],1157⟩,
  ⟨33,60,[-1],1156⟩,
  ⟨33,61,[-1],1160⟩,
  ⟨33,62,[-1],1157⟩,
  ⟨33,63,[-1],1157⟩,
  ⟨35,0,[-1],285⟩,
  ⟨35,1,[-1],285⟩,
  ⟨35,2,[-1],285⟩,
  ⟨35,3,[-1],285⟩
]

private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨35,4,[-1],285⟩,
  ⟨35,5,[-1],285⟩,
  ⟨35,6,[-1],285⟩,
  ⟨35,7,[-1],285⟩,
  ⟨35,8,[-1],311⟩,
  ⟨35,9,[-1],311⟩,
  ⟨35,10,[-1],311⟩,
  ⟨35,11,[-1],311⟩,
  ⟨35,12,[-1],311⟩,
  ⟨35,13,[-1],311⟩,
  ⟨35,14,[-1],311⟩,
  ⟨35,15,[-1],311⟩,
  ⟨35,16,[-1],287⟩,
  ⟨35,17,[-1],287⟩,
  ⟨35,18,[-1],287⟩,
  ⟨35,19,[-1],287⟩
]

private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨35,20,[-1],297⟩,
  ⟨35,21,[-1],297⟩,
  ⟨35,22,[-1],297⟩,
  ⟨35,23,[-1],297⟩,
  ⟨35,24,[-1],287⟩,
  ⟨35,25,[-1],287⟩,
  ⟨35,26,[-1],287⟩,
  ⟨35,27,[-1],287⟩,
  ⟨35,28,[-1],320⟩,
  ⟨35,29,[-1],309⟩,
  ⟨35,30,[-1],301⟩,
  ⟨35,31,[-1],315⟩,
  ⟨35,32,[-1],285⟩,
  ⟨35,33,[-1],285⟩,
  ⟨35,34,[-1],285⟩,
  ⟨35,35,[-1],285⟩
]

private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨35,36,[-1],285⟩,
  ⟨35,37,[-1],285⟩,
  ⟨35,38,[-1],285⟩,
  ⟨35,39,[-1],285⟩,
  ⟨35,40,[-1],311⟩,
  ⟨35,41,[-1],311⟩,
  ⟨35,42,[-1],311⟩,
  ⟨35,43,[-1],311⟩,
  ⟨35,44,[-1],311⟩,
  ⟨35,45,[-1],311⟩,
  ⟨35,46,[-1],311⟩,
  ⟨35,47,[-1],311⟩,
  ⟨35,48,[-1],287⟩,
  ⟨35,49,[-1],287⟩,
  ⟨35,50,[-1],287⟩,
  ⟨35,51,[-1],287⟩
]

private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨35,52,[-1],297⟩,
  ⟨35,53,[-1],297⟩,
  ⟨35,54,[-1],297⟩,
  ⟨35,55,[-1],297⟩,
  ⟨35,56,[-1],287⟩,
  ⟨35,57,[-1],287⟩,
  ⟨35,58,[-1],287⟩,
  ⟨35,59,[-1],287⟩,
  ⟨35,60,[-1],320⟩,
  ⟨35,61,[-1],309⟩,
  ⟨35,62,[-1],301⟩,
  ⟨35,63,[-1],315⟩,
  ⟨36,0,[-1],5⟩,
  ⟨36,1,[-1],5⟩,
  ⟨36,2,[-1],5⟩,
  ⟨36,3,[-1],5⟩
]

private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨36,4,[-1],762⟩,
  ⟨36,5,[-1],762⟩,
  ⟨36,6,[-1],762⟩,
  ⟨36,7,[-1],762⟩,
  ⟨36,8,[-1],590⟩,
  ⟨36,9,[-1],704⟩,
  ⟨36,10,[-1],598⟩,
  ⟨36,11,[-1],1006⟩,
  ⟨36,12,[-1],762⟩,
  ⟨36,13,[-1],762⟩,
  ⟨36,14,[-1],762⟩,
  ⟨36,15,[-1],762⟩,
  ⟨36,16,[-1],770⟩,
  ⟨36,17,[-1],770⟩,
  ⟨36,18,[-1],770⟩,
  ⟨36,19,[-1],770⟩
]

private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨36,20,[-1],770⟩,
  ⟨36,21,[-1],770⟩,
  ⟨36,22,[-1],770⟩,
  ⟨36,23,[-1],770⟩,
  ⟨36,24,[-1],684⟩,
  ⟨36,25,[-1],684⟩,
  ⟨36,26,[-1],684⟩,
  ⟨36,27,[-1],684⟩,
  ⟨36,28,[-1],684⟩,
  ⟨36,29,[-1],684⟩,
  ⟨36,30,[-1],684⟩,
  ⟨36,31,[-1],684⟩,
  ⟨36,32,[-1],5⟩,
  ⟨36,33,[-1],5⟩,
  ⟨36,34,[-1],5⟩,
  ⟨36,35,[-1],5⟩
]

private theorem refs_valid_18 : ∀ rec ∈ chunk_18, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨36,36,[-1],762⟩,
  ⟨36,37,[-1],762⟩,
  ⟨36,38,[-1],762⟩,
  ⟨36,39,[-1],762⟩,
  ⟨36,40,[-1],590⟩,
  ⟨36,41,[-1],704⟩,
  ⟨36,42,[-1],598⟩,
  ⟨36,43,[-1],1006⟩,
  ⟨36,44,[-1],762⟩,
  ⟨36,45,[-1],762⟩,
  ⟨36,46,[-1],762⟩,
  ⟨36,47,[-1],762⟩,
  ⟨36,48,[-1],770⟩,
  ⟨36,49,[-1],770⟩,
  ⟨36,50,[-1],770⟩,
  ⟨36,51,[-1],770⟩
]

private theorem refs_valid_19 : ∀ rec ∈ chunk_19, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨36,52,[-1],770⟩,
  ⟨36,53,[-1],770⟩,
  ⟨36,54,[-1],770⟩,
  ⟨36,55,[-1],770⟩,
  ⟨36,56,[-1],684⟩,
  ⟨36,57,[-1],684⟩,
  ⟨36,58,[-1],684⟩,
  ⟨36,59,[-1],684⟩,
  ⟨36,60,[-1],684⟩,
  ⟨36,61,[-1],684⟩,
  ⟨36,62,[-1],684⟩,
  ⟨36,63,[-1],684⟩,
  ⟨37,0,[-1],326⟩,
  ⟨37,1,[-1],331⟩,
  ⟨37,2,[-1],328⟩,
  ⟨37,3,[-1],327⟩
]

private theorem refs_valid_20 : ∀ rec ∈ chunk_20, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_21 : List MiddleCertRecord := [
  ⟨37,4,[-1],289⟩,
  ⟨37,5,[-1],299⟩,
  ⟨37,6,[-1],292⟩,
  ⟨37,7,[-1],290⟩,
  ⟨37,8,[-1],848⟩,
  ⟨37,9,[-1],853⟩,
  ⟨37,10,[-1],850⟩,
  ⟨37,11,[-1],849⟩,
  ⟨37,12,[-1],1097⟩,
  ⟨37,13,[-1],1102⟩,
  ⟨37,14,[-1],1099⟩,
  ⟨37,15,[-1],1098⟩,
  ⟨37,16,[-1],326⟩,
  ⟨37,17,[-1],331⟩,
  ⟨37,18,[-1],328⟩,
  ⟨37,19,[-1],333⟩
]

private theorem refs_valid_21 : ∀ rec ∈ chunk_21, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_22 : List MiddleCertRecord := [
  ⟨37,20,[-1],289⟩,
  ⟨37,21,[-1],299⟩,
  ⟨37,22,[-1],292⟩,
  ⟨37,23,[-1],307⟩,
  ⟨37,24,[-1],848⟩,
  ⟨37,25,[-1],853⟩,
  ⟨37,26,[-1],850⟩,
  ⟨37,27,[-1],854⟩,
  ⟨37,28,[-1],1097⟩,
  ⟨37,29,[-1],1102⟩,
  ⟨37,30,[-1],1099⟩,
  ⟨37,31,[-1],1103⟩,
  ⟨39,0,[-1],289⟩,
  ⟨39,1,[-1],289⟩,
  ⟨39,2,[-1],289⟩,
  ⟨39,3,[-1],932⟩
]

private theorem refs_valid_22 : ∀ rec ∈ chunk_22, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_23 : List MiddleCertRecord := [
  ⟨39,4,[-1],313⟩,
  ⟨39,5,[-1],313⟩,
  ⟨39,6,[-1],313⟩,
  ⟨39,7,[-1],947⟩,
  ⟨39,8,[-1],295⟩,
  ⟨39,9,[-1],295⟩,
  ⟨39,10,[-1],295⟩,
  ⟨39,11,[-1],940⟩,
  ⟨39,12,[-1],318⟩,
  ⟨39,13,[-1],305⟩,
  ⟨39,14,[-1],308⟩,
  ⟨39,15,[-1],946⟩
]

private theorem refs_valid_23 : ∀ rec ∈ chunk_23, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def selectedRecords : List MiddleCertRecord := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23].flatten

private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by
  decide +kernel

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([2] : List ℕ)))
      = selectedRecords := by
  decide +kernel

private theorem refs_valid : ∀ rec ∈ selectedRecords, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  intro rec hr
  simp only [selectedRecords] at hr
  obtain ⟨chunk, hc, hr⟩ := List.mem_flatten.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact refs_valid_0 rec hr
  · exact refs_valid_1 rec hr
  · exact refs_valid_2 rec hr
  · exact refs_valid_3 rec hr
  · exact refs_valid_4 rec hr
  · exact refs_valid_5 rec hr
  · exact refs_valid_6 rec hr
  · exact refs_valid_7 rec hr
  · exact refs_valid_8 rec hr
  · exact refs_valid_9 rec hr
  · exact refs_valid_10 rec hr
  · exact refs_valid_11 rec hr
  · exact refs_valid_12 rec hr
  · exact refs_valid_13 rec hr
  · exact refs_valid_14 rec hr
  · exact refs_valid_15 rec hr
  · exact refs_valid_16 rec hr
  · exact refs_valid_17 rec hr
  · exact refs_valid_18 rec hr
  · exact refs_valid_19 rec hr
  · exact refs_valid_20 rec hr
  · exact refs_valid_21 rec hr
  · exact refs_valid_22 rec hr
  · exact refs_valid_23 rec hr

end RetRow2

open RetRow2

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([2] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)

#print axioms solution
