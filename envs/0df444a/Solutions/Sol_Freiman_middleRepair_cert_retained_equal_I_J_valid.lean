-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_equal_I_J_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T17:06:12.178254+00:00
-- url     : https://prove2.me/submissions/da94d191-a3a0-4f21-9e8c-c869417457d7

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

namespace RetRow4

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

private def branches_61 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,637⟩,⟨true,false,602⟩],(.bound ⟨true,false,728⟩)),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,637⟩,⟨false,false,665⟩],(.bound ⟨true,false,799⟩)),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,637⟩,⟨true,true,665⟩],(.bound ⟨true,false,538⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,637⟩,⟨true,false,602⟩],(.bound ⟨false,false,801⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,637⟩,⟨false,true,602⟩],(.bound ⟨false,false,790⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,637⟩,⟨false,false,665⟩],(.bound ⟨false,false,787⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic)
]

private theorem branches_61_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 61)
      = (branches_61).map decodeBranch := by
  decide +kernel

private def branches_62 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],(.bound ⟨false,false,645⟩)),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],(.bound ⟨false,false,635⟩)),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],(.bound ⟨true,false,645⟩)),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],(.bound ⟨true,false,635⟩)),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],(.bound ⟨false,false,645⟩)),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],(.bound ⟨false,false,635⟩)),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],(.bound ⟨true,false,645⟩)),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨true,false,601⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],(.bound ⟨true,false,635⟩)),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.automatic)
]

private theorem branches_62_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 62)
      = (branches_62).map decodeBranch := by
  decide +kernel

private def branches_63 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic)
]

private theorem branches_63_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 63)
      = (branches_63).map decodeBranch := by
  decide +kernel

private def branches_64 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,533⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,229⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,246⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,515⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,533⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,229⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,246⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,515⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,488⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,226⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,252⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,326⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,488⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,226⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,252⟩)),
([⟨false,false,572⟩,⟨false,false,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,326⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,315⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,283⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,339⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,359⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,315⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,283⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,339⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,359⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,513⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,145⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,144⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,507⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,513⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,145⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,144⟩)),
([⟨false,false,572⟩,⟨true,true,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,507⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,533⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,229⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,246⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,515⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,533⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,229⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,246⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨true,false,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,515⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,488⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,226⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,252⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,326⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,488⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,226⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,252⟩)),
([⟨true,true,572⟩,⟨false,true,459⟩,⟨false,true,451⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,326⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,315⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,283⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,339⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,359⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,315⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,283⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,339⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨false,false,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,359⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,513⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨false,false,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,145⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,144⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨false,false,462⟩,⟨true,true,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,507⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨true,false,471⟩],(.bound ⟨true,false,513⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨false,true,503⟩,⟨false,true,471⟩],(.bound ⟨true,false,145⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨false,false,506⟩],(.bound ⟨true,false,144⟩)),
([⟨true,true,572⟩,⟨true,false,459⟩,⟨true,true,482⟩,⟨true,true,462⟩,⟨true,false,503⟩,⟨true,true,506⟩],(.bound ⟨true,false,507⟩))
]

private theorem branches_64_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 64)
      = (branches_64).map decodeBranch := by
  decide +kernel

private def branches_65 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,133⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,51⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,76⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,96⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,133⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,51⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,76⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,96⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,529⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,792⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,741⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,80⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,529⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,792⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,741⟩)),
([⟨false,true,677⟩,⟨false,false,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,80⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,287⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,791⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,715⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,188⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,287⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,791⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,715⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,188⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,89⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,40⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,388⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,77⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,89⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,40⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,388⟩)),
([⟨false,true,677⟩,⟨true,true,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,77⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,133⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,51⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,76⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,96⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,133⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,51⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,76⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨true,false,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,96⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,529⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,792⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,741⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,80⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,529⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,792⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,741⟩)),
([⟨true,false,677⟩,⟨false,true,721⟩,⟨false,true,684⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,80⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,287⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,791⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,715⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,188⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,287⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,791⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,715⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨false,false,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,188⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,89⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨false,false,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,40⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,388⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨false,true,713⟩,⟨true,true,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,77⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨true,false,726⟩],(.bound ⟨false,false,89⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨false,true,700⟩,⟨false,true,726⟩],(.bound ⟨false,false,40⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨false,false,761⟩],(.bound ⟨false,false,388⟩)),
([⟨true,false,677⟩,⟨true,false,721⟩,⟨true,true,707⟩,⟨true,false,713⟩,⟨true,false,700⟩,⟨true,true,761⟩],(.bound ⟨false,false,77⟩))
]

private theorem branches_65_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 65)
      = (branches_65).map decodeBranch := by
  decide +kernel

private def branches_66 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,680⟩,⟨true,false,689⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic)
]

private theorem branches_66_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 66)
      = (branches_66).map decodeBranch := by
  decide +kernel

private def branches_67 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,653⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,97⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,118⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,630⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,653⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,97⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,118⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,630⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,558⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,88⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,111⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,303⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,558⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,88⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,111⟩)),
([⟨false,false,600⟩,⟨false,false,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,303⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,251⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,175⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,269⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,351⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,251⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,175⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,269⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,351⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,628⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,53⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,52⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,616⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,628⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,53⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,52⟩)),
([⟨false,false,600⟩,⟨true,true,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,616⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,653⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,97⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,118⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,630⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,653⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,97⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,118⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨true,false,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,630⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,558⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,88⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,111⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,303⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,558⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,88⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,111⟩)),
([⟨true,true,600⟩,⟨false,true,514⟩,⟨false,true,547⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,303⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,251⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,175⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,269⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,351⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,251⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,175⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,269⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨false,false,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,351⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,628⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨false,false,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,53⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,52⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨false,false,526⟩,⟨true,true,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,616⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨true,false,532⟩],(.bound ⟨true,false,628⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨false,true,575⟩,⟨false,true,532⟩],(.bound ⟨true,false,53⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨false,false,584⟩],(.bound ⟨true,false,52⟩)),
([⟨true,true,600⟩,⟨true,false,514⟩,⟨true,true,619⟩,⟨true,true,526⟩,⟨true,false,575⟩,⟨true,true,584⟩],(.bound ⟨true,false,616⟩))
]

private theorem branches_67_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 67)
      = (branches_67).map decodeBranch := by
  decide +kernel

private def branches_68 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,63⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,25⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,30⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,43⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,63⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,25⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,30⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,43⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,685⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,798⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,794⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,9⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,685⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,798⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,794⟩)),
([⟨false,true,705⟩,⟨false,false,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,9⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,181⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,795⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,782⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,67⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,181⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,795⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,782⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,67⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,42⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,33⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,510⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,36⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,42⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,33⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,510⟩)),
([⟨false,true,705⟩,⟨true,true,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,36⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,63⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,25⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,30⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,43⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,63⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,25⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,30⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨true,false,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,43⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,685⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,798⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,794⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,9⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,685⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,798⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,794⟩)),
([⟨true,false,705⟩,⟨false,true,775⟩,⟨false,true,752⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,9⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,181⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,795⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,782⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,67⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,181⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,795⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,782⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨false,false,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,67⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,42⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨false,false,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,33⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,510⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨false,true,769⟩,⟨true,true,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,36⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨true,false,743⟩],(.bound ⟨false,false,42⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨false,true,733⟩,⟨false,true,743⟩],(.bound ⟨false,false,33⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨false,false,777⟩],(.bound ⟨false,false,510⟩)),
([⟨true,false,705⟩,⟨true,false,775⟩,⟨true,true,780⟩,⟨true,false,769⟩,⟨true,false,733⟩,⟨true,true,777⟩],(.bound ⟨false,false,36⟩))
]

private theorem branches_68_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 68)
      = (branches_68).map decodeBranch := by
  decide +kernel

private def branches_69 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic)
]

private theorem branches_69_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 69)
      = (branches_69).map decodeBranch := by
  decide +kernel

private def branches_70 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,588⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,170⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,189⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,565⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,588⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,170⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,189⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,565⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,539⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,152⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,184⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,279⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,539⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,152⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,184⟩)),
([⟨false,false,566⟩,⟨false,false,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,279⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,271⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,241⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,312⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,345⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,271⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,241⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,312⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,345⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,555⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,86⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,85⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,548⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,555⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,86⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,85⟩)),
([⟨false,false,566⟩,⟨true,true,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,548⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,588⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,170⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,189⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,565⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,588⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,170⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,189⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨true,false,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,565⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,539⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,152⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,184⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,279⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,539⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,152⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,184⟩)),
([⟨true,true,566⟩,⟨false,true,494⟩,⟨false,true,486⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,279⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,271⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,241⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,312⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,345⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,271⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,241⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,312⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨false,false,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,345⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,555⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨false,false,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,86⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,85⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨false,false,504⟩,⟨true,true,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,548⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨true,false,505⟩],(.bound ⟨true,false,555⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨false,true,549⟩,⟨false,true,505⟩],(.bound ⟨true,false,86⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨false,false,543⟩],(.bound ⟨true,false,85⟩)),
([⟨true,true,566⟩,⟨true,false,494⟩,⟨true,true,525⟩,⟨true,true,504⟩,⟨true,false,549⟩,⟨true,true,543⟩],(.bound ⟨true,false,548⟩))
]

private theorem branches_70_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 70)
      = (branches_70).map decodeBranch := by
  decide +kernel

private def branches_71 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,93⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,46⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,60⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,71⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,93⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,46⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,60⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,71⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,652⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,793⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,786⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,27⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,652⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,793⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,786⟩)),
([⟨false,true,690⟩,⟨false,false,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,27⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,263⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,788⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,755⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,92⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,263⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,788⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,755⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,92⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,66⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,68⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,492⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,61⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,66⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,68⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,492⟩)),
([⟨false,true,690⟩,⟨true,true,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,61⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,93⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,46⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,60⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,71⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,93⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,46⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,60⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨true,false,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,71⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,652⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,793⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,786⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,27⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,652⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,793⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,786⟩)),
([⟨true,false,690⟩,⟨false,true,738⟩,⟨false,true,714⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,27⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,263⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,788⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,755⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,92⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,263⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,788⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,755⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨false,false,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,92⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,66⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨false,false,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,68⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,492⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨false,true,732⟩,⟨true,true,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,61⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨true,false,710⟩],(.bound ⟨false,false,66⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨false,true,699⟩,⟨false,true,710⟩],(.bound ⟨false,false,68⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨false,false,747⟩],(.bound ⟨false,false,492⟩)),
([⟨true,false,690⟩,⟨true,false,738⟩,⟨true,true,750⟩,⟨true,false,732⟩,⟨true,false,699⟩,⟨true,true,747⟩],(.bound ⟨false,false,61⟩))
]

private theorem branches_71_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 71)
      = (branches_71).map decodeBranch := by
  decide +kernel

private def branches_72 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],.automatic)
]

private theorem branches_72_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 72)
      = (branches_72).map decodeBranch := by
  decide +kernel

private def branches_73 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,634⟩,⟨true,false,605⟩],(.bound ⟨true,false,659⟩)),
([⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,634⟩,⟨false,true,605⟩],(.bound ⟨true,false,100⟩)),
([⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,634⟩,⟨false,false,668⟩],(.bound ⟨true,false,112⟩)),
([⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,634⟩,⟨true,true,668⟩],(.bound ⟨true,false,651⟩)),
([⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,634⟩,⟨true,false,605⟩],(.bound ⟨true,false,625⟩)),
([⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,634⟩,⟨false,true,605⟩],(.bound ⟨true,false,102⟩)),
([⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,634⟩,⟨false,false,668⟩],(.bound ⟨true,false,151⟩)),
([⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,634⟩,⟨true,true,668⟩],(.bound ⟨true,false,167⟩)),
([⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,634⟩,⟨true,false,605⟩],(.bound ⟨true,false,172⟩)),
([⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,634⟩,⟨false,true,605⟩],(.bound ⟨true,false,150⟩)),
([⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,634⟩,⟨false,false,668⟩],(.bound ⟨true,false,272⟩)),
([⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,634⟩,⟨true,true,668⟩],(.bound ⟨true,false,292⟩)),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,634⟩,⟨true,false,605⟩],(.bound ⟨true,false,623⟩)),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,634⟩,⟨false,true,605⟩],(.bound ⟨true,false,56⟩)),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,634⟩,⟨false,false,668⟩],(.bound ⟨true,false,54⟩)),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,634⟩,⟨true,true,668⟩],(.bound ⟨true,false,620⟩))
]

private theorem branches_73_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 73)
      = (branches_73).map decodeBranch := by
  decide +kernel

private def branches_74 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,696⟩,⟨true,false,648⟩,⟨false,true,734⟩,⟨true,false,737⟩],(.bound ⟨false,false,22⟩)),
([⟨false,true,696⟩,⟨true,false,648⟩,⟨false,true,734⟩,⟨false,true,737⟩],(.bound ⟨false,false,135⟩)),
([⟨false,true,696⟩,⟨true,false,648⟩,⟨true,false,734⟩,⟨false,false,773⟩],(.bound ⟨false,false,129⟩)),
([⟨false,true,696⟩,⟨true,false,648⟩,⟨true,false,734⟩,⟨true,true,773⟩],(.bound ⟨false,false,8⟩)),
([⟨false,true,696⟩,⟨false,true,648⟩,⟨false,true,734⟩,⟨true,false,737⟩],(.bound ⟨false,false,1⟩)),
([⟨false,true,696⟩,⟨false,true,648⟩,⟨false,true,734⟩,⟨false,true,737⟩],(.bound ⟨false,false,7⟩)),
([⟨false,true,696⟩,⟨false,true,648⟩,⟨true,false,734⟩,⟨false,false,773⟩],(.bound ⟨false,false,3⟩)),
([⟨false,true,696⟩,⟨false,true,648⟩,⟨true,false,734⟩,⟨true,true,773⟩],(.bound ⟨false,false,783⟩)),
([⟨true,false,696⟩,⟨false,false,691⟩,⟨false,true,734⟩,⟨true,false,737⟩],(.bound ⟨false,false,2⟩)),
([⟨true,false,696⟩,⟨false,false,691⟩,⟨false,true,734⟩,⟨false,true,737⟩],(.bound ⟨false,false,789⟩)),
([⟨true,false,696⟩,⟨false,false,691⟩,⟨true,false,734⟩,⟨false,false,773⟩],(.bound ⟨false,false,784⟩)),
([⟨true,false,696⟩,⟨false,false,691⟩,⟨true,false,734⟩,⟨true,true,773⟩],(.bound ⟨false,false,65⟩)),
([⟨true,false,696⟩,⟨true,true,691⟩,⟨false,true,734⟩,⟨true,false,737⟩],(.bound ⟨false,false,6⟩)),
([⟨true,false,696⟩,⟨true,true,691⟩,⟨false,true,734⟩,⟨false,true,737⟩],(.bound ⟨false,false,661⟩)),
([⟨true,false,696⟩,⟨true,true,691⟩,⟨true,false,734⟩,⟨false,false,773⟩],(.bound ⟨false,false,654⟩)),
([⟨true,false,696⟩,⟨true,true,691⟩,⟨true,false,734⟩,⟨true,true,773⟩],(.bound ⟨false,false,4⟩))
]

private theorem branches_74_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 74)
      = (branches_74).map decodeBranch := by
  decide +kernel

private def branches_75 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,680⟩,⟨true,false,627⟩],(.bound ⟨true,false,615⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,680⟩,⟨false,true,627⟩],(.bound ⟨true,false,195⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,680⟩,⟨false,false,686⟩],(.bound ⟨true,false,586⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,680⟩,⟨true,true,686⟩],(.bound ⟨true,false,589⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,680⟩,⟨true,false,627⟩],(.bound ⟨true,false,678⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,680⟩,⟨false,true,627⟩],(.bound ⟨true,false,557⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,680⟩,⟨false,false,686⟩],(.bound ⟨true,false,479⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,680⟩,⟨true,true,686⟩],(.bound ⟨true,false,198⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,680⟩,⟨true,false,627⟩],(.bound ⟨true,false,103⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,680⟩,⟨false,true,627⟩],(.bound ⟨true,false,542⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,680⟩,⟨false,false,686⟩],(.bound ⟨true,false,440⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,680⟩,⟨true,true,686⟩],(.bound ⟨true,false,209⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,680⟩,⟨true,false,627⟩],(.bound ⟨true,false,585⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,680⟩,⟨false,true,627⟩],(.bound ⟨true,false,474⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,680⟩,⟨false,false,686⟩],(.bound ⟨true,false,571⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,680⟩,⟨true,true,686⟩],(.bound ⟨true,false,573⟩))
]

private theorem branches_75_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 75)
      = (branches_75).map decodeBranch := by
  decide +kernel

private def branches_76 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,680⟩,⟨true,false,689⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,467⟩)),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,595⟩)),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,131⟩)),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,493⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,477⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,781⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,749⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,536⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,551⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,772⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,711⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,593⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,487⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,41⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,554⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,501⟩))
]

private theorem branches_76_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 76)
      = (branches_76).map decodeBranch := by
  decide +kernel

private def branches_77 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,680⟩,⟨true,false,689⟩,⟨false,false,640⟩,⟨true,false,604⟩],(.bound ⟨false,false,187⟩)),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨false,false,640⟩,⟨false,true,604⟩],(.bound ⟨false,false,163⟩)),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨true,true,640⟩,⟨false,false,667⟩],(.bound ⟨false,false,84⟩)),
([⟨false,false,680⟩,⟨true,false,689⟩,⟨true,true,640⟩,⟨true,true,667⟩],(.bound ⟨false,false,132⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨false,false,640⟩,⟨true,false,604⟩],(.bound ⟨false,false,174⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨false,false,640⟩,⟨false,true,604⟩],(.bound ⟨false,false,770⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨true,true,640⟩,⟨false,false,667⟩],(.bound ⟨false,false,742⟩)),
([⟨false,false,680⟩,⟨false,true,689⟩,⟨true,true,640⟩,⟨true,true,667⟩],(.bound ⟨false,false,248⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨false,false,640⟩,⟨true,false,604⟩],(.bound ⟨false,false,247⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨false,false,640⟩,⟨false,true,604⟩],(.bound ⟨false,false,748⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨true,true,640⟩,⟨false,false,667⟩],(.bound ⟨false,false,704⟩)),
([⟨true,true,680⟩,⟨false,false,712⟩,⟨true,true,640⟩,⟨true,true,667⟩],(.bound ⟨false,false,470⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨false,false,640⟩,⟨true,false,604⟩],(.bound ⟨false,false,146⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨false,false,640⟩,⟨false,true,604⟩],(.bound ⟨false,false,58⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨true,true,640⟩,⟨false,false,667⟩],(.bound ⟨false,false,311⟩)),
([⟨true,true,680⟩,⟨true,true,712⟩,⟨true,true,640⟩,⟨true,true,667⟩],(.bound ⟨false,false,119⟩))
]

private theorem branches_77_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 77)
      = (branches_77).map decodeBranch := by
  decide +kernel

private def branches_78 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,680⟩,⟨true,false,627⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,680⟩,⟨false,true,627⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,680⟩,⟨false,false,686⟩],.automatic),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,680⟩,⟨true,true,686⟩],.automatic)
]

private theorem branches_78_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 78)
      = (branches_78).map decodeBranch := by
  decide +kernel

private def branches_79 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,44⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,266⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,191⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,28⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,44⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,266⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,191⟩)),
([⟨false,false,640⟩,⟨true,false,612⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,28⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,14⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,745⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,725⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,107⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,14⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,745⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,725⟩)),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,107⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,13⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,730⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,709⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,173⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,13⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,730⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,709⟩)),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,173⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,29⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,120⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,158⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,681⟩,⟨true,true,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,23⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨true,false,697⟩],(.bound ⟨false,false,29⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,681⟩,⟨false,true,696⟩,⟨false,true,697⟩],(.bound ⟨false,false,120⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨false,false,723⟩],(.bound ⟨false,false,158⟩)),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,681⟩,⟨true,false,696⟩,⟨true,true,723⟩],(.bound ⟨false,false,23⟩))
]

private theorem branches_79_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 79)
      = (branches_79).map decodeBranch := by
  decide +kernel

private def branches_80 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨false,false,681⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨false,false,681⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨true,false,601⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨true,true,681⟩,⟨false,true,634⟩,⟨false,true,601⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨false,false,664⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,640⟩,⟨true,false,604⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨false,false,640⟩,⟨false,true,604⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,640⟩,⟨false,false,667⟩],.automatic),
([⟨true,true,681⟩,⟨true,false,634⟩,⟨true,true,664⟩,⟨true,true,640⟩,⟨true,true,667⟩],.automatic)
]

private theorem branches_80_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 80)
      = (branches_80).map decodeBranch := by
  decide +kernel

private def branches_81 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,643⟩,⟨true,false,610⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,431⟩)),
([⟨false,false,643⟩,⟨true,false,610⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,771⟩)),
([⟨false,false,643⟩,⟨true,false,610⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,649⟩)),
([⟨false,false,643⟩,⟨true,false,610⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,489⟩)),
([⟨false,false,643⟩,⟨false,true,610⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,72⟩)),
([⟨false,false,643⟩,⟨false,true,610⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,774⟩)),
([⟨false,false,643⟩,⟨false,true,610⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,702⟩)),
([⟨false,false,643⟩,⟨false,true,610⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,410⟩)),
([⟨true,true,643⟩,⟨false,false,673⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,356⟩)),
([⟨true,true,643⟩,⟨false,false,673⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,766⟩)),
([⟨true,true,643⟩,⟨false,false,673⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,646⟩)),
([⟨true,true,643⟩,⟨false,false,673⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,495⟩)),
([⟨true,true,643⟩,⟨true,true,673⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,478⟩)),
([⟨true,true,643⟩,⟨true,true,673⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,37⟩)),
([⟨true,true,643⟩,⟨true,true,673⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,288⟩)),
([⟨true,true,643⟩,⟨true,true,673⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,491⟩))
]

private theorem branches_81_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 81)
      = (branches_81).map decodeBranch := by
  decide +kernel

private def branches_82 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,643⟩,⟨true,false,607⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,643⟩,⟨false,true,607⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,643⟩,⟨false,false,670⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,643⟩,⟨true,true,670⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,643⟩,⟨true,false,607⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,643⟩,⟨false,true,607⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,643⟩,⟨false,false,670⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,643⟩,⟨true,true,670⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,643⟩,⟨true,false,607⟩],(.bound ⟨true,false,357⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,643⟩,⟨false,true,607⟩],(.bound ⟨true,false,369⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,643⟩,⟨false,false,670⟩],(.bound ⟨true,false,370⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,643⟩,⟨true,true,670⟩],(.bound ⟨true,false,418⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,643⟩,⟨true,false,607⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,643⟩,⟨false,true,607⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,643⟩,⟨false,false,670⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,643⟩,⟨true,true,670⟩],.automatic)
]

private theorem branches_82_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 82)
      = (branches_82).map decodeBranch := by
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
  if g = 61 then branches_61 else
  if g = 62 then branches_62 else
  if g = 63 then branches_63 else
  if g = 64 then branches_64 else
  if g = 65 then branches_65 else
  if g = 66 then branches_66 else
  if g = 67 then branches_67 else
  if g = 68 then branches_68 else
  if g = 69 then branches_69 else
  if g = 70 then branches_70 else
  if g = 71 then branches_71 else
  if g = 72 then branches_72 else
  if g = 73 then branches_73 else
  if g = 74 then branches_74 else
  if g = 75 then branches_75 else
  if g = 76 then branches_76 else
  if g = 77 then branches_77 else
  if g = 78 then branches_78 else
  if g = 79 then branches_79 else
  if g = 80 then branches_80 else
  if g = 81 then branches_81 else
  if g = 82 then branches_82 else
  []

private theorem cb_61 : cachedBranches 61 = branches_61 := by
  norm_num [cachedBranches]

private theorem cb_62 : cachedBranches 62 = branches_62 := by
  norm_num [cachedBranches]

private theorem cb_63 : cachedBranches 63 = branches_63 := by
  norm_num [cachedBranches]

private theorem cb_64 : cachedBranches 64 = branches_64 := by
  norm_num [cachedBranches]

private theorem cb_65 : cachedBranches 65 = branches_65 := by
  norm_num [cachedBranches]

private theorem cb_66 : cachedBranches 66 = branches_66 := by
  norm_num [cachedBranches]

private theorem cb_67 : cachedBranches 67 = branches_67 := by
  norm_num [cachedBranches]

private theorem cb_68 : cachedBranches 68 = branches_68 := by
  norm_num [cachedBranches]

private theorem cb_69 : cachedBranches 69 = branches_69 := by
  norm_num [cachedBranches]

private theorem cb_70 : cachedBranches 70 = branches_70 := by
  norm_num [cachedBranches]

private theorem cb_71 : cachedBranches 71 = branches_71 := by
  norm_num [cachedBranches]

private theorem cb_72 : cachedBranches 72 = branches_72 := by
  norm_num [cachedBranches]

private theorem cb_73 : cachedBranches 73 = branches_73 := by
  norm_num [cachedBranches]

private theorem cb_74 : cachedBranches 74 = branches_74 := by
  norm_num [cachedBranches]

private theorem cb_75 : cachedBranches 75 = branches_75 := by
  norm_num [cachedBranches]

private theorem cb_76 : cachedBranches 76 = branches_76 := by
  norm_num [cachedBranches]

private theorem cb_77 : cachedBranches 77 = branches_77 := by
  norm_num [cachedBranches]

private theorem cb_78 : cachedBranches 78 = branches_78 := by
  norm_num [cachedBranches]

private theorem cb_79 : cachedBranches 79 = branches_79 := by
  norm_num [cachedBranches]

private theorem cb_80 : cachedBranches 80 = branches_80 := by
  norm_num [cachedBranches]

private theorem cb_81 : cachedBranches 81 = branches_81 := by
  norm_num [cachedBranches]

private theorem cb_82 : cachedBranches 82 = branches_82 := by
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

private def selectedGoals : List ℕ := [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]

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
    rcases hg with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
    · simpa only [hg, cb_61] using branches_61_eq
    · simpa only [hg, cb_62] using branches_62_eq
    · simpa only [hg, cb_63] using branches_63_eq
    · simpa only [hg, cb_64] using branches_64_eq
    · simpa only [hg, cb_65] using branches_65_eq
    · simpa only [hg, cb_66] using branches_66_eq
    · simpa only [hg, cb_67] using branches_67_eq
    · simpa only [hg, cb_68] using branches_68_eq
    · simpa only [hg, cb_69] using branches_69_eq
    · simpa only [hg, cb_70] using branches_70_eq
    · simpa only [hg, cb_71] using branches_71_eq
    · simpa only [hg, cb_72] using branches_72_eq
    · simpa only [hg, cb_73] using branches_73_eq
    · simpa only [hg, cb_74] using branches_74_eq
    · simpa only [hg, cb_75] using branches_75_eq
    · simpa only [hg, cb_76] using branches_76_eq
    · simpa only [hg, cb_77] using branches_77_eq
    · simpa only [hg, cb_78] using branches_78_eq
    · simpa only [hg, cb_79] using branches_79_eq
    · simpa only [hg, cb_80] using branches_80_eq
    · simpa only [hg, cb_81] using branches_81_eq
    · simpa only [hg, cb_82] using branches_82_eq
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
  ⟨61,4,[-1],406⟩,
  ⟨61,6,[-1],735⟩,
  ⟨61,7,[-1],1135⟩,
  ⟨61,12,[-1],739⟩,
  ⟨61,13,[-1],739⟩,
  ⟨61,14,[-1],739⟩,
  ⟨62,1,[-1],407⟩,
  ⟨62,2,[-1],739⟩,
  ⟨62,3,[-1],739⟩,
  ⟨62,7,[-1],739⟩,
  ⟨62,8,[-1],750⟩,
  ⟨62,9,[-1],751⟩,
  ⟨62,11,[-1],1137⟩,
  ⟨62,13,[-1],1140⟩,
  ⟨62,17,[-1],407⟩,
  ⟨62,18,[-1],739⟩
]

private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨62,19,[-1],739⟩,
  ⟨62,23,[-1],739⟩,
  ⟨62,24,[-1],919⟩,
  ⟨62,25,[-1],920⟩,
  ⟨62,27,[-1],1137⟩,
  ⟨62,29,[-1],920⟩,
  ⟨64,0,[-1],1062⟩,
  ⟨64,1,[-1],1062⟩,
  ⟨64,2,[-1],1062⟩,
  ⟨64,3,[-1],1062⟩,
  ⟨64,4,[-1],1062⟩,
  ⟨64,5,[-1],1062⟩,
  ⟨64,6,[-1],1062⟩,
  ⟨64,7,[-1],1062⟩,
  ⟨64,8,[-1],1076⟩,
  ⟨64,9,[-1],1076⟩
]

private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨64,10,[-1],1076⟩,
  ⟨64,11,[-1],1076⟩,
  ⟨64,12,[-1],1076⟩,
  ⟨64,13,[-1],1076⟩,
  ⟨64,14,[-1],1076⟩,
  ⟨64,15,[-1],1076⟩,
  ⟨64,16,[-1],1059⟩,
  ⟨64,17,[-1],1059⟩,
  ⟨64,18,[-1],1059⟩,
  ⟨64,19,[-1],1059⟩,
  ⟨64,20,[-1],1063⟩,
  ⟨64,21,[-1],1063⟩,
  ⟨64,22,[-1],1063⟩,
  ⟨64,23,[-1],1063⟩,
  ⟨64,24,[-1],1059⟩,
  ⟨64,25,[-1],1059⟩
]

private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨64,26,[-1],1059⟩,
  ⟨64,27,[-1],1059⟩,
  ⟨64,28,[-1],1073⟩,
  ⟨64,29,[-1],1067⟩,
  ⟨64,30,[-1],1069⟩,
  ⟨64,31,[-1],1077⟩,
  ⟨64,32,[-1],1062⟩,
  ⟨64,33,[-1],1062⟩,
  ⟨64,34,[-1],1062⟩,
  ⟨64,35,[-1],1062⟩,
  ⟨64,36,[-1],1062⟩,
  ⟨64,37,[-1],1062⟩,
  ⟨64,38,[-1],1062⟩,
  ⟨64,39,[-1],1062⟩,
  ⟨64,40,[-1],1076⟩,
  ⟨64,41,[-1],1076⟩
]

private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨64,42,[-1],1076⟩,
  ⟨64,43,[-1],1076⟩,
  ⟨64,44,[-1],1076⟩,
  ⟨64,45,[-1],1076⟩,
  ⟨64,46,[-1],1076⟩,
  ⟨64,47,[-1],1076⟩,
  ⟨64,48,[-1],1059⟩,
  ⟨64,49,[-1],1059⟩,
  ⟨64,50,[-1],1059⟩,
  ⟨64,51,[-1],1059⟩,
  ⟨64,52,[-1],1063⟩,
  ⟨64,53,[-1],1063⟩,
  ⟨64,54,[-1],1063⟩,
  ⟨64,55,[-1],1063⟩,
  ⟨64,56,[-1],1059⟩,
  ⟨64,57,[-1],1059⟩
]

private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨64,58,[-1],1059⟩,
  ⟨64,59,[-1],1059⟩,
  ⟨64,60,[-1],1073⟩,
  ⟨64,61,[-1],1067⟩,
  ⟨64,62,[-1],1069⟩,
  ⟨64,63,[-1],1077⟩,
  ⟨65,0,[-1],225⟩,
  ⟨65,1,[-1],225⟩,
  ⟨65,2,[-1],225⟩,
  ⟨65,3,[-1],225⟩,
  ⟨65,4,[-1],800⟩,
  ⟨65,5,[-1],800⟩,
  ⟨65,6,[-1],800⟩,
  ⟨65,7,[-1],800⟩,
  ⟨65,8,[-1],930⟩,
  ⟨65,9,[-1],1122⟩
]

private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨65,10,[-1],1194⟩,
  ⟨65,11,[-1],670⟩,
  ⟨65,12,[-1],800⟩,
  ⟨65,13,[-1],800⟩,
  ⟨65,14,[-1],800⟩,
  ⟨65,15,[-1],800⟩,
  ⟨65,16,[-1],1176⟩,
  ⟨65,17,[-1],1176⟩,
  ⟨65,18,[-1],1176⟩,
  ⟨65,19,[-1],1176⟩,
  ⟨65,20,[-1],1176⟩,
  ⟨65,21,[-1],1176⟩,
  ⟨65,22,[-1],1176⟩,
  ⟨65,23,[-1],1176⟩,
  ⟨65,24,[-1],998⟩,
  ⟨65,25,[-1],998⟩
]

private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨65,26,[-1],998⟩,
  ⟨65,27,[-1],998⟩,
  ⟨65,28,[-1],998⟩,
  ⟨65,29,[-1],998⟩,
  ⟨65,30,[-1],998⟩,
  ⟨65,31,[-1],998⟩,
  ⟨65,32,[-1],225⟩,
  ⟨65,33,[-1],225⟩,
  ⟨65,34,[-1],225⟩,
  ⟨65,35,[-1],225⟩,
  ⟨65,36,[-1],800⟩,
  ⟨65,37,[-1],800⟩,
  ⟨65,38,[-1],800⟩,
  ⟨65,39,[-1],800⟩,
  ⟨65,40,[-1],930⟩,
  ⟨65,41,[-1],1122⟩
]

private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨65,42,[-1],1194⟩,
  ⟨65,43,[-1],670⟩,
  ⟨65,44,[-1],800⟩,
  ⟨65,45,[-1],800⟩,
  ⟨65,46,[-1],800⟩,
  ⟨65,47,[-1],800⟩,
  ⟨65,48,[-1],1176⟩,
  ⟨65,49,[-1],1176⟩,
  ⟨65,50,[-1],1176⟩,
  ⟨65,51,[-1],1176⟩,
  ⟨65,52,[-1],1176⟩,
  ⟨65,53,[-1],1176⟩,
  ⟨65,54,[-1],1176⟩,
  ⟨65,55,[-1],1176⟩,
  ⟨65,56,[-1],998⟩,
  ⟨65,57,[-1],998⟩
]

private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨65,58,[-1],998⟩,
  ⟨65,59,[-1],998⟩,
  ⟨65,60,[-1],998⟩,
  ⟨65,61,[-1],998⟩,
  ⟨65,62,[-1],998⟩,
  ⟨65,63,[-1],998⟩,
  ⟨67,0,[-1],1054⟩,
  ⟨67,1,[-1],1054⟩,
  ⟨67,2,[-1],1169⟩,
  ⟨67,3,[-1],892⟩,
  ⟨67,4,[-1],1054⟩,
  ⟨67,5,[-1],1054⟩,
  ⟨67,6,[-1],1169⟩,
  ⟨67,7,[-1],892⟩,
  ⟨67,8,[-1],1072⟩,
  ⟨67,9,[-1],1072⟩
]

private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨67,10,[-1],1173⟩,
  ⟨67,11,[-1],895⟩,
  ⟨67,12,[-1],1072⟩,
  ⟨67,13,[-1],1072⟩,
  ⟨67,14,[-1],1173⟩,
  ⟨67,15,[-1],895⟩,
  ⟨67,16,[-1],1060⟩,
  ⟨67,17,[-1],1060⟩,
  ⟨67,18,[-1],1170⟩,
  ⟨67,19,[-1],893⟩,
  ⟨67,20,[-1],1061⟩,
  ⟨67,21,[-1],1061⟩,
  ⟨67,22,[-1],1171⟩,
  ⟨67,23,[-1],894⟩,
  ⟨67,24,[-1],1060⟩,
  ⟨67,25,[-1],1060⟩
]

private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨67,26,[-1],1170⟩,
  ⟨67,27,[-1],893⟩,
  ⟨67,28,[-1],1074⟩,
  ⟨67,29,[-1],1066⟩,
  ⟨67,30,[-1],1172⟩,
  ⟨67,31,[-1],896⟩,
  ⟨67,32,[-1],1126⟩,
  ⟨67,33,[-1],1126⟩,
  ⟨67,34,[-1],1169⟩,
  ⟨67,35,[-1],892⟩,
  ⟨67,36,[-1],1126⟩,
  ⟨67,37,[-1],1126⟩,
  ⟨67,38,[-1],1169⟩,
  ⟨67,39,[-1],892⟩,
  ⟨67,40,[-1],1130⟩,
  ⟨67,41,[-1],1130⟩
]

private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨67,42,[-1],1173⟩,
  ⟨67,43,[-1],895⟩,
  ⟨67,44,[-1],1130⟩,
  ⟨67,45,[-1],1130⟩,
  ⟨67,46,[-1],1173⟩,
  ⟨67,47,[-1],895⟩,
  ⟨67,48,[-1],1127⟩,
  ⟨67,49,[-1],1127⟩,
  ⟨67,50,[-1],1170⟩,
  ⟨67,51,[-1],893⟩,
  ⟨67,52,[-1],1128⟩,
  ⟨67,53,[-1],1128⟩,
  ⟨67,54,[-1],1171⟩,
  ⟨67,55,[-1],894⟩,
  ⟨67,56,[-1],1127⟩,
  ⟨67,57,[-1],1127⟩
]

private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨67,58,[-1],1170⟩,
  ⟨67,59,[-1],893⟩,
  ⟨67,60,[-1],1131⟩,
  ⟨67,61,[-1],1129⟩,
  ⟨67,62,[-1],1172⟩,
  ⟨67,63,[-1],896⟩,
  ⟨68,0,[-1],179⟩,
  ⟨68,1,[-1],179⟩,
  ⟨68,2,[-1],179⟩,
  ⟨68,3,[-1],179⟩,
  ⟨68,4,[-1],792⟩,
  ⟨68,5,[-1],792⟩,
  ⟨68,6,[-1],792⟩,
  ⟨68,7,[-1],792⟩,
  ⟨68,8,[-1],898⟩,
  ⟨68,9,[-1],1182⟩
]

private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨68,10,[-1],1020⟩,
  ⟨68,11,[-1],611⟩,
  ⟨68,12,[-1],792⟩,
  ⟨68,13,[-1],792⟩,
  ⟨68,14,[-1],792⟩,
  ⟨68,15,[-1],792⟩,
  ⟨68,16,[-1],833⟩,
  ⟨68,17,[-1],833⟩,
  ⟨68,18,[-1],833⟩,
  ⟨68,19,[-1],833⟩,
  ⟨68,20,[-1],833⟩,
  ⟨68,21,[-1],833⟩,
  ⟨68,22,[-1],833⟩,
  ⟨68,23,[-1],833⟩,
  ⟨68,24,[-1],1180⟩,
  ⟨68,25,[-1],1180⟩
]

private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨68,26,[-1],1180⟩,
  ⟨68,27,[-1],1180⟩,
  ⟨68,28,[-1],1180⟩,
  ⟨68,29,[-1],1180⟩,
  ⟨68,30,[-1],1180⟩,
  ⟨68,31,[-1],1180⟩,
  ⟨68,32,[-1],179⟩,
  ⟨68,33,[-1],179⟩,
  ⟨68,34,[-1],179⟩,
  ⟨68,35,[-1],179⟩,
  ⟨68,36,[-1],792⟩,
  ⟨68,37,[-1],792⟩,
  ⟨68,38,[-1],792⟩,
  ⟨68,39,[-1],792⟩,
  ⟨68,40,[-1],898⟩,
  ⟨68,41,[-1],1182⟩
]

private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨68,42,[-1],1020⟩,
  ⟨68,43,[-1],611⟩,
  ⟨68,44,[-1],792⟩,
  ⟨68,45,[-1],792⟩,
  ⟨68,46,[-1],792⟩,
  ⟨68,47,[-1],792⟩,
  ⟨68,48,[-1],833⟩,
  ⟨68,49,[-1],833⟩,
  ⟨68,50,[-1],833⟩,
  ⟨68,51,[-1],833⟩,
  ⟨68,52,[-1],833⟩,
  ⟨68,53,[-1],833⟩,
  ⟨68,54,[-1],833⟩,
  ⟨68,55,[-1],833⟩,
  ⟨68,56,[-1],1180⟩,
  ⟨68,57,[-1],1180⟩
]

private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨68,58,[-1],1180⟩,
  ⟨68,59,[-1],1180⟩,
  ⟨68,60,[-1],1180⟩,
  ⟨68,61,[-1],1180⟩,
  ⟨68,62,[-1],1180⟩,
  ⟨68,63,[-1],1180⟩,
  ⟨70,0,[-1],1055⟩,
  ⟨70,1,[-1],1055⟩,
  ⟨70,2,[-1],1055⟩,
  ⟨70,3,[-1],1243⟩,
  ⟨70,4,[-1],1055⟩,
  ⟨70,5,[-1],1055⟩,
  ⟨70,6,[-1],1055⟩,
  ⟨70,7,[-1],1243⟩,
  ⟨70,8,[-1],1071⟩,
  ⟨70,9,[-1],1071⟩
]

private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨70,10,[-1],1071⟩,
  ⟨70,11,[-1],1246⟩,
  ⟨70,12,[-1],1071⟩,
  ⟨70,13,[-1],1071⟩,
  ⟨70,14,[-1],1071⟩,
  ⟨70,15,[-1],1246⟩,
  ⟨70,16,[-1],1057⟩,
  ⟨70,17,[-1],1057⟩,
  ⟨70,18,[-1],1057⟩,
  ⟨70,19,[-1],1245⟩,
  ⟨70,20,[-1],1056⟩,
  ⟨70,21,[-1],1056⟩,
  ⟨70,22,[-1],1056⟩,
  ⟨70,23,[-1],1244⟩,
  ⟨70,24,[-1],1057⟩,
  ⟨70,25,[-1],1057⟩
]

private theorem refs_valid_18 : ∀ rec ∈ chunk_18, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨70,26,[-1],1057⟩,
  ⟨70,27,[-1],1245⟩,
  ⟨70,28,[-1],1079⟩,
  ⟨70,29,[-1],1064⟩,
  ⟨70,30,[-1],1070⟩,
  ⟨70,31,[-1],1247⟩,
  ⟨70,32,[-1],1055⟩,
  ⟨70,33,[-1],1055⟩,
  ⟨70,34,[-1],1055⟩,
  ⟨70,35,[-1],1243⟩,
  ⟨70,36,[-1],1055⟩,
  ⟨70,37,[-1],1055⟩,
  ⟨70,38,[-1],1055⟩,
  ⟨70,39,[-1],1243⟩,
  ⟨70,40,[-1],1071⟩,
  ⟨70,41,[-1],1071⟩
]

private theorem refs_valid_19 : ∀ rec ∈ chunk_19, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨70,42,[-1],1071⟩,
  ⟨70,43,[-1],1246⟩,
  ⟨70,44,[-1],1071⟩,
  ⟨70,45,[-1],1071⟩,
  ⟨70,46,[-1],1071⟩,
  ⟨70,47,[-1],1246⟩,
  ⟨70,48,[-1],1057⟩,
  ⟨70,49,[-1],1057⟩,
  ⟨70,50,[-1],1057⟩,
  ⟨70,51,[-1],1245⟩,
  ⟨70,52,[-1],1056⟩,
  ⟨70,53,[-1],1056⟩,
  ⟨70,54,[-1],1056⟩,
  ⟨70,55,[-1],1244⟩,
  ⟨70,56,[-1],1057⟩,
  ⟨70,57,[-1],1057⟩
]

private theorem refs_valid_20 : ∀ rec ∈ chunk_20, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_21 : List MiddleCertRecord := [
  ⟨70,58,[-1],1057⟩,
  ⟨70,59,[-1],1245⟩,
  ⟨70,60,[-1],1079⟩,
  ⟨70,61,[-1],1064⟩,
  ⟨70,62,[-1],1070⟩,
  ⟨70,63,[-1],1247⟩,
  ⟨71,0,[-1],532⟩,
  ⟨71,1,[-1],532⟩,
  ⟨71,2,[-1],532⟩,
  ⟨71,3,[-1],532⟩,
  ⟨71,4,[-1],1047⟩,
  ⟨71,5,[-1],1047⟩,
  ⟨71,6,[-1],1047⟩,
  ⟨71,7,[-1],1047⟩,
  ⟨71,8,[-1],824⟩,
  ⟨71,9,[-1],1011⟩
]

private theorem refs_valid_21 : ∀ rec ∈ chunk_21, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_22 : List MiddleCertRecord := [
  ⟨71,10,[-1],831⟩,
  ⟨71,11,[-1],677⟩,
  ⟨71,12,[-1],1047⟩,
  ⟨71,13,[-1],1047⟩,
  ⟨71,14,[-1],1047⟩,
  ⟨71,15,[-1],1047⟩,
  ⟨71,16,[-1],1117⟩,
  ⟨71,17,[-1],1117⟩,
  ⟨71,18,[-1],1117⟩,
  ⟨71,19,[-1],1117⟩,
  ⟨71,20,[-1],1117⟩,
  ⟨71,21,[-1],1117⟩,
  ⟨71,22,[-1],1117⟩,
  ⟨71,23,[-1],1117⟩,
  ⟨71,24,[-1],1000⟩,
  ⟨71,25,[-1],1000⟩
]

private theorem refs_valid_22 : ∀ rec ∈ chunk_22, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_23 : List MiddleCertRecord := [
  ⟨71,26,[-1],1000⟩,
  ⟨71,27,[-1],1000⟩,
  ⟨71,28,[-1],1000⟩,
  ⟨71,29,[-1],1000⟩,
  ⟨71,30,[-1],1000⟩,
  ⟨71,31,[-1],1000⟩,
  ⟨71,32,[-1],532⟩,
  ⟨71,33,[-1],532⟩,
  ⟨71,34,[-1],532⟩,
  ⟨71,35,[-1],532⟩,
  ⟨71,36,[-1],1047⟩,
  ⟨71,37,[-1],1047⟩,
  ⟨71,38,[-1],1047⟩,
  ⟨71,39,[-1],1047⟩,
  ⟨71,40,[-1],824⟩,
  ⟨71,41,[-1],1011⟩
]

private theorem refs_valid_23 : ∀ rec ∈ chunk_23, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_24 : List MiddleCertRecord := [
  ⟨71,42,[-1],831⟩,
  ⟨71,43,[-1],677⟩,
  ⟨71,44,[-1],1047⟩,
  ⟨71,45,[-1],1047⟩,
  ⟨71,46,[-1],1047⟩,
  ⟨71,47,[-1],1047⟩,
  ⟨71,48,[-1],1117⟩,
  ⟨71,49,[-1],1117⟩,
  ⟨71,50,[-1],1117⟩,
  ⟨71,51,[-1],1117⟩,
  ⟨71,52,[-1],1117⟩,
  ⟨71,53,[-1],1117⟩,
  ⟨71,54,[-1],1117⟩,
  ⟨71,55,[-1],1117⟩,
  ⟨71,56,[-1],1000⟩,
  ⟨71,57,[-1],1000⟩
]

private theorem refs_valid_24 : ∀ rec ∈ chunk_24, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_25 : List MiddleCertRecord := [
  ⟨71,58,[-1],1000⟩,
  ⟨71,59,[-1],1000⟩,
  ⟨71,60,[-1],1000⟩,
  ⟨71,61,[-1],1000⟩,
  ⟨71,62,[-1],1000⟩,
  ⟨71,63,[-1],1000⟩,
  ⟨73,0,[-1],408⟩,
  ⟨73,1,[-1],1053⟩,
  ⟨73,2,[-1],740⟩,
  ⟨73,3,[-1],1141⟩,
  ⟨73,4,[-1],411⟩,
  ⟨73,5,[-1],1078⟩,
  ⟨73,6,[-1],753⟩,
  ⟨73,7,[-1],1144⟩,
  ⟨73,8,[-1],409⟩,
  ⟨73,9,[-1],1058⟩
]

private theorem refs_valid_25 : ∀ rec ∈ chunk_25, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_26 : List MiddleCertRecord := [
  ⟨73,10,[-1],743⟩,
  ⟨73,11,[-1],1142⟩,
  ⟨73,12,[-1],410⟩,
  ⟨73,13,[-1],1065⟩,
  ⟨73,14,[-1],747⟩,
  ⟨73,15,[-1],1143⟩,
  ⟨74,0,[-1],536⟩,
  ⟨74,1,[-1],667⟩,
  ⟨74,2,[-1],777⟩,
  ⟨74,3,[-1],794⟩,
  ⟨74,4,[-1],536⟩,
  ⟨74,5,[-1],595⟩,
  ⟨74,6,[-1],777⟩,
  ⟨74,7,[-1],794⟩,
  ⟨74,8,[-1],536⟩,
  ⟨74,9,[-1],902⟩
]

private theorem refs_valid_26 : ∀ rec ∈ chunk_26, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_27 : List MiddleCertRecord := [
  ⟨74,10,[-1],777⟩,
  ⟨74,11,[-1],794⟩,
  ⟨74,12,[-1],536⟩,
  ⟨74,13,[-1],1009⟩,
  ⟨74,14,[-1],777⟩,
  ⟨74,15,[-1],794⟩,
  ⟨75,0,[-1],228⟩,
  ⟨75,1,[-1],1068⟩,
  ⟨75,2,[-1],910⟩,
  ⟨75,3,[-1],808⟩,
  ⟨75,4,[-1],227⟩,
  ⟨75,5,[-1],1075⟩,
  ⟨75,6,[-1],912⟩,
  ⟨75,7,[-1],806⟩,
  ⟨75,8,[-1],226⟩,
  ⟨75,9,[-1],842⟩
]

private theorem refs_valid_27 : ∀ rec ∈ chunk_27, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_28 : List MiddleCertRecord := [
  ⟨75,10,[-1],911⟩,
  ⟨75,11,[-1],807⟩,
  ⟨75,12,[-1],229⟩,
  ⟨75,13,[-1],1114⟩,
  ⟨75,14,[-1],915⟩,
  ⟨75,15,[-1],809⟩,
  ⟨76,0,[-1],805⟩,
  ⟨76,1,[-1],1001⟩,
  ⟨76,2,[-1],620⟩,
  ⟨76,3,[-1],1087⟩,
  ⟨76,4,[-1],1178⟩,
  ⟨76,5,[-1],822⟩,
  ⟨76,6,[-1],1085⟩,
  ⟨76,7,[-1],829⟩,
  ⟨76,8,[-1],891⟩,
  ⟨76,9,[-1],890⟩
]

private theorem refs_valid_28 : ∀ rec ∈ chunk_28, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_29 : List MiddleCertRecord := [
  ⟨76,10,[-1],1024⟩,
  ⟨76,11,[-1],1022⟩,
  ⟨76,12,[-1],801⟩,
  ⟨76,13,[-1],680⟩,
  ⟨76,14,[-1],1249⟩,
  ⟨76,15,[-1],1198⟩,
  ⟨77,0,[-1],232⟩,
  ⟨77,1,[-1],231⟩,
  ⟨77,2,[-1],232⟩,
  ⟨77,3,[-1],1134⟩,
  ⟨77,4,[-1],613⟩,
  ⟨77,5,[-1],804⟩,
  ⟨77,6,[-1],1196⟩,
  ⟨77,7,[-1],714⟩,
  ⟨77,8,[-1],914⟩,
  ⟨77,9,[-1],913⟩
]

private theorem refs_valid_29 : ∀ rec ∈ chunk_29, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_30 : List MiddleCertRecord := [
  ⟨77,10,[-1],914⟩,
  ⟨77,11,[-1],914⟩,
  ⟨77,12,[-1],821⟩,
  ⟨77,13,[-1],820⟩,
  ⟨77,14,[-1],821⟩,
  ⟨77,15,[-1],821⟩,
  ⟨79,0,[-1],494⟩,
  ⟨79,1,[-1],710⟩,
  ⟨79,2,[-1],1044⟩,
  ⟨79,3,[-1],1190⟩,
  ⟨79,4,[-1],494⟩,
  ⟨79,5,[-1],919⟩,
  ⟨79,6,[-1],1044⟩,
  ⟨79,7,[-1],1190⟩,
  ⟨79,8,[-1],495⟩,
  ⟨79,9,[-1],1125⟩
]

private theorem refs_valid_30 : ∀ rec ∈ chunk_30, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_31 : List MiddleCertRecord := [
  ⟨79,10,[-1],1045⟩,
  ⟨79,11,[-1],1191⟩,
  ⟨79,12,[-1],495⟩,
  ⟨79,13,[-1],921⟩,
  ⟨79,14,[-1],1045⟩,
  ⟨79,15,[-1],1191⟩,
  ⟨79,16,[-1],494⟩,
  ⟨79,17,[-1],1242⟩,
  ⟨79,18,[-1],1044⟩,
  ⟨79,19,[-1],1190⟩,
  ⟨79,20,[-1],494⟩,
  ⟨79,21,[-1],919⟩,
  ⟨79,22,[-1],1044⟩,
  ⟨79,23,[-1],1190⟩,
  ⟨79,24,[-1],494⟩,
  ⟨79,25,[-1],712⟩
]

private theorem refs_valid_31 : ∀ rec ∈ chunk_31, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_32 : List MiddleCertRecord := [
  ⟨79,26,[-1],1044⟩,
  ⟨79,27,[-1],1190⟩,
  ⟨79,28,[-1],494⟩,
  ⟨79,29,[-1],919⟩,
  ⟨79,30,[-1],1044⟩,
  ⟨79,31,[-1],1190⟩,
  ⟨81,0,[-1],1123⟩,
  ⟨81,1,[-1],1177⟩,
  ⟨81,2,[-1],1012⟩,
  ⟨81,3,[-1],900⟩,
  ⟨81,4,[-1],664⟩,
  ⟨81,5,[-1],1018⟩,
  ⟨81,6,[-1],1115⟩,
  ⟨81,7,[-1],1119⟩,
  ⟨81,8,[-1],754⟩,
  ⟨81,9,[-1],758⟩
]

private theorem refs_valid_32 : ∀ rec ∈ chunk_32, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_33 : List MiddleCertRecord := [
  ⟨81,10,[-1],757⟩,
  ⟨81,11,[-1],757⟩,
  ⟨81,12,[-1],1145⟩,
  ⟨81,13,[-1],1148⟩,
  ⟨81,14,[-1],1147⟩,
  ⟨81,15,[-1],1147⟩,
  ⟨82,8,[-1],457⟩,
  ⟨82,9,[-1],840⟩,
  ⟨82,10,[-1],756⟩,
  ⟨82,11,[-1],1153⟩
]

private theorem refs_valid_33 : ∀ rec ∈ chunk_33, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def selectedRecords : List MiddleCertRecord := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28, chunk_29, chunk_30, chunk_31, chunk_32, chunk_33].flatten

private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by
  decide +kernel

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([4] : List ℕ)))
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact refs_valid_24 rec hr
  · exact refs_valid_25 rec hr
  · exact refs_valid_26 rec hr
  · exact refs_valid_27 rec hr
  · exact refs_valid_28 rec hr
  · exact refs_valid_29 rec hr
  · exact refs_valid_30 rec hr
  · exact refs_valid_31 rec hr
  · exact refs_valid_32 rec hr
  · exact refs_valid_33 rec hr

end RetRow4

open RetRow4

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([4] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)

#print axioms solution
