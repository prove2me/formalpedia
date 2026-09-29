-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_equal_II_b_J_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T17:06:07.287719+00:00
-- url     : https://prove2.me/submissions/66de09c0-f701-44b2-9a52-3af0d84784eb

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

namespace RetRow8

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

private def branches_133 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_133_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 133)
      = (branches_133).map decodeBranch := by
  decide +kernel

private def branches_134 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_134_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 134)
      = (branches_134).map decodeBranch := by
  decide +kernel

private def branches_135 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_135_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 135)
      = (branches_135).map decodeBranch := by
  decide +kernel

private def branches_136 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_136_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 136)
      = (branches_136).map decodeBranch := by
  decide +kernel

private def branches_137 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_137_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 137)
      = (branches_137).map decodeBranch := by
  decide +kernel

private def branches_138 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_138_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 138)
      = (branches_138).map decodeBranch := by
  decide +kernel

private def branches_139 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_139_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 139)
      = (branches_139).map decodeBranch := by
  decide +kernel

private def branches_140 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_140_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 140)
      = (branches_140).map decodeBranch := by
  decide +kernel

private def branches_141 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_141_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 141)
      = (branches_141).map decodeBranch := by
  decide +kernel

private def branches_142 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_142_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 142)
      = (branches_142).map decodeBranch := by
  decide +kernel

private def branches_143 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_143_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 143)
      = (branches_143).map decodeBranch := by
  decide +kernel

private def branches_144 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,676⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,201⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,423⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,589⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,676⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,201⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,423⟩)),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,589⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,280⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,78⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,197⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,198⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,280⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,78⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,197⟩)),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,198⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,355⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,91⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,275⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,209⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,355⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,91⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,275⟩)),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,209⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,650⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,322⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,439⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,573⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨true,false,508⟩],(.bound ⟨true,false,650⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,222⟩,⟨false,true,254⟩,⟨false,true,508⟩],(.bound ⟨true,false,322⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨false,false,552⟩],(.bound ⟨true,false,439⟩)),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,222⟩,⟨true,false,254⟩,⟨true,true,552⟩],(.bound ⟨true,false,573⟩))
]

private theorem branches_144_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 144)
      = (branches_144).map decodeBranch := by
  decide +kernel

private def branches_145 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨false,false,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨true,false,433⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨true,true,222⟩,⟨false,true,296⟩,⟨false,true,433⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨false,false,453⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,613⟩,⟨true,false,621⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨false,false,613⟩,⟨false,true,621⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,613⟩,⟨false,false,682⟩],.automatic),
([⟨true,true,222⟩,⟨true,false,296⟩,⟨true,true,453⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic)
]

private theorem branches_145_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 145)
      = (branches_145).map decodeBranch := by
  decide +kernel

private def branches_146 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_146_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 146)
      = (branches_146).map decodeBranch := by
  decide +kernel

private def branches_147 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_147_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 147)
      = (branches_147).map decodeBranch := by
  decide +kernel

private def branches_148 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_148_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 148)
      = (branches_148).map decodeBranch := by
  decide +kernel

private def branches_149 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_149_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 149)
      = (branches_149).map decodeBranch := by
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
  if g = 133 then branches_133 else
  if g = 134 then branches_134 else
  if g = 135 then branches_135 else
  if g = 136 then branches_136 else
  if g = 137 then branches_137 else
  if g = 138 then branches_138 else
  if g = 139 then branches_139 else
  if g = 140 then branches_140 else
  if g = 141 then branches_141 else
  if g = 142 then branches_142 else
  if g = 143 then branches_143 else
  if g = 144 then branches_144 else
  if g = 145 then branches_145 else
  if g = 146 then branches_146 else
  if g = 147 then branches_147 else
  if g = 148 then branches_148 else
  if g = 149 then branches_149 else
  []

private theorem cb_133 : cachedBranches 133 = branches_133 := by
  norm_num [cachedBranches]

private theorem cb_134 : cachedBranches 134 = branches_134 := by
  norm_num [cachedBranches]

private theorem cb_135 : cachedBranches 135 = branches_135 := by
  norm_num [cachedBranches]

private theorem cb_136 : cachedBranches 136 = branches_136 := by
  norm_num [cachedBranches]

private theorem cb_137 : cachedBranches 137 = branches_137 := by
  norm_num [cachedBranches]

private theorem cb_138 : cachedBranches 138 = branches_138 := by
  norm_num [cachedBranches]

private theorem cb_139 : cachedBranches 139 = branches_139 := by
  norm_num [cachedBranches]

private theorem cb_140 : cachedBranches 140 = branches_140 := by
  norm_num [cachedBranches]

private theorem cb_141 : cachedBranches 141 = branches_141 := by
  norm_num [cachedBranches]

private theorem cb_142 : cachedBranches 142 = branches_142 := by
  norm_num [cachedBranches]

private theorem cb_143 : cachedBranches 143 = branches_143 := by
  norm_num [cachedBranches]

private theorem cb_144 : cachedBranches 144 = branches_144 := by
  norm_num [cachedBranches]

private theorem cb_145 : cachedBranches 145 = branches_145 := by
  norm_num [cachedBranches]

private theorem cb_146 : cachedBranches 146 = branches_146 := by
  norm_num [cachedBranches]

private theorem cb_147 : cachedBranches 147 = branches_147 := by
  norm_num [cachedBranches]

private theorem cb_148 : cachedBranches 148 = branches_148 := by
  norm_num [cachedBranches]

private theorem cb_149 : cachedBranches 149 = branches_149 := by
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

private def selectedGoals : List ℕ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]

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
    rcases hg with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
    · simpa only [hg, cb_133] using branches_133_eq
    · simpa only [hg, cb_134] using branches_134_eq
    · simpa only [hg, cb_135] using branches_135_eq
    · simpa only [hg, cb_136] using branches_136_eq
    · simpa only [hg, cb_137] using branches_137_eq
    · simpa only [hg, cb_138] using branches_138_eq
    · simpa only [hg, cb_139] using branches_139_eq
    · simpa only [hg, cb_140] using branches_140_eq
    · simpa only [hg, cb_141] using branches_141_eq
    · simpa only [hg, cb_142] using branches_142_eq
    · simpa only [hg, cb_143] using branches_143_eq
    · simpa only [hg, cb_144] using branches_144_eq
    · simpa only [hg, cb_145] using branches_145_eq
    · simpa only [hg, cb_146] using branches_146_eq
    · simpa only [hg, cb_147] using branches_147_eq
    · simpa only [hg, cb_148] using branches_148_eq
    · simpa only [hg, cb_149] using branches_149_eq
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
  ⟨133,4,[-1],406⟩,
  ⟨133,6,[-1],734⟩,
  ⟨133,7,[-1],1135⟩,
  ⟨133,12,[-1],739⟩,
  ⟨133,13,[-1],739⟩,
  ⟨133,14,[-1],739⟩,
  ⟨134,1,[-1],407⟩,
  ⟨134,2,[-1],739⟩,
  ⟨134,3,[-1],739⟩,
  ⟨134,7,[-1],739⟩,
  ⟨134,8,[-1],745⟩,
  ⟨134,9,[-1],745⟩,
  ⟨134,11,[-1],1137⟩,
  ⟨134,13,[-1],1138⟩,
  ⟨134,17,[-1],407⟩,
  ⟨134,18,[-1],739⟩
]

private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨134,19,[-1],739⟩,
  ⟨134,23,[-1],739⟩,
  ⟨134,24,[-1],744⟩,
  ⟨134,25,[-1],744⟩,
  ⟨134,27,[-1],1137⟩,
  ⟨134,29,[-1],1136⟩,
  ⟨136,0,[-1],424⟩,
  ⟨136,1,[-1],424⟩,
  ⟨136,2,[-1],424⟩,
  ⟨136,3,[-1],424⟩,
  ⟨136,4,[-1],424⟩,
  ⟨136,5,[-1],424⟩,
  ⟨136,6,[-1],424⟩,
  ⟨136,7,[-1],424⟩,
  ⟨136,8,[-1],450⟩,
  ⟨136,9,[-1],450⟩
]

private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨136,10,[-1],450⟩,
  ⟨136,11,[-1],450⟩,
  ⟨136,12,[-1],450⟩,
  ⟨136,13,[-1],450⟩,
  ⟨136,14,[-1],450⟩,
  ⟨136,15,[-1],450⟩,
  ⟨136,16,[-1],423⟩,
  ⟨136,17,[-1],423⟩,
  ⟨136,18,[-1],423⟩,
  ⟨136,19,[-1],423⟩,
  ⟨136,20,[-1],426⟩,
  ⟨136,21,[-1],426⟩,
  ⟨136,22,[-1],426⟩,
  ⟨136,23,[-1],426⟩,
  ⟨136,24,[-1],423⟩,
  ⟨136,25,[-1],423⟩
]

private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨136,26,[-1],423⟩,
  ⟨136,27,[-1],423⟩,
  ⟨136,28,[-1],443⟩,
  ⟨136,29,[-1],434⟩,
  ⟨136,30,[-1],438⟩,
  ⟨136,31,[-1],453⟩,
  ⟨136,32,[-1],424⟩,
  ⟨136,33,[-1],424⟩,
  ⟨136,34,[-1],424⟩,
  ⟨136,35,[-1],424⟩,
  ⟨136,36,[-1],424⟩,
  ⟨136,37,[-1],424⟩,
  ⟨136,38,[-1],424⟩,
  ⟨136,39,[-1],424⟩,
  ⟨136,40,[-1],450⟩,
  ⟨136,41,[-1],450⟩
]

private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨136,42,[-1],450⟩,
  ⟨136,43,[-1],450⟩,
  ⟨136,44,[-1],450⟩,
  ⟨136,45,[-1],450⟩,
  ⟨136,46,[-1],450⟩,
  ⟨136,47,[-1],450⟩,
  ⟨136,48,[-1],423⟩,
  ⟨136,49,[-1],423⟩,
  ⟨136,50,[-1],423⟩,
  ⟨136,51,[-1],423⟩,
  ⟨136,52,[-1],426⟩,
  ⟨136,53,[-1],426⟩,
  ⟨136,54,[-1],426⟩,
  ⟨136,55,[-1],426⟩,
  ⟨136,56,[-1],423⟩,
  ⟨136,57,[-1],423⟩
]

private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨136,58,[-1],423⟩,
  ⟨136,59,[-1],423⟩,
  ⟨136,60,[-1],443⟩,
  ⟨136,61,[-1],434⟩,
  ⟨136,62,[-1],438⟩,
  ⟨136,63,[-1],453⟩,
  ⟨137,0,[-1],224⟩,
  ⟨137,1,[-1],224⟩,
  ⟨137,2,[-1],224⟩,
  ⟨137,3,[-1],224⟩,
  ⟨137,4,[-1],799⟩,
  ⟨137,5,[-1],799⟩,
  ⟨137,6,[-1],799⟩,
  ⟨137,7,[-1],799⟩,
  ⟨137,8,[-1],929⟩,
  ⟨137,9,[-1],1121⟩
]

private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨137,10,[-1],1193⟩,
  ⟨137,11,[-1],669⟩,
  ⟨137,12,[-1],799⟩,
  ⟨137,13,[-1],799⟩,
  ⟨137,14,[-1],799⟩,
  ⟨137,15,[-1],799⟩,
  ⟨137,16,[-1],1175⟩,
  ⟨137,17,[-1],1175⟩,
  ⟨137,18,[-1],1175⟩,
  ⟨137,19,[-1],1175⟩,
  ⟨137,20,[-1],1175⟩,
  ⟨137,21,[-1],1175⟩,
  ⟨137,22,[-1],1175⟩,
  ⟨137,23,[-1],1175⟩,
  ⟨137,24,[-1],997⟩,
  ⟨137,25,[-1],997⟩
]

private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨137,26,[-1],997⟩,
  ⟨137,27,[-1],997⟩,
  ⟨137,28,[-1],997⟩,
  ⟨137,29,[-1],997⟩,
  ⟨137,30,[-1],997⟩,
  ⟨137,31,[-1],997⟩,
  ⟨137,32,[-1],224⟩,
  ⟨137,33,[-1],224⟩,
  ⟨137,34,[-1],224⟩,
  ⟨137,35,[-1],224⟩,
  ⟨137,36,[-1],799⟩,
  ⟨137,37,[-1],799⟩,
  ⟨137,38,[-1],799⟩,
  ⟨137,39,[-1],799⟩,
  ⟨137,40,[-1],929⟩,
  ⟨137,41,[-1],1121⟩
]

private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨137,42,[-1],1193⟩,
  ⟨137,43,[-1],669⟩,
  ⟨137,44,[-1],799⟩,
  ⟨137,45,[-1],799⟩,
  ⟨137,46,[-1],799⟩,
  ⟨137,47,[-1],799⟩,
  ⟨137,48,[-1],1175⟩,
  ⟨137,49,[-1],1175⟩,
  ⟨137,50,[-1],1175⟩,
  ⟨137,51,[-1],1175⟩,
  ⟨137,52,[-1],1175⟩,
  ⟨137,53,[-1],1175⟩,
  ⟨137,54,[-1],1175⟩,
  ⟨137,55,[-1],1175⟩,
  ⟨137,56,[-1],997⟩,
  ⟨137,57,[-1],997⟩
]

private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨137,58,[-1],997⟩,
  ⟨137,59,[-1],997⟩,
  ⟨137,60,[-1],997⟩,
  ⟨137,61,[-1],997⟩,
  ⟨137,62,[-1],997⟩,
  ⟨137,63,[-1],997⟩,
  ⟨139,0,[-1],419⟩,
  ⟨139,1,[-1],451⟩,
  ⟨139,2,[-1],427⟩,
  ⟨139,3,[-1],454⟩,
  ⟨139,4,[-1],419⟩,
  ⟨139,5,[-1],451⟩,
  ⟨139,6,[-1],436⟩,
  ⟨139,7,[-1],433⟩,
  ⟨139,8,[-1],419⟩,
  ⟨139,9,[-1],451⟩
]

private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨139,10,[-1],427⟩,
  ⟨139,11,[-1],432⟩,
  ⟨139,12,[-1],419⟩,
  ⟨139,13,[-1],451⟩,
  ⟨139,14,[-1],427⟩,
  ⟨139,15,[-1],447⟩,
  ⟨140,0,[-1],414⟩,
  ⟨140,1,[-1],441⟩,
  ⟨140,2,[-1],468⟩,
  ⟨140,3,[-1],468⟩,
  ⟨140,4,[-1],414⟩,
  ⟨140,5,[-1],441⟩,
  ⟨140,6,[-1],905⟩,
  ⟨140,7,[-1],614⟩,
  ⟨140,8,[-1],716⟩,
  ⟨140,9,[-1],720⟩
]

private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨140,10,[-1],719⟩,
  ⟨140,11,[-1],719⟩,
  ⟨140,12,[-1],1163⟩,
  ⟨140,13,[-1],1165⟩,
  ⟨140,14,[-1],1164⟩,
  ⟨140,15,[-1],1164⟩,
  ⟨142,0,[-1],416⟩,
  ⟨142,1,[-1],455⟩,
  ⟨142,2,[-1],420⟩,
  ⟨142,3,[-1],456⟩,
  ⟨142,4,[-1],416⟩,
  ⟨142,5,[-1],455⟩,
  ⟨142,6,[-1],429⟩,
  ⟨142,7,[-1],439⟩,
  ⟨142,8,[-1],416⟩,
  ⟨142,9,[-1],455⟩
]

private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨142,10,[-1],420⟩,
  ⟨142,11,[-1],428⟩,
  ⟨142,12,[-1],416⟩,
  ⟨142,13,[-1],455⟩,
  ⟨142,14,[-1],420⟩,
  ⟨142,15,[-1],448⟩,
  ⟨143,0,[-1],8⟩,
  ⟨143,1,[-1],8⟩,
  ⟨143,2,[-1],8⟩,
  ⟨143,3,[-1],8⟩,
  ⟨143,4,[-1],592⟩,
  ⟨143,5,[-1],705⟩,
  ⟨143,6,[-1],599⟩,
  ⟨143,7,[-1],1002⟩,
  ⟨143,8,[-1],763⟩,
  ⟨143,9,[-1],763⟩
]

private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨143,10,[-1],763⟩,
  ⟨143,11,[-1],763⟩,
  ⟨143,12,[-1],687⟩,
  ⟨143,13,[-1],687⟩,
  ⟨143,14,[-1],687⟩,
  ⟨143,15,[-1],687⟩,
  ⟨144,0,[-1],415⟩,
  ⟨144,1,[-1],444⟩,
  ⟨144,2,[-1],425⟩,
  ⟨144,3,[-1],417⟩,
  ⟨144,4,[-1],415⟩,
  ⟨144,5,[-1],444⟩,
  ⟨144,6,[-1],425⟩,
  ⟨144,7,[-1],446⟩,
  ⟨144,8,[-1],415⟩,
  ⟨144,9,[-1],444⟩
]

private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨144,10,[-1],425⟩,
  ⟨144,11,[-1],417⟩,
  ⟨144,12,[-1],415⟩,
  ⟨144,13,[-1],444⟩,
  ⟨144,14,[-1],425⟩,
  ⟨144,15,[-1],431⟩,
  ⟨144,16,[-1],415⟩,
  ⟨144,17,[-1],444⟩,
  ⟨144,18,[-1],425⟩,
  ⟨144,19,[-1],417⟩,
  ⟨144,20,[-1],415⟩,
  ⟨144,21,[-1],444⟩,
  ⟨144,22,[-1],425⟩,
  ⟨144,23,[-1],435⟩,
  ⟨144,24,[-1],1106⟩,
  ⟨144,25,[-1],1111⟩
]

private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨144,26,[-1],1109⟩,
  ⟨144,27,[-1],1107⟩,
  ⟨144,28,[-1],1106⟩,
  ⟨144,29,[-1],1111⟩,
  ⟨144,30,[-1],1109⟩,
  ⟨144,31,[-1],1113⟩,
  ⟨146,0,[-1],418⟩,
  ⟨146,1,[-1],445⟩,
  ⟨146,2,[-1],417⟩,
  ⟨146,3,[-1],417⟩,
  ⟨146,4,[-1],418⟩,
  ⟨146,5,[-1],445⟩,
  ⟨146,6,[-1],417⟩,
  ⟨146,7,[-1],417⟩,
  ⟨146,8,[-1],418⟩,
  ⟨146,9,[-1],445⟩
]

private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨146,10,[-1],417⟩,
  ⟨146,11,[-1],417⟩,
  ⟨146,12,[-1],418⟩,
  ⟨146,13,[-1],445⟩,
  ⟨146,14,[-1],417⟩,
  ⟨146,15,[-1],417⟩,
  ⟨146,16,[-1],418⟩,
  ⟨146,17,[-1],445⟩,
  ⟨146,18,[-1],417⟩,
  ⟨146,19,[-1],417⟩,
  ⟨146,20,[-1],418⟩,
  ⟨146,21,[-1],445⟩,
  ⟨146,22,[-1],417⟩,
  ⟨146,23,[-1],417⟩,
  ⟨146,24,[-1],418⟩,
  ⟨146,25,[-1],445⟩
]

private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨146,26,[-1],417⟩,
  ⟨146,27,[-1],417⟩,
  ⟨146,28,[-1],418⟩,
  ⟨146,29,[-1],445⟩,
  ⟨146,30,[-1],417⟩,
  ⟨146,31,[-1],417⟩,
  ⟨146,32,[-1],418⟩,
  ⟨146,33,[-1],445⟩,
  ⟨146,34,[-1],422⟩,
  ⟨146,35,[-1],452⟩,
  ⟨146,36,[-1],418⟩,
  ⟨146,37,[-1],445⟩,
  ⟨146,38,[-1],422⟩,
  ⟨146,39,[-1],452⟩,
  ⟨146,40,[-1],418⟩,
  ⟨146,41,[-1],445⟩
]

private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨146,42,[-1],422⟩,
  ⟨146,43,[-1],437⟩,
  ⟨146,44,[-1],418⟩,
  ⟨146,45,[-1],445⟩,
  ⟨146,46,[-1],422⟩,
  ⟨146,47,[-1],437⟩,
  ⟨146,48,[-1],418⟩,
  ⟨146,49,[-1],445⟩,
  ⟨146,50,[-1],422⟩,
  ⟨146,51,[-1],440⟩,
  ⟨146,52,[-1],418⟩,
  ⟨146,53,[-1],445⟩,
  ⟨146,54,[-1],422⟩,
  ⟨146,55,[-1],440⟩,
  ⟨146,56,[-1],418⟩,
  ⟨146,57,[-1],445⟩
]

private theorem refs_valid_18 : ∀ rec ∈ chunk_18, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨146,58,[-1],422⟩,
  ⟨146,59,[-1],442⟩,
  ⟨146,60,[-1],418⟩,
  ⟨146,61,[-1],445⟩,
  ⟨146,62,[-1],422⟩,
  ⟨146,63,[-1],442⟩,
  ⟨148,0,[-1],1123⟩,
  ⟨148,1,[-1],1177⟩,
  ⟨148,2,[-1],1012⟩,
  ⟨148,3,[-1],899⟩,
  ⟨148,4,[-1],664⟩,
  ⟨148,5,[-1],1018⟩,
  ⟨148,6,[-1],1115⟩,
  ⟨148,7,[-1],1118⟩,
  ⟨148,8,[-1],754⟩,
  ⟨148,9,[-1],758⟩
]

private theorem refs_valid_19 : ∀ rec ∈ chunk_19, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨148,10,[-1],755⟩,
  ⟨148,11,[-1],755⟩,
  ⟨148,12,[-1],1146⟩,
  ⟨148,13,[-1],1148⟩,
  ⟨148,14,[-1],1146⟩,
  ⟨148,15,[-1],1146⟩,
  ⟨149,8,[-1],457⟩,
  ⟨149,9,[-1],430⟩,
  ⟨149,10,[-1],756⟩,
  ⟨149,11,[-1],1153⟩
]

private theorem refs_valid_20 : ∀ rec ∈ chunk_20, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def selectedRecords : List MiddleCertRecord := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20].flatten

private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by
  decide +kernel

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([8] : List ℕ)))
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end RetRow8

open RetRow8

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([8] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)

#print axioms solution
