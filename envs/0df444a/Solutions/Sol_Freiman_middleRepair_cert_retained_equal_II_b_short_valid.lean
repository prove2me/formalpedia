-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_equal_II_b_short_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:55:29.570099+00:00
-- url     : https://prove2.me/submissions/ae1bf8c0-f9c6-4dad-9aff-14d35c826207

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

namespace RetRow7

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

private def branches_118 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,800⟩)),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,778⟩)),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,765⟩)),
([⟨false,false,633⟩,⟨true,false,603⟩,⟨true,true,613⟩,⟨true,true,682⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,613⟩,⟨true,false,621⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,613⟩,⟨false,true,621⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,613⟩,⟨false,false,682⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,613⟩,⟨true,true,682⟩],.impossible),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,740⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,692⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,75⟩)),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,580⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,756⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,735⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,727⟩)),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,763⟩))
]

private theorem branches_118_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 118)
      = (branches_118).map decodeBranch := by
  decide +kernel

private def branches_119 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_119_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 119)
      = (branches_119).map decodeBranch := by
  decide +kernel

private def branches_120 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_120_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 120)
      = (branches_120).map decodeBranch := by
  decide +kernel

private def branches_121 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_121_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 121)
      = (branches_121).map decodeBranch := by
  decide +kernel

private def branches_122 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_122_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 122)
      = (branches_122).map decodeBranch := by
  decide +kernel

private def branches_123 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_123_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 123)
      = (branches_123).map decodeBranch := by
  decide +kernel

private def branches_124 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_124_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 124)
      = (branches_124).map decodeBranch := by
  decide +kernel

private def branches_125 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_125_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 125)
      = (branches_125).map decodeBranch := by
  decide +kernel

private def branches_126 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_126_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 126)
      = (branches_126).map decodeBranch := by
  decide +kernel

private def branches_127 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_127_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 127)
      = (branches_127).map decodeBranch := by
  decide +kernel

private def branches_128 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_128_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 128)
      = (branches_128).map decodeBranch := by
  decide +kernel

private def branches_129 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_129_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 129)
      = (branches_129).map decodeBranch := by
  decide +kernel

private def branches_130 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_130_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 130)
      = (branches_130).map decodeBranch := by
  decide +kernel

private def branches_131 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_131_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 131)
      = (branches_131).map decodeBranch := by
  decide +kernel

private def branches_132 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_132_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 132)
      = (branches_132).map decodeBranch := by
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
  if g = 118 then branches_118 else
  if g = 119 then branches_119 else
  if g = 120 then branches_120 else
  if g = 121 then branches_121 else
  if g = 122 then branches_122 else
  if g = 123 then branches_123 else
  if g = 124 then branches_124 else
  if g = 125 then branches_125 else
  if g = 126 then branches_126 else
  if g = 127 then branches_127 else
  if g = 128 then branches_128 else
  if g = 129 then branches_129 else
  if g = 130 then branches_130 else
  if g = 131 then branches_131 else
  if g = 132 then branches_132 else
  []

private theorem cb_118 : cachedBranches 118 = branches_118 := by
  norm_num [cachedBranches]

private theorem cb_119 : cachedBranches 119 = branches_119 := by
  norm_num [cachedBranches]

private theorem cb_120 : cachedBranches 120 = branches_120 := by
  norm_num [cachedBranches]

private theorem cb_121 : cachedBranches 121 = branches_121 := by
  norm_num [cachedBranches]

private theorem cb_122 : cachedBranches 122 = branches_122 := by
  norm_num [cachedBranches]

private theorem cb_123 : cachedBranches 123 = branches_123 := by
  norm_num [cachedBranches]

private theorem cb_124 : cachedBranches 124 = branches_124 := by
  norm_num [cachedBranches]

private theorem cb_125 : cachedBranches 125 = branches_125 := by
  norm_num [cachedBranches]

private theorem cb_126 : cachedBranches 126 = branches_126 := by
  norm_num [cachedBranches]

private theorem cb_127 : cachedBranches 127 = branches_127 := by
  norm_num [cachedBranches]

private theorem cb_128 : cachedBranches 128 = branches_128 := by
  norm_num [cachedBranches]

private theorem cb_129 : cachedBranches 129 = branches_129 := by
  norm_num [cachedBranches]

private theorem cb_130 : cachedBranches 130 = branches_130 := by
  norm_num [cachedBranches]

private theorem cb_131 : cachedBranches 131 = branches_131 := by
  norm_num [cachedBranches]

private theorem cb_132 : cachedBranches 132 = branches_132 := by
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

private def selectedGoals : List ℕ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]

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
    · simpa only [hg, cb_118] using branches_118_eq
    · simpa only [hg, cb_119] using branches_119_eq
    · simpa only [hg, cb_120] using branches_120_eq
    · simpa only [hg, cb_121] using branches_121_eq
    · simpa only [hg, cb_122] using branches_122_eq
    · simpa only [hg, cb_123] using branches_123_eq
    · simpa only [hg, cb_124] using branches_124_eq
    · simpa only [hg, cb_125] using branches_125_eq
    · simpa only [hg, cb_126] using branches_126_eq
    · simpa only [hg, cb_127] using branches_127_eq
    · simpa only [hg, cb_128] using branches_128_eq
    · simpa only [hg, cb_129] using branches_129_eq
    · simpa only [hg, cb_130] using branches_130_eq
    · simpa only [hg, cb_131] using branches_131_eq
    · simpa only [hg, cb_132] using branches_132_eq
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
  ⟨118,0,[-1],421⟩,
  ⟨118,1,[-1],803⟩,
  ⟨118,2,[-1],1096⟩,
  ⟨118,4,[-1],395⟩,
  ⟨118,5,[-1],395⟩,
  ⟨118,6,[-1],395⟩,
  ⟨118,7,[-1],395⟩,
  ⟨118,8,[-1],739⟩,
  ⟨118,9,[-1],739⟩,
  ⟨118,10,[-1],739⟩,
  ⟨118,11,[-1],739⟩,
  ⟨118,12,[-1],739⟩,
  ⟨118,13,[-1],739⟩,
  ⟨118,14,[-1],739⟩,
  ⟨118,15,[-1],739⟩,
  ⟨119,1,[-1],407⟩
]

private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨119,2,[-1],739⟩,
  ⟨119,3,[-1],739⟩,
  ⟨119,7,[-1],739⟩,
  ⟨119,8,[-1],745⟩,
  ⟨119,9,[-1],745⟩,
  ⟨119,11,[-1],1137⟩,
  ⟨119,13,[-1],1138⟩,
  ⟨119,17,[-1],407⟩,
  ⟨119,18,[-1],739⟩,
  ⟨119,19,[-1],739⟩,
  ⟨119,23,[-1],739⟩,
  ⟨119,24,[-1],744⟩,
  ⟨119,25,[-1],744⟩,
  ⟨119,27,[-1],1137⟩,
  ⟨119,29,[-1],1136⟩,
  ⟨121,0,[-1],359⟩
]

private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨121,1,[-1],359⟩,
  ⟨121,2,[-1],359⟩,
  ⟨121,3,[-1],359⟩,
  ⟨121,4,[-1],359⟩,
  ⟨121,5,[-1],359⟩,
  ⟨121,6,[-1],359⟩,
  ⟨121,7,[-1],359⟩,
  ⟨121,8,[-1],396⟩,
  ⟨121,9,[-1],396⟩,
  ⟨121,10,[-1],396⟩,
  ⟨121,11,[-1],396⟩,
  ⟨121,12,[-1],396⟩,
  ⟨121,13,[-1],396⟩,
  ⟨121,14,[-1],396⟩,
  ⟨121,15,[-1],396⟩,
  ⟨121,16,[-1],356⟩
]

private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨121,17,[-1],356⟩,
  ⟨121,18,[-1],356⟩,
  ⟨121,19,[-1],356⟩,
  ⟨121,20,[-1],361⟩,
  ⟨121,21,[-1],361⟩,
  ⟨121,22,[-1],361⟩,
  ⟨121,23,[-1],361⟩,
  ⟨121,24,[-1],356⟩,
  ⟨121,25,[-1],356⟩,
  ⟨121,26,[-1],356⟩,
  ⟨121,27,[-1],356⟩,
  ⟨121,28,[-1],385⟩,
  ⟨121,29,[-1],370⟩,
  ⟨121,30,[-1],375⟩,
  ⟨121,31,[-1],400⟩,
  ⟨121,32,[-1],359⟩
]

private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨121,33,[-1],359⟩,
  ⟨121,34,[-1],359⟩,
  ⟨121,35,[-1],359⟩,
  ⟨121,36,[-1],359⟩,
  ⟨121,37,[-1],359⟩,
  ⟨121,38,[-1],359⟩,
  ⟨121,39,[-1],359⟩,
  ⟨121,40,[-1],396⟩,
  ⟨121,41,[-1],396⟩,
  ⟨121,42,[-1],396⟩,
  ⟨121,43,[-1],396⟩,
  ⟨121,44,[-1],396⟩,
  ⟨121,45,[-1],396⟩,
  ⟨121,46,[-1],396⟩,
  ⟨121,47,[-1],396⟩,
  ⟨121,48,[-1],356⟩
]

private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨121,49,[-1],356⟩,
  ⟨121,50,[-1],356⟩,
  ⟨121,51,[-1],356⟩,
  ⟨121,52,[-1],361⟩,
  ⟨121,53,[-1],361⟩,
  ⟨121,54,[-1],361⟩,
  ⟨121,55,[-1],361⟩,
  ⟨121,56,[-1],356⟩,
  ⟨121,57,[-1],356⟩,
  ⟨121,58,[-1],356⟩,
  ⟨121,59,[-1],356⟩,
  ⟨121,60,[-1],385⟩,
  ⟨121,61,[-1],370⟩,
  ⟨121,62,[-1],375⟩,
  ⟨121,63,[-1],400⟩,
  ⟨122,0,[-1],224⟩
]

private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨122,1,[-1],224⟩,
  ⟨122,2,[-1],224⟩,
  ⟨122,3,[-1],224⟩,
  ⟨122,4,[-1],799⟩,
  ⟨122,5,[-1],799⟩,
  ⟨122,6,[-1],799⟩,
  ⟨122,7,[-1],799⟩,
  ⟨122,8,[-1],929⟩,
  ⟨122,9,[-1],1121⟩,
  ⟨122,10,[-1],1193⟩,
  ⟨122,11,[-1],669⟩,
  ⟨122,12,[-1],799⟩,
  ⟨122,13,[-1],799⟩,
  ⟨122,14,[-1],799⟩,
  ⟨122,15,[-1],799⟩,
  ⟨122,16,[-1],1175⟩
]

private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨122,17,[-1],1175⟩,
  ⟨122,18,[-1],1175⟩,
  ⟨122,19,[-1],1175⟩,
  ⟨122,20,[-1],1175⟩,
  ⟨122,21,[-1],1175⟩,
  ⟨122,22,[-1],1175⟩,
  ⟨122,23,[-1],1175⟩,
  ⟨122,24,[-1],997⟩,
  ⟨122,25,[-1],997⟩,
  ⟨122,26,[-1],997⟩,
  ⟨122,27,[-1],997⟩,
  ⟨122,28,[-1],997⟩,
  ⟨122,29,[-1],997⟩,
  ⟨122,30,[-1],997⟩,
  ⟨122,31,[-1],997⟩,
  ⟨122,32,[-1],224⟩
]

private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨122,33,[-1],224⟩,
  ⟨122,34,[-1],224⟩,
  ⟨122,35,[-1],224⟩,
  ⟨122,36,[-1],799⟩,
  ⟨122,37,[-1],799⟩,
  ⟨122,38,[-1],799⟩,
  ⟨122,39,[-1],799⟩,
  ⟨122,40,[-1],929⟩,
  ⟨122,41,[-1],1121⟩,
  ⟨122,42,[-1],1193⟩,
  ⟨122,43,[-1],669⟩,
  ⟨122,44,[-1],799⟩,
  ⟨122,45,[-1],799⟩,
  ⟨122,46,[-1],799⟩,
  ⟨122,47,[-1],799⟩,
  ⟨122,48,[-1],1175⟩
]

private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨122,49,[-1],1175⟩,
  ⟨122,50,[-1],1175⟩,
  ⟨122,51,[-1],1175⟩,
  ⟨122,52,[-1],1175⟩,
  ⟨122,53,[-1],1175⟩,
  ⟨122,54,[-1],1175⟩,
  ⟨122,55,[-1],1175⟩,
  ⟨122,56,[-1],997⟩,
  ⟨122,57,[-1],997⟩,
  ⟨122,58,[-1],997⟩,
  ⟨122,59,[-1],997⟩,
  ⟨122,60,[-1],997⟩,
  ⟨122,61,[-1],997⟩,
  ⟨122,62,[-1],997⟩,
  ⟨122,63,[-1],997⟩,
  ⟨124,0,[-1],348⟩
]

private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨124,1,[-1],397⟩,
  ⟨124,2,[-1],362⟩,
  ⟨124,3,[-1],402⟩,
  ⟨124,4,[-1],348⟩,
  ⟨124,5,[-1],397⟩,
  ⟨124,6,[-1],373⟩,
  ⟨124,7,[-1],368⟩,
  ⟨124,8,[-1],348⟩,
  ⟨124,9,[-1],397⟩,
  ⟨124,10,[-1],362⟩,
  ⟨124,11,[-1],367⟩,
  ⟨124,12,[-1],348⟩,
  ⟨124,13,[-1],397⟩,
  ⟨124,14,[-1],362⟩,
  ⟨124,15,[-1],392⟩,
  ⟨125,0,[-1],414⟩
]

private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨125,1,[-1],380⟩,
  ⟨125,2,[-1],468⟩,
  ⟨125,3,[-1],468⟩,
  ⟨125,4,[-1],414⟩,
  ⟨125,5,[-1],380⟩,
  ⟨125,6,[-1],905⟩,
  ⟨125,7,[-1],614⟩,
  ⟨125,8,[-1],716⟩,
  ⟨125,9,[-1],720⟩,
  ⟨125,10,[-1],719⟩,
  ⟨125,11,[-1],719⟩,
  ⟨125,12,[-1],1163⟩,
  ⟨125,13,[-1],1165⟩,
  ⟨125,14,[-1],1164⟩,
  ⟨125,15,[-1],1164⟩,
  ⟨127,0,[-1],345⟩
]

private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨127,1,[-1],403⟩,
  ⟨127,2,[-1],350⟩,
  ⟨127,3,[-1],404⟩,
  ⟨127,4,[-1],345⟩,
  ⟨127,5,[-1],403⟩,
  ⟨127,6,[-1],364⟩,
  ⟨127,7,[-1],377⟩,
  ⟨127,8,[-1],345⟩,
  ⟨127,9,[-1],403⟩,
  ⟨127,10,[-1],350⟩,
  ⟨127,11,[-1],363⟩,
  ⟨127,12,[-1],345⟩,
  ⟨127,13,[-1],403⟩,
  ⟨127,14,[-1],350⟩,
  ⟨127,15,[-1],393⟩,
  ⟨128,0,[-1],8⟩
]

private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨128,1,[-1],8⟩,
  ⟨128,2,[-1],8⟩,
  ⟨128,3,[-1],8⟩,
  ⟨128,4,[-1],592⟩,
  ⟨128,5,[-1],705⟩,
  ⟨128,6,[-1],599⟩,
  ⟨128,7,[-1],1002⟩,
  ⟨128,8,[-1],763⟩,
  ⟨128,9,[-1],763⟩,
  ⟨128,10,[-1],763⟩,
  ⟨128,11,[-1],763⟩,
  ⟨128,12,[-1],687⟩,
  ⟨128,13,[-1],687⟩,
  ⟨128,14,[-1],687⟩,
  ⟨128,15,[-1],687⟩,
  ⟨129,0,[-1],344⟩
]

private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨129,1,[-1],387⟩,
  ⟨129,2,[-1],360⟩,
  ⟨129,3,[-1],346⟩,
  ⟨129,4,[-1],344⟩,
  ⟨129,5,[-1],387⟩,
  ⟨129,6,[-1],360⟩,
  ⟨129,7,[-1],391⟩,
  ⟨129,8,[-1],344⟩,
  ⟨129,9,[-1],387⟩,
  ⟨129,10,[-1],360⟩,
  ⟨129,11,[-1],346⟩,
  ⟨129,12,[-1],344⟩,
  ⟨129,13,[-1],387⟩,
  ⟨129,14,[-1],360⟩,
  ⟨129,15,[-1],366⟩,
  ⟨129,16,[-1],344⟩
]

private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨129,17,[-1],387⟩,
  ⟨129,18,[-1],360⟩,
  ⟨129,19,[-1],346⟩,
  ⟨129,20,[-1],344⟩,
  ⟨129,21,[-1],387⟩,
  ⟨129,22,[-1],360⟩,
  ⟨129,23,[-1],371⟩,
  ⟨129,24,[-1],344⟩,
  ⟨129,25,[-1],387⟩,
  ⟨129,26,[-1],360⟩,
  ⟨129,27,[-1],346⟩,
  ⟨129,28,[-1],344⟩,
  ⟨129,29,[-1],387⟩,
  ⟨129,30,[-1],360⟩,
  ⟨129,31,[-1],394⟩,
  ⟨131,0,[-1],347⟩
]

private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨131,1,[-1],389⟩,
  ⟨131,2,[-1],346⟩,
  ⟨131,3,[-1],346⟩,
  ⟨131,4,[-1],347⟩,
  ⟨131,5,[-1],389⟩,
  ⟨131,6,[-1],346⟩,
  ⟨131,7,[-1],346⟩,
  ⟨131,8,[-1],347⟩,
  ⟨131,9,[-1],389⟩,
  ⟨131,10,[-1],346⟩,
  ⟨131,11,[-1],346⟩,
  ⟨131,12,[-1],347⟩,
  ⟨131,13,[-1],389⟩,
  ⟨131,14,[-1],346⟩,
  ⟨131,15,[-1],346⟩,
  ⟨131,16,[-1],347⟩
]

private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨131,17,[-1],389⟩,
  ⟨131,18,[-1],346⟩,
  ⟨131,19,[-1],346⟩,
  ⟨131,20,[-1],347⟩,
  ⟨131,21,[-1],389⟩,
  ⟨131,22,[-1],346⟩,
  ⟨131,23,[-1],346⟩,
  ⟨131,24,[-1],347⟩,
  ⟨131,25,[-1],389⟩,
  ⟨131,26,[-1],346⟩,
  ⟨131,27,[-1],346⟩,
  ⟨131,28,[-1],347⟩,
  ⟨131,29,[-1],389⟩,
  ⟨131,30,[-1],346⟩,
  ⟨131,31,[-1],346⟩,
  ⟨131,32,[-1],347⟩
]

private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨131,33,[-1],389⟩,
  ⟨131,34,[-1],354⟩,
  ⟨131,35,[-1],398⟩,
  ⟨131,36,[-1],347⟩,
  ⟨131,37,[-1],389⟩,
  ⟨131,38,[-1],354⟩,
  ⟨131,39,[-1],398⟩,
  ⟨131,40,[-1],347⟩,
  ⟨131,41,[-1],389⟩,
  ⟨131,42,[-1],354⟩,
  ⟨131,43,[-1],374⟩,
  ⟨131,44,[-1],347⟩,
  ⟨131,45,[-1],389⟩,
  ⟨131,46,[-1],354⟩,
  ⟨131,47,[-1],374⟩,
  ⟨131,48,[-1],347⟩
]

private theorem refs_valid_18 : ∀ rec ∈ chunk_18, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨131,49,[-1],389⟩,
  ⟨131,50,[-1],354⟩,
  ⟨131,51,[-1],378⟩,
  ⟨131,52,[-1],347⟩,
  ⟨131,53,[-1],389⟩,
  ⟨131,54,[-1],354⟩,
  ⟨131,55,[-1],378⟩,
  ⟨131,56,[-1],347⟩,
  ⟨131,57,[-1],389⟩,
  ⟨131,58,[-1],354⟩,
  ⟨131,59,[-1],382⟩,
  ⟨131,60,[-1],347⟩,
  ⟨131,61,[-1],389⟩,
  ⟨131,62,[-1],354⟩,
  ⟨131,63,[-1],382⟩
]

private theorem refs_valid_19 : ∀ rec ∈ chunk_19, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def selectedRecords : List MiddleCertRecord := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19].flatten

private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by
  decide +kernel

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([7] : List ℕ)))
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end RetRow7

open RetRow7

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([7] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)

#print axioms solution
