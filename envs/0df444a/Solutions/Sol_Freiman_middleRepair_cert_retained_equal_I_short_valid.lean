-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_equal_I_short_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T17:06:11.087745+00:00
-- url     : https://prove2.me/submissions/0cd2dff0-16e4-4e03-998f-ebcb5a311b74

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

namespace RetRow3

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

private def branches_41 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_41_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 41)
      = (branches_41).map decodeBranch := by
  decide +kernel

private def branches_42 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_42_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 42)
      = (branches_42).map decodeBranch := by
  decide +kernel

private def branches_43 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_43_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 43)
      = (branches_43).map decodeBranch := by
  decide +kernel

private def branches_44 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_44_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 44)
      = (branches_44).map decodeBranch := by
  decide +kernel

private def branches_45 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_45_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 45)
      = (branches_45).map decodeBranch := by
  decide +kernel

private def branches_46 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_46_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 46)
      = (branches_46).map decodeBranch := by
  decide +kernel

private def branches_47 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_47_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 47)
      = (branches_47).map decodeBranch := by
  decide +kernel

private def branches_48 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_48_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 48)
      = (branches_48).map decodeBranch := by
  decide +kernel

private def branches_49 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_49_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 49)
      = (branches_49).map decodeBranch := by
  decide +kernel

private def branches_50 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_50_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 50)
      = (branches_50).map decodeBranch := by
  decide +kernel

private def branches_51 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_51_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 51)
      = (branches_51).map decodeBranch := by
  decide +kernel

private def branches_52 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_52_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 52)
      = (branches_52).map decodeBranch := by
  decide +kernel

private def branches_53 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_53_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 53)
      = (branches_53).map decodeBranch := by
  decide +kernel

private def branches_54 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_54_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 54)
      = (branches_54).map decodeBranch := by
  decide +kernel

private def branches_55 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_55_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 55)
      = (branches_55).map decodeBranch := by
  decide +kernel

private def branches_56 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_56_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 56)
      = (branches_56).map decodeBranch := by
  decide +kernel

private def branches_57 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_57_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 57)
      = (branches_57).map decodeBranch := by
  decide +kernel

private def branches_58 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_58_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 58)
      = (branches_58).map decodeBranch := by
  decide +kernel

private def branches_59 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_59_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 59)
      = (branches_59).map decodeBranch := by
  decide +kernel

private def branches_60 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_60_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 60)
      = (branches_60).map decodeBranch := by
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
  if g = 41 then branches_41 else
  if g = 42 then branches_42 else
  if g = 43 then branches_43 else
  if g = 44 then branches_44 else
  if g = 45 then branches_45 else
  if g = 46 then branches_46 else
  if g = 47 then branches_47 else
  if g = 48 then branches_48 else
  if g = 49 then branches_49 else
  if g = 50 then branches_50 else
  if g = 51 then branches_51 else
  if g = 52 then branches_52 else
  if g = 53 then branches_53 else
  if g = 54 then branches_54 else
  if g = 55 then branches_55 else
  if g = 56 then branches_56 else
  if g = 57 then branches_57 else
  if g = 58 then branches_58 else
  if g = 59 then branches_59 else
  if g = 60 then branches_60 else
  []

private theorem cb_41 : cachedBranches 41 = branches_41 := by
  norm_num [cachedBranches]

private theorem cb_42 : cachedBranches 42 = branches_42 := by
  norm_num [cachedBranches]

private theorem cb_43 : cachedBranches 43 = branches_43 := by
  norm_num [cachedBranches]

private theorem cb_44 : cachedBranches 44 = branches_44 := by
  norm_num [cachedBranches]

private theorem cb_45 : cachedBranches 45 = branches_45 := by
  norm_num [cachedBranches]

private theorem cb_46 : cachedBranches 46 = branches_46 := by
  norm_num [cachedBranches]

private theorem cb_47 : cachedBranches 47 = branches_47 := by
  norm_num [cachedBranches]

private theorem cb_48 : cachedBranches 48 = branches_48 := by
  norm_num [cachedBranches]

private theorem cb_49 : cachedBranches 49 = branches_49 := by
  norm_num [cachedBranches]

private theorem cb_50 : cachedBranches 50 = branches_50 := by
  norm_num [cachedBranches]

private theorem cb_51 : cachedBranches 51 = branches_51 := by
  norm_num [cachedBranches]

private theorem cb_52 : cachedBranches 52 = branches_52 := by
  norm_num [cachedBranches]

private theorem cb_53 : cachedBranches 53 = branches_53 := by
  norm_num [cachedBranches]

private theorem cb_54 : cachedBranches 54 = branches_54 := by
  norm_num [cachedBranches]

private theorem cb_55 : cachedBranches 55 = branches_55 := by
  norm_num [cachedBranches]

private theorem cb_56 : cachedBranches 56 = branches_56 := by
  norm_num [cachedBranches]

private theorem cb_57 : cachedBranches 57 = branches_57 := by
  norm_num [cachedBranches]

private theorem cb_58 : cachedBranches 58 = branches_58 := by
  norm_num [cachedBranches]

private theorem cb_59 : cachedBranches 59 = branches_59 := by
  norm_num [cachedBranches]

private theorem cb_60 : cachedBranches 60 = branches_60 := by
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

private def selectedGoals : List ℕ := [41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]

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
    rcases hg with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
    · simpa only [hg, cb_41] using branches_41_eq
    · simpa only [hg, cb_42] using branches_42_eq
    · simpa only [hg, cb_43] using branches_43_eq
    · simpa only [hg, cb_44] using branches_44_eq
    · simpa only [hg, cb_45] using branches_45_eq
    · simpa only [hg, cb_46] using branches_46_eq
    · simpa only [hg, cb_47] using branches_47_eq
    · simpa only [hg, cb_48] using branches_48_eq
    · simpa only [hg, cb_49] using branches_49_eq
    · simpa only [hg, cb_50] using branches_50_eq
    · simpa only [hg, cb_51] using branches_51_eq
    · simpa only [hg, cb_52] using branches_52_eq
    · simpa only [hg, cb_53] using branches_53_eq
    · simpa only [hg, cb_54] using branches_54_eq
    · simpa only [hg, cb_55] using branches_55_eq
    · simpa only [hg, cb_56] using branches_56_eq
    · simpa only [hg, cb_57] using branches_57_eq
    · simpa only [hg, cb_58] using branches_58_eq
    · simpa only [hg, cb_59] using branches_59_eq
    · simpa only [hg, cb_60] using branches_60_eq
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
  ⟨41,0,[-1],353⟩,
  ⟨41,1,[-1],803⟩,
  ⟨41,2,[-1],1095⟩,
  ⟨41,4,[-1],395⟩,
  ⟨41,5,[-1],395⟩,
  ⟨41,6,[-1],395⟩,
  ⟨41,7,[-1],395⟩,
  ⟨41,8,[-1],739⟩,
  ⟨41,9,[-1],739⟩,
  ⟨41,10,[-1],739⟩,
  ⟨41,11,[-1],739⟩,
  ⟨41,12,[-1],739⟩,
  ⟨41,13,[-1],739⟩,
  ⟨41,14,[-1],739⟩,
  ⟨41,15,[-1],739⟩,
  ⟨42,1,[-1],407⟩
]

private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨42,2,[-1],739⟩,
  ⟨42,3,[-1],739⟩,
  ⟨42,7,[-1],739⟩,
  ⟨42,8,[-1],1⟩,
  ⟨42,9,[-1],751⟩,
  ⟨42,11,[-1],1137⟩,
  ⟨42,13,[-1],1140⟩,
  ⟨42,17,[-1],407⟩,
  ⟨42,18,[-1],739⟩,
  ⟨42,19,[-1],739⟩,
  ⟨42,23,[-1],739⟩,
  ⟨42,24,[-1],918⟩,
  ⟨42,25,[-1],920⟩,
  ⟨42,27,[-1],1137⟩,
  ⟨42,29,[-1],920⟩,
  ⟨44,0,[-1],359⟩
]

private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨44,1,[-1],359⟩,
  ⟨44,2,[-1],359⟩,
  ⟨44,3,[-1],359⟩,
  ⟨44,4,[-1],359⟩,
  ⟨44,5,[-1],359⟩,
  ⟨44,6,[-1],359⟩,
  ⟨44,7,[-1],359⟩,
  ⟨44,8,[-1],396⟩,
  ⟨44,9,[-1],396⟩,
  ⟨44,10,[-1],396⟩,
  ⟨44,11,[-1],396⟩,
  ⟨44,12,[-1],396⟩,
  ⟨44,13,[-1],396⟩,
  ⟨44,14,[-1],396⟩,
  ⟨44,15,[-1],396⟩,
  ⟨44,16,[-1],356⟩
]

private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨44,17,[-1],356⟩,
  ⟨44,18,[-1],356⟩,
  ⟨44,19,[-1],356⟩,
  ⟨44,20,[-1],361⟩,
  ⟨44,21,[-1],361⟩,
  ⟨44,22,[-1],361⟩,
  ⟨44,23,[-1],361⟩,
  ⟨44,24,[-1],356⟩,
  ⟨44,25,[-1],356⟩,
  ⟨44,26,[-1],356⟩,
  ⟨44,27,[-1],356⟩,
  ⟨44,28,[-1],385⟩,
  ⟨44,29,[-1],370⟩,
  ⟨44,30,[-1],375⟩,
  ⟨44,31,[-1],400⟩,
  ⟨44,32,[-1],359⟩
]

private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨44,33,[-1],359⟩,
  ⟨44,34,[-1],359⟩,
  ⟨44,35,[-1],359⟩,
  ⟨44,36,[-1],359⟩,
  ⟨44,37,[-1],359⟩,
  ⟨44,38,[-1],359⟩,
  ⟨44,39,[-1],359⟩,
  ⟨44,40,[-1],396⟩,
  ⟨44,41,[-1],396⟩,
  ⟨44,42,[-1],396⟩,
  ⟨44,43,[-1],396⟩,
  ⟨44,44,[-1],396⟩,
  ⟨44,45,[-1],396⟩,
  ⟨44,46,[-1],396⟩,
  ⟨44,47,[-1],396⟩,
  ⟨44,48,[-1],356⟩
]

private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨44,49,[-1],356⟩,
  ⟨44,50,[-1],356⟩,
  ⟨44,51,[-1],356⟩,
  ⟨44,52,[-1],361⟩,
  ⟨44,53,[-1],361⟩,
  ⟨44,54,[-1],361⟩,
  ⟨44,55,[-1],361⟩,
  ⟨44,56,[-1],356⟩,
  ⟨44,57,[-1],356⟩,
  ⟨44,58,[-1],356⟩,
  ⟨44,59,[-1],356⟩,
  ⟨44,60,[-1],385⟩,
  ⟨44,61,[-1],370⟩,
  ⟨44,62,[-1],375⟩,
  ⟨44,63,[-1],400⟩,
  ⟨45,0,[-1],223⟩
]

private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨45,1,[-1],223⟩,
  ⟨45,2,[-1],223⟩,
  ⟨45,3,[-1],223⟩,
  ⟨45,4,[-1],798⟩,
  ⟨45,5,[-1],798⟩,
  ⟨45,6,[-1],798⟩,
  ⟨45,7,[-1],798⟩,
  ⟨45,8,[-1],928⟩,
  ⟨45,9,[-1],1120⟩,
  ⟨45,10,[-1],1192⟩,
  ⟨45,11,[-1],668⟩,
  ⟨45,12,[-1],798⟩,
  ⟨45,13,[-1],798⟩,
  ⟨45,14,[-1],798⟩,
  ⟨45,15,[-1],798⟩,
  ⟨45,16,[-1],1174⟩
]

private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨45,17,[-1],1174⟩,
  ⟨45,18,[-1],1174⟩,
  ⟨45,19,[-1],1174⟩,
  ⟨45,20,[-1],1174⟩,
  ⟨45,21,[-1],1174⟩,
  ⟨45,22,[-1],1174⟩,
  ⟨45,23,[-1],1174⟩,
  ⟨45,24,[-1],996⟩,
  ⟨45,25,[-1],996⟩,
  ⟨45,26,[-1],996⟩,
  ⟨45,27,[-1],996⟩,
  ⟨45,28,[-1],996⟩,
  ⟨45,29,[-1],996⟩,
  ⟨45,30,[-1],996⟩,
  ⟨45,31,[-1],996⟩,
  ⟨45,32,[-1],223⟩
]

private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨45,33,[-1],223⟩,
  ⟨45,34,[-1],223⟩,
  ⟨45,35,[-1],223⟩,
  ⟨45,36,[-1],798⟩,
  ⟨45,37,[-1],798⟩,
  ⟨45,38,[-1],798⟩,
  ⟨45,39,[-1],798⟩,
  ⟨45,40,[-1],928⟩,
  ⟨45,41,[-1],1120⟩,
  ⟨45,42,[-1],1192⟩,
  ⟨45,43,[-1],668⟩,
  ⟨45,44,[-1],798⟩,
  ⟨45,45,[-1],798⟩,
  ⟨45,46,[-1],798⟩,
  ⟨45,47,[-1],798⟩,
  ⟨45,48,[-1],1174⟩
]

private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨45,49,[-1],1174⟩,
  ⟨45,50,[-1],1174⟩,
  ⟨45,51,[-1],1174⟩,
  ⟨45,52,[-1],1174⟩,
  ⟨45,53,[-1],1174⟩,
  ⟨45,54,[-1],1174⟩,
  ⟨45,55,[-1],1174⟩,
  ⟨45,56,[-1],996⟩,
  ⟨45,57,[-1],996⟩,
  ⟨45,58,[-1],996⟩,
  ⟨45,59,[-1],996⟩,
  ⟨45,60,[-1],996⟩,
  ⟨45,61,[-1],996⟩,
  ⟨45,62,[-1],996⟩,
  ⟨45,63,[-1],996⟩,
  ⟨47,0,[-1],349⟩
]

private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨47,1,[-1],349⟩,
  ⟨47,2,[-1],349⟩,
  ⟨47,3,[-1],892⟩,
  ⟨47,4,[-1],349⟩,
  ⟨47,5,[-1],349⟩,
  ⟨47,6,[-1],349⟩,
  ⟨47,7,[-1],892⟩,
  ⟨47,8,[-1],384⟩,
  ⟨47,9,[-1],384⟩,
  ⟨47,10,[-1],384⟩,
  ⟨47,11,[-1],895⟩,
  ⟨47,12,[-1],384⟩,
  ⟨47,13,[-1],384⟩,
  ⟨47,14,[-1],384⟩,
  ⟨47,15,[-1],895⟩,
  ⟨47,16,[-1],357⟩
]

private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨47,17,[-1],357⟩,
  ⟨47,18,[-1],357⟩,
  ⟨47,19,[-1],893⟩,
  ⟨47,20,[-1],358⟩,
  ⟨47,21,[-1],358⟩,
  ⟨47,22,[-1],358⟩,
  ⟨47,23,[-1],894⟩,
  ⟨47,24,[-1],357⟩,
  ⟨47,25,[-1],357⟩,
  ⟨47,26,[-1],357⟩,
  ⟨47,27,[-1],893⟩,
  ⟨47,28,[-1],386⟩,
  ⟨47,29,[-1],369⟩,
  ⟨47,30,[-1],376⟩,
  ⟨47,31,[-1],896⟩,
  ⟨47,32,[-1],349⟩
]

private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨47,33,[-1],349⟩,
  ⟨47,34,[-1],349⟩,
  ⟨47,35,[-1],892⟩,
  ⟨47,36,[-1],349⟩,
  ⟨47,37,[-1],349⟩,
  ⟨47,38,[-1],349⟩,
  ⟨47,39,[-1],892⟩,
  ⟨47,40,[-1],384⟩,
  ⟨47,41,[-1],384⟩,
  ⟨47,42,[-1],384⟩,
  ⟨47,43,[-1],895⟩,
  ⟨47,44,[-1],384⟩,
  ⟨47,45,[-1],384⟩,
  ⟨47,46,[-1],384⟩,
  ⟨47,47,[-1],895⟩,
  ⟨47,48,[-1],357⟩
]

private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨47,49,[-1],357⟩,
  ⟨47,50,[-1],357⟩,
  ⟨47,51,[-1],893⟩,
  ⟨47,52,[-1],358⟩,
  ⟨47,53,[-1],358⟩,
  ⟨47,54,[-1],358⟩,
  ⟨47,55,[-1],894⟩,
  ⟨47,56,[-1],357⟩,
  ⟨47,57,[-1],357⟩,
  ⟨47,58,[-1],357⟩,
  ⟨47,59,[-1],893⟩,
  ⟨47,60,[-1],386⟩,
  ⟨47,61,[-1],369⟩,
  ⟨47,62,[-1],376⟩,
  ⟨47,63,[-1],896⟩,
  ⟨48,0,[-1],178⟩
]

private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨48,1,[-1],178⟩,
  ⟨48,2,[-1],178⟩,
  ⟨48,3,[-1],178⟩,
  ⟨48,4,[-1],791⟩,
  ⟨48,5,[-1],791⟩,
  ⟨48,6,[-1],791⟩,
  ⟨48,7,[-1],791⟩,
  ⟨48,8,[-1],897⟩,
  ⟨48,9,[-1],1181⟩,
  ⟨48,10,[-1],1019⟩,
  ⟨48,11,[-1],610⟩,
  ⟨48,12,[-1],791⟩,
  ⟨48,13,[-1],791⟩,
  ⟨48,14,[-1],791⟩,
  ⟨48,15,[-1],791⟩,
  ⟨48,16,[-1],832⟩
]

private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨48,17,[-1],832⟩,
  ⟨48,18,[-1],832⟩,
  ⟨48,19,[-1],832⟩,
  ⟨48,20,[-1],832⟩,
  ⟨48,21,[-1],832⟩,
  ⟨48,22,[-1],832⟩,
  ⟨48,23,[-1],832⟩,
  ⟨48,24,[-1],1179⟩,
  ⟨48,25,[-1],1179⟩,
  ⟨48,26,[-1],1179⟩,
  ⟨48,27,[-1],1179⟩,
  ⟨48,28,[-1],1179⟩,
  ⟨48,29,[-1],1179⟩,
  ⟨48,30,[-1],1179⟩,
  ⟨48,31,[-1],1179⟩,
  ⟨48,32,[-1],178⟩
]

private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨48,33,[-1],178⟩,
  ⟨48,34,[-1],178⟩,
  ⟨48,35,[-1],178⟩,
  ⟨48,36,[-1],791⟩,
  ⟨48,37,[-1],791⟩,
  ⟨48,38,[-1],791⟩,
  ⟨48,39,[-1],791⟩,
  ⟨48,40,[-1],897⟩,
  ⟨48,41,[-1],1181⟩,
  ⟨48,42,[-1],1019⟩,
  ⟨48,43,[-1],610⟩,
  ⟨48,44,[-1],791⟩,
  ⟨48,45,[-1],791⟩,
  ⟨48,46,[-1],791⟩,
  ⟨48,47,[-1],791⟩,
  ⟨48,48,[-1],832⟩
]

private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨48,49,[-1],832⟩,
  ⟨48,50,[-1],832⟩,
  ⟨48,51,[-1],832⟩,
  ⟨48,52,[-1],832⟩,
  ⟨48,53,[-1],832⟩,
  ⟨48,54,[-1],832⟩,
  ⟨48,55,[-1],832⟩,
  ⟨48,56,[-1],1179⟩,
  ⟨48,57,[-1],1179⟩,
  ⟨48,58,[-1],1179⟩,
  ⟨48,59,[-1],1179⟩,
  ⟨48,60,[-1],1179⟩,
  ⟨48,61,[-1],1179⟩,
  ⟨48,62,[-1],1179⟩,
  ⟨48,63,[-1],1179⟩,
  ⟨50,0,[-1],351⟩
]

private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨50,1,[-1],351⟩,
  ⟨50,2,[-1],351⟩,
  ⟨50,3,[-1],351⟩,
  ⟨50,4,[-1],351⟩,
  ⟨50,5,[-1],351⟩,
  ⟨50,6,[-1],351⟩,
  ⟨50,7,[-1],351⟩,
  ⟨50,8,[-1],381⟩,
  ⟨50,9,[-1],381⟩,
  ⟨50,10,[-1],381⟩,
  ⟨50,11,[-1],381⟩,
  ⟨50,12,[-1],381⟩,
  ⟨50,13,[-1],381⟩,
  ⟨50,14,[-1],381⟩,
  ⟨50,15,[-1],381⟩,
  ⟨50,16,[-1],355⟩
]

private theorem refs_valid_18 : ∀ rec ∈ chunk_18, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨50,17,[-1],355⟩,
  ⟨50,18,[-1],355⟩,
  ⟨50,19,[-1],355⟩,
  ⟨50,20,[-1],352⟩,
  ⟨50,21,[-1],352⟩,
  ⟨50,22,[-1],352⟩,
  ⟨50,23,[-1],352⟩,
  ⟨50,24,[-1],355⟩,
  ⟨50,25,[-1],355⟩,
  ⟨50,26,[-1],355⟩,
  ⟨50,27,[-1],355⟩,
  ⟨50,28,[-1],405⟩,
  ⟨50,29,[-1],365⟩,
  ⟨50,30,[-1],379⟩,
  ⟨50,31,[-1],388⟩,
  ⟨50,32,[-1],351⟩
]

private theorem refs_valid_19 : ∀ rec ∈ chunk_19, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨50,33,[-1],351⟩,
  ⟨50,34,[-1],351⟩,
  ⟨50,35,[-1],351⟩,
  ⟨50,36,[-1],351⟩,
  ⟨50,37,[-1],351⟩,
  ⟨50,38,[-1],351⟩,
  ⟨50,39,[-1],351⟩,
  ⟨50,40,[-1],381⟩,
  ⟨50,41,[-1],381⟩,
  ⟨50,42,[-1],381⟩,
  ⟨50,43,[-1],381⟩,
  ⟨50,44,[-1],381⟩,
  ⟨50,45,[-1],381⟩,
  ⟨50,46,[-1],381⟩,
  ⟨50,47,[-1],381⟩,
  ⟨50,48,[-1],355⟩
]

private theorem refs_valid_20 : ∀ rec ∈ chunk_20, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_21 : List MiddleCertRecord := [
  ⟨50,49,[-1],355⟩,
  ⟨50,50,[-1],355⟩,
  ⟨50,51,[-1],355⟩,
  ⟨50,52,[-1],352⟩,
  ⟨50,53,[-1],352⟩,
  ⟨50,54,[-1],352⟩,
  ⟨50,55,[-1],352⟩,
  ⟨50,56,[-1],355⟩,
  ⟨50,57,[-1],355⟩,
  ⟨50,58,[-1],355⟩,
  ⟨50,59,[-1],355⟩,
  ⟨50,60,[-1],405⟩,
  ⟨50,61,[-1],365⟩,
  ⟨50,62,[-1],379⟩,
  ⟨50,63,[-1],388⟩,
  ⟨51,0,[-1],531⟩
]

private theorem refs_valid_21 : ∀ rec ∈ chunk_21, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_22 : List MiddleCertRecord := [
  ⟨51,1,[-1],531⟩,
  ⟨51,2,[-1],531⟩,
  ⟨51,3,[-1],531⟩,
  ⟨51,4,[-1],1046⟩,
  ⟨51,5,[-1],1046⟩,
  ⟨51,6,[-1],1046⟩,
  ⟨51,7,[-1],1046⟩,
  ⟨51,8,[-1],823⟩,
  ⟨51,9,[-1],1010⟩,
  ⟨51,10,[-1],830⟩,
  ⟨51,11,[-1],676⟩,
  ⟨51,12,[-1],1046⟩,
  ⟨51,13,[-1],1046⟩,
  ⟨51,14,[-1],1046⟩,
  ⟨51,15,[-1],1046⟩,
  ⟨51,16,[-1],1116⟩
]

private theorem refs_valid_22 : ∀ rec ∈ chunk_22, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_23 : List MiddleCertRecord := [
  ⟨51,17,[-1],1116⟩,
  ⟨51,18,[-1],1116⟩,
  ⟨51,19,[-1],1116⟩,
  ⟨51,20,[-1],1116⟩,
  ⟨51,21,[-1],1116⟩,
  ⟨51,22,[-1],1116⟩,
  ⟨51,23,[-1],1116⟩,
  ⟨51,24,[-1],999⟩,
  ⟨51,25,[-1],999⟩,
  ⟨51,26,[-1],999⟩,
  ⟨51,27,[-1],999⟩,
  ⟨51,28,[-1],999⟩,
  ⟨51,29,[-1],999⟩,
  ⟨51,30,[-1],999⟩,
  ⟨51,31,[-1],999⟩,
  ⟨51,32,[-1],531⟩
]

private theorem refs_valid_23 : ∀ rec ∈ chunk_23, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_24 : List MiddleCertRecord := [
  ⟨51,33,[-1],531⟩,
  ⟨51,34,[-1],531⟩,
  ⟨51,35,[-1],531⟩,
  ⟨51,36,[-1],1046⟩,
  ⟨51,37,[-1],1046⟩,
  ⟨51,38,[-1],1046⟩,
  ⟨51,39,[-1],1046⟩,
  ⟨51,40,[-1],823⟩,
  ⟨51,41,[-1],1010⟩,
  ⟨51,42,[-1],830⟩,
  ⟨51,43,[-1],676⟩,
  ⟨51,44,[-1],1046⟩,
  ⟨51,45,[-1],1046⟩,
  ⟨51,46,[-1],1046⟩,
  ⟨51,47,[-1],1046⟩,
  ⟨51,48,[-1],1116⟩
]

private theorem refs_valid_24 : ∀ rec ∈ chunk_24, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_25 : List MiddleCertRecord := [
  ⟨51,49,[-1],1116⟩,
  ⟨51,50,[-1],1116⟩,
  ⟨51,51,[-1],1116⟩,
  ⟨51,52,[-1],1116⟩,
  ⟨51,53,[-1],1116⟩,
  ⟨51,54,[-1],1116⟩,
  ⟨51,55,[-1],1116⟩,
  ⟨51,56,[-1],999⟩,
  ⟨51,57,[-1],999⟩,
  ⟨51,58,[-1],999⟩,
  ⟨51,59,[-1],999⟩,
  ⟨51,60,[-1],999⟩,
  ⟨51,61,[-1],999⟩,
  ⟨51,62,[-1],999⟩,
  ⟨51,63,[-1],999⟩,
  ⟨53,0,[-1],343⟩
]

private theorem refs_valid_25 : ∀ rec ∈ chunk_25, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_26 : List MiddleCertRecord := [
  ⟨53,1,[-1],343⟩,
  ⟨53,2,[-1],740⟩,
  ⟨53,3,[-1],1141⟩,
  ⟨53,4,[-1],401⟩,
  ⟨53,5,[-1],401⟩,
  ⟨53,6,[-1],753⟩,
  ⟨53,7,[-1],1144⟩,
  ⟨53,8,[-1],409⟩,
  ⟨53,9,[-1],1058⟩,
  ⟨53,10,[-1],743⟩,
  ⟨53,11,[-1],1142⟩,
  ⟨53,12,[-1],410⟩,
  ⟨53,13,[-1],1065⟩,
  ⟨53,14,[-1],747⟩,
  ⟨53,15,[-1],1143⟩,
  ⟨54,0,[-1],535⟩
]

private theorem refs_valid_26 : ∀ rec ∈ chunk_26, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_27 : List MiddleCertRecord := [
  ⟨54,1,[-1],666⟩,
  ⟨54,2,[-1],776⟩,
  ⟨54,3,[-1],793⟩,
  ⟨54,4,[-1],535⟩,
  ⟨54,5,[-1],594⟩,
  ⟨54,6,[-1],776⟩,
  ⟨54,7,[-1],793⟩,
  ⟨54,8,[-1],535⟩,
  ⟨54,9,[-1],901⟩,
  ⟨54,10,[-1],776⟩,
  ⟨54,11,[-1],793⟩,
  ⟨54,12,[-1],535⟩,
  ⟨54,13,[-1],1008⟩,
  ⟨54,14,[-1],776⟩,
  ⟨54,15,[-1],793⟩,
  ⟨55,0,[-1],228⟩
]

private theorem refs_valid_27 : ∀ rec ∈ chunk_27, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_28 : List MiddleCertRecord := [
  ⟨55,1,[-1],372⟩,
  ⟨55,2,[-1],910⟩,
  ⟨55,3,[-1],808⟩,
  ⟨55,4,[-1],227⟩,
  ⟨55,5,[-1],390⟩,
  ⟨55,6,[-1],912⟩,
  ⟨55,7,[-1],806⟩,
  ⟨55,8,[-1],226⟩,
  ⟨55,9,[-1],383⟩,
  ⟨55,10,[-1],911⟩,
  ⟨55,11,[-1],807⟩,
  ⟨55,12,[-1],229⟩,
  ⟨55,13,[-1],399⟩,
  ⟨55,14,[-1],915⟩,
  ⟨55,15,[-1],809⟩,
  ⟨56,0,[-1],805⟩
]

private theorem refs_valid_28 : ∀ rec ∈ chunk_28, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_29 : List MiddleCertRecord := [
  ⟨56,1,[-1],1001⟩,
  ⟨56,2,[-1],619⟩,
  ⟨56,3,[-1],1086⟩,
  ⟨56,4,[-1],1178⟩,
  ⟨56,5,[-1],822⟩,
  ⟨56,6,[-1],1084⟩,
  ⟨56,7,[-1],828⟩,
  ⟨56,8,[-1],891⟩,
  ⟨56,9,[-1],890⟩,
  ⟨56,10,[-1],1023⟩,
  ⟨56,11,[-1],1021⟩,
  ⟨56,12,[-1],801⟩,
  ⟨56,13,[-1],680⟩,
  ⟨56,14,[-1],1248⟩,
  ⟨56,15,[-1],1197⟩,
  ⟨57,0,[-1],230⟩
]

private theorem refs_valid_29 : ∀ rec ∈ chunk_29, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_30 : List MiddleCertRecord := [
  ⟨57,1,[-1],231⟩,
  ⟨57,2,[-1],230⟩,
  ⟨57,3,[-1],1133⟩,
  ⟨57,4,[-1],612⟩,
  ⟨57,5,[-1],804⟩,
  ⟨57,6,[-1],1195⟩,
  ⟨57,7,[-1],713⟩,
  ⟨57,8,[-1],909⟩,
  ⟨57,9,[-1],913⟩,
  ⟨57,10,[-1],909⟩,
  ⟨57,11,[-1],909⟩,
  ⟨57,12,[-1],819⟩,
  ⟨57,13,[-1],820⟩,
  ⟨57,14,[-1],819⟩,
  ⟨57,15,[-1],819⟩,
  ⟨59,0,[-1],493⟩
]

private theorem refs_valid_30 : ∀ rec ∈ chunk_30, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_31 : List MiddleCertRecord := [
  ⟨59,1,[-1],709⟩,
  ⟨59,2,[-1],1043⟩,
  ⟨59,3,[-1],1189⟩,
  ⟨59,4,[-1],493⟩,
  ⟨59,5,[-1],916⟩,
  ⟨59,6,[-1],1043⟩,
  ⟨59,7,[-1],1189⟩,
  ⟨59,8,[-1],495⟩,
  ⟨59,9,[-1],1125⟩,
  ⟨59,10,[-1],1045⟩,
  ⟨59,11,[-1],1191⟩,
  ⟨59,12,[-1],495⟩,
  ⟨59,13,[-1],921⟩,
  ⟨59,14,[-1],1045⟩,
  ⟨59,15,[-1],1191⟩,
  ⟨59,16,[-1],493⟩
]

private theorem refs_valid_31 : ∀ rec ∈ chunk_31, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_32 : List MiddleCertRecord := [
  ⟨59,17,[-1],1241⟩,
  ⟨59,18,[-1],1043⟩,
  ⟨59,19,[-1],1189⟩,
  ⟨59,20,[-1],493⟩,
  ⟨59,21,[-1],916⟩,
  ⟨59,22,[-1],1043⟩,
  ⟨59,23,[-1],1189⟩,
  ⟨59,24,[-1],493⟩,
  ⟨59,25,[-1],711⟩,
  ⟨59,26,[-1],1043⟩,
  ⟨59,27,[-1],1189⟩,
  ⟨59,28,[-1],493⟩,
  ⟨59,29,[-1],916⟩,
  ⟨59,30,[-1],1043⟩,
  ⟨59,31,[-1],1189⟩
]

private theorem refs_valid_32 : ∀ rec ∈ chunk_32, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def selectedRecords : List MiddleCertRecord := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28, chunk_29, chunk_30, chunk_31, chunk_32].flatten

private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by
  decide +kernel

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([3] : List ℕ)))
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end RetRow3

open RetRow3

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([3] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)

#print axioms solution
