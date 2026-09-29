-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_equal_II_b_normal_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T17:06:10.039934+00:00
-- url     : https://prove2.me/submissions/db141b42-e5de-42e0-ad8e-fce0536ce737

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

namespace RetRow6

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

private def branches_98 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_98_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 98)
      = (branches_98).map decodeBranch := by
  decide +kernel

private def branches_99 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_99_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 99)
      = (branches_99).map decodeBranch := by
  decide +kernel

private def branches_100 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,637⟩,⟨true,false,608⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨false,false,637⟩,⟨true,false,608⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨false,false,637⟩,⟨true,false,608⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨false,false,637⟩,⟨true,false,608⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic)
]

private theorem branches_100_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 100)
      = (branches_100).map decodeBranch := by
  decide +kernel

private def branches_101 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,587⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,149⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,180⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,562⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,587⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,149⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,180⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,562⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,502⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,156⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,192⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,338⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,502⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,156⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,192⟩)),
([⟨false,false,598⟩,⟨false,false,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,338⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,295⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,232⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,308⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,363⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,295⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,232⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,308⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,363⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,559⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,81⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,82⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,545⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,559⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,81⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,82⟩)),
([⟨false,false,598⟩,⟨true,true,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,545⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,587⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,149⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,180⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,562⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,587⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,149⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,180⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨true,false,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,562⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,502⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,156⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,192⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,338⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,502⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,156⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,192⟩)),
([⟨true,true,598⟩,⟨false,true,480⟩,⟨false,true,500⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,338⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,295⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,232⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,308⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,363⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,295⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,232⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,308⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨false,false,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,363⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,559⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨false,false,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,81⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,82⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨false,false,485⟩,⟨true,true,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,545⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨true,false,490⟩],(.bound ⟨true,false,559⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨false,true,522⟩,⟨false,true,490⟩],(.bound ⟨true,false,81⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨false,false,531⟩],(.bound ⟨true,false,82⟩)),
([⟨true,true,598⟩,⟨true,false,480⟩,⟨true,true,540⟩,⟨true,true,485⟩,⟨true,false,522⟩,⟨true,true,531⟩],(.bound ⟨true,false,545⟩))
]

private theorem branches_101_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 101)
      = (branches_101).map decodeBranch := by
  decide +kernel

private def branches_102 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,79⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,32⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,45⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,64⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,79⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,32⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,45⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,64⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,544⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,797⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,776⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,59⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,544⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,797⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,776⟩)),
([⟨false,true,687⟩,⟨false,false,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,59⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,231⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,796⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,751⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,141⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,231⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,796⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,751⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,141⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,62⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,10⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,336⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,49⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,62⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,10⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,336⟩)),
([⟨false,true,687⟩,⟨true,true,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,49⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,79⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,32⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,45⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,64⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,79⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,32⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,45⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨true,false,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,64⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,544⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,797⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,776⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,59⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,544⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,797⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,776⟩)),
([⟨true,false,687⟩,⟨false,true,757⟩,⟨false,true,708⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,59⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,231⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,796⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,751⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,141⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,231⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,796⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,751⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨false,false,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,141⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,62⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨false,false,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,10⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,336⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨false,true,754⟩,⟨true,true,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,49⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨true,false,758⟩],(.bound ⟨false,false,62⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨false,true,736⟩,⟨false,true,758⟩],(.bound ⟨false,false,10⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨false,false,785⟩],(.bound ⟨false,false,336⟩)),
([⟨true,false,687⟩,⟨true,false,757⟩,⟨true,true,739⟩,⟨true,false,754⟩,⟨true,false,736⟩,⟨true,true,785⟩],(.bound ⟨false,false,49⟩))
]

private theorem branches_102_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 102)
      = (branches_102).map decodeBranch := by
  decide +kernel

private def branches_103 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_103_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 103)
      = (branches_103).map decodeBranch := by
  decide +kernel

private def branches_104 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_104_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 104)
      = (branches_104).map decodeBranch := by
  decide +kernel

private def branches_105 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_105_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 105)
      = (branches_105).map decodeBranch := by
  decide +kernel

private def branches_106 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_106_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 106)
      = (branches_106).map decodeBranch := by
  decide +kernel

private def branches_107 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_107_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 107)
      = (branches_107).map decodeBranch := by
  decide +kernel

private def branches_108 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_108_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 108)
      = (branches_108).map decodeBranch := by
  decide +kernel

private def branches_109 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_109_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 109)
      = (branches_109).map decodeBranch := by
  decide +kernel

private def branches_110 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_110_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 110)
      = (branches_110).map decodeBranch := by
  decide +kernel

private def branches_111 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_111_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 111)
      = (branches_111).map decodeBranch := by
  decide +kernel

private def branches_112 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,637⟩,⟨true,false,608⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,233⟩)),
([⟨false,false,637⟩,⟨true,false,608⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,581⟩)),
([⟨false,false,637⟩,⟨true,false,608⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,125⟩)),
([⟨false,false,637⟩,⟨true,false,608⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,182⟩)),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,273⟩)),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,767⟩)),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,693⟩)),
([⟨false,false,637⟩,⟨false,true,608⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,408⟩)),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,299⟩)),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,759⟩)),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,662⟩)),
([⟨true,true,637⟩,⟨false,false,671⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,455⟩)),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨false,false,613⟩,⟨true,false,621⟩],(.bound ⟨false,false,193⟩)),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨false,false,613⟩,⟨false,true,621⟩],(.bound ⟨false,false,38⟩)),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨true,true,613⟩,⟨false,false,682⟩],(.bound ⟨false,false,317⟩)),
([⟨true,true,637⟩,⟨true,true,671⟩,⟨true,true,613⟩,⟨true,true,682⟩],(.bound ⟨false,false,168⟩))
]

private theorem branches_112_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 112)
      = (branches_112).map decodeBranch := by
  decide +kernel

private def branches_113 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨false,false,613⟩,⟨true,false,528⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,637⟩,⟨true,false,602⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨false,false,637⟩,⟨false,true,602⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,637⟩,⟨false,false,665⟩],.automatic),
([⟨true,true,613⟩,⟨true,true,579⟩,⟨true,true,637⟩,⟨true,true,665⟩],.automatic)
]

private theorem branches_113_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 113)
      = (branches_113).map decodeBranch := by
  decide +kernel

private def branches_114 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_114_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 114)
      = (branches_114).map decodeBranch := by
  decide +kernel

private def branches_115 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_115_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 115)
      = (branches_115).map decodeBranch := by
  decide +kernel

private def branches_116 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_116_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 116)
      = (branches_116).map decodeBranch := by
  decide +kernel

private def branches_117 : List (List MiddleCertBoundRef × RefComparison) := [
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

private theorem branches_117_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 117)
      = (branches_117).map decodeBranch := by
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
  if g = 98 then branches_98 else
  if g = 99 then branches_99 else
  if g = 100 then branches_100 else
  if g = 101 then branches_101 else
  if g = 102 then branches_102 else
  if g = 103 then branches_103 else
  if g = 104 then branches_104 else
  if g = 105 then branches_105 else
  if g = 106 then branches_106 else
  if g = 107 then branches_107 else
  if g = 108 then branches_108 else
  if g = 109 then branches_109 else
  if g = 110 then branches_110 else
  if g = 111 then branches_111 else
  if g = 112 then branches_112 else
  if g = 113 then branches_113 else
  if g = 114 then branches_114 else
  if g = 115 then branches_115 else
  if g = 116 then branches_116 else
  if g = 117 then branches_117 else
  []

private theorem cb_98 : cachedBranches 98 = branches_98 := by
  norm_num [cachedBranches]

private theorem cb_99 : cachedBranches 99 = branches_99 := by
  norm_num [cachedBranches]

private theorem cb_100 : cachedBranches 100 = branches_100 := by
  norm_num [cachedBranches]

private theorem cb_101 : cachedBranches 101 = branches_101 := by
  norm_num [cachedBranches]

private theorem cb_102 : cachedBranches 102 = branches_102 := by
  norm_num [cachedBranches]

private theorem cb_103 : cachedBranches 103 = branches_103 := by
  norm_num [cachedBranches]

private theorem cb_104 : cachedBranches 104 = branches_104 := by
  norm_num [cachedBranches]

private theorem cb_105 : cachedBranches 105 = branches_105 := by
  norm_num [cachedBranches]

private theorem cb_106 : cachedBranches 106 = branches_106 := by
  norm_num [cachedBranches]

private theorem cb_107 : cachedBranches 107 = branches_107 := by
  norm_num [cachedBranches]

private theorem cb_108 : cachedBranches 108 = branches_108 := by
  norm_num [cachedBranches]

private theorem cb_109 : cachedBranches 109 = branches_109 := by
  norm_num [cachedBranches]

private theorem cb_110 : cachedBranches 110 = branches_110 := by
  norm_num [cachedBranches]

private theorem cb_111 : cachedBranches 111 = branches_111 := by
  norm_num [cachedBranches]

private theorem cb_112 : cachedBranches 112 = branches_112 := by
  norm_num [cachedBranches]

private theorem cb_113 : cachedBranches 113 = branches_113 := by
  norm_num [cachedBranches]

private theorem cb_114 : cachedBranches 114 = branches_114 := by
  norm_num [cachedBranches]

private theorem cb_115 : cachedBranches 115 = branches_115 := by
  norm_num [cachedBranches]

private theorem cb_116 : cachedBranches 116 = branches_116 := by
  norm_num [cachedBranches]

private theorem cb_117 : cachedBranches 117 = branches_117 := by
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

private def selectedGoals : List ℕ := [98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117]

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
    · simpa only [hg, cb_98] using branches_98_eq
    · simpa only [hg, cb_99] using branches_99_eq
    · simpa only [hg, cb_100] using branches_100_eq
    · simpa only [hg, cb_101] using branches_101_eq
    · simpa only [hg, cb_102] using branches_102_eq
    · simpa only [hg, cb_103] using branches_103_eq
    · simpa only [hg, cb_104] using branches_104_eq
    · simpa only [hg, cb_105] using branches_105_eq
    · simpa only [hg, cb_106] using branches_106_eq
    · simpa only [hg, cb_107] using branches_107_eq
    · simpa only [hg, cb_108] using branches_108_eq
    · simpa only [hg, cb_109] using branches_109_eq
    · simpa only [hg, cb_110] using branches_110_eq
    · simpa only [hg, cb_111] using branches_111_eq
    · simpa only [hg, cb_112] using branches_112_eq
    · simpa only [hg, cb_113] using branches_113_eq
    · simpa only [hg, cb_114] using branches_114_eq
    · simpa only [hg, cb_115] using branches_115_eq
    · simpa only [hg, cb_116] using branches_116_eq
    · simpa only [hg, cb_117] using branches_117_eq
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
  ⟨98,4,[-1],406⟩,
  ⟨98,6,[-1],734⟩,
  ⟨98,7,[-1],1135⟩,
  ⟨98,12,[-1],739⟩,
  ⟨98,13,[-1],739⟩,
  ⟨98,14,[-1],739⟩,
  ⟨99,1,[-1],407⟩,
  ⟨99,2,[-1],739⟩,
  ⟨99,3,[-1],739⟩,
  ⟨99,7,[-1],739⟩,
  ⟨99,8,[-1],745⟩,
  ⟨99,9,[-1],745⟩,
  ⟨99,11,[-1],1137⟩,
  ⟨99,13,[-1],1138⟩,
  ⟨99,17,[-1],407⟩,
  ⟨99,18,[-1],739⟩
]

private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨99,19,[-1],739⟩,
  ⟨99,23,[-1],739⟩,
  ⟨99,24,[-1],744⟩,
  ⟨99,25,[-1],744⟩,
  ⟨99,27,[-1],1137⟩,
  ⟨99,29,[-1],1136⟩,
  ⟨101,0,[-1],247⟩,
  ⟨101,1,[-1],247⟩,
  ⟨101,2,[-1],1050⟩,
  ⟨101,3,[-1],993⟩,
  ⟨101,4,[-1],247⟩,
  ⟨101,5,[-1],247⟩,
  ⟨101,6,[-1],1050⟩,
  ⟨101,7,[-1],993⟩,
  ⟨101,8,[-1],259⟩,
  ⟨101,9,[-1],259⟩
]

private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨101,10,[-1],1052⟩,
  ⟨101,11,[-1],994⟩,
  ⟨101,12,[-1],259⟩,
  ⟨101,13,[-1],259⟩,
  ⟨101,14,[-1],1052⟩,
  ⟨101,15,[-1],994⟩,
  ⟨101,16,[-1],239⟩,
  ⟨101,17,[-1],239⟩,
  ⟨101,18,[-1],1048⟩,
  ⟨101,19,[-1],991⟩,
  ⟨101,20,[-1],240⟩,
  ⟨101,21,[-1],240⟩,
  ⟨101,22,[-1],1049⟩,
  ⟨101,23,[-1],992⟩,
  ⟨101,24,[-1],239⟩,
  ⟨101,25,[-1],239⟩
]

private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨101,26,[-1],1048⟩,
  ⟨101,27,[-1],991⟩,
  ⟨101,28,[-1],265⟩,
  ⟨101,29,[-1],258⟩,
  ⟨101,30,[-1],1051⟩,
  ⟨101,31,[-1],995⟩,
  ⟨101,32,[-1],1090⟩,
  ⟨101,33,[-1],1090⟩,
  ⟨101,34,[-1],1090⟩,
  ⟨101,35,[-1],993⟩,
  ⟨101,36,[-1],1090⟩,
  ⟨101,37,[-1],1090⟩,
  ⟨101,38,[-1],1090⟩,
  ⟨101,39,[-1],993⟩,
  ⟨101,40,[-1],1093⟩,
  ⟨101,41,[-1],1093⟩
]

private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨101,42,[-1],1093⟩,
  ⟨101,43,[-1],994⟩,
  ⟨101,44,[-1],1093⟩,
  ⟨101,45,[-1],1093⟩,
  ⟨101,46,[-1],1093⟩,
  ⟨101,47,[-1],994⟩,
  ⟨101,48,[-1],1088⟩,
  ⟨101,49,[-1],1088⟩,
  ⟨101,50,[-1],1088⟩,
  ⟨101,51,[-1],991⟩,
  ⟨101,52,[-1],1089⟩,
  ⟨101,53,[-1],1089⟩,
  ⟨101,54,[-1],1089⟩,
  ⟨101,55,[-1],992⟩,
  ⟨101,56,[-1],1088⟩,
  ⟨101,57,[-1],1088⟩
]

private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨101,58,[-1],1088⟩,
  ⟨101,59,[-1],991⟩,
  ⟨101,60,[-1],1094⟩,
  ⟨101,61,[-1],1092⟩,
  ⟨101,62,[-1],1091⟩,
  ⟨101,63,[-1],995⟩,
  ⟨102,0,[-1],490⟩,
  ⟨102,1,[-1],490⟩,
  ⟨102,2,[-1],490⟩,
  ⟨102,3,[-1],490⟩,
  ⟨102,4,[-1],802⟩,
  ⟨102,5,[-1],802⟩,
  ⟨102,6,[-1],802⟩,
  ⟨102,7,[-1],802⟩,
  ⟨102,8,[-1],825⟩,
  ⟨102,9,[-1],797⟩
]

private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨102,10,[-1],817⟩,
  ⟨102,11,[-1],663⟩,
  ⟨102,12,[-1],802⟩,
  ⟨102,13,[-1],802⟩,
  ⟨102,14,[-1],802⟩,
  ⟨102,15,[-1],802⟩,
  ⟨102,16,[-1],925⟩,
  ⟨102,17,[-1],925⟩,
  ⟨102,18,[-1],925⟩,
  ⟨102,19,[-1],925⟩,
  ⟨102,20,[-1],925⟩,
  ⟨102,21,[-1],925⟩,
  ⟨102,22,[-1],925⟩,
  ⟨102,23,[-1],925⟩,
  ⟨102,24,[-1],1168⟩,
  ⟨102,25,[-1],1168⟩
]

private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨102,26,[-1],1168⟩,
  ⟨102,27,[-1],1168⟩,
  ⟨102,28,[-1],1168⟩,
  ⟨102,29,[-1],1168⟩,
  ⟨102,30,[-1],1168⟩,
  ⟨102,31,[-1],1168⟩,
  ⟨102,32,[-1],490⟩,
  ⟨102,33,[-1],490⟩,
  ⟨102,34,[-1],490⟩,
  ⟨102,35,[-1],490⟩,
  ⟨102,36,[-1],802⟩,
  ⟨102,37,[-1],802⟩,
  ⟨102,38,[-1],802⟩,
  ⟨102,39,[-1],802⟩,
  ⟨102,40,[-1],825⟩,
  ⟨102,41,[-1],797⟩
]

private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨102,42,[-1],817⟩,
  ⟨102,43,[-1],663⟩,
  ⟨102,44,[-1],802⟩,
  ⟨102,45,[-1],802⟩,
  ⟨102,46,[-1],802⟩,
  ⟨102,47,[-1],802⟩,
  ⟨102,48,[-1],925⟩,
  ⟨102,49,[-1],925⟩,
  ⟨102,50,[-1],925⟩,
  ⟨102,51,[-1],925⟩,
  ⟨102,52,[-1],925⟩,
  ⟨102,53,[-1],925⟩,
  ⟨102,54,[-1],925⟩,
  ⟨102,55,[-1],925⟩,
  ⟨102,56,[-1],1168⟩,
  ⟨102,57,[-1],1168⟩
]

private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨102,58,[-1],1168⟩,
  ⟨102,59,[-1],1168⟩,
  ⟨102,60,[-1],1168⟩,
  ⟨102,61,[-1],1168⟩,
  ⟨102,62,[-1],1168⟩,
  ⟨102,63,[-1],1168⟩,
  ⟨104,0,[-1],243⟩,
  ⟨104,1,[-1],243⟩,
  ⟨104,2,[-1],243⟩,
  ⟨104,3,[-1],243⟩,
  ⟨104,4,[-1],243⟩,
  ⟨104,5,[-1],243⟩,
  ⟨104,6,[-1],243⟩,
  ⟨104,7,[-1],243⟩,
  ⟨104,8,[-1],266⟩,
  ⟨104,9,[-1],266⟩
]

private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨104,10,[-1],266⟩,
  ⟨104,11,[-1],266⟩,
  ⟨104,12,[-1],266⟩,
  ⟨104,13,[-1],266⟩,
  ⟨104,14,[-1],266⟩,
  ⟨104,15,[-1],266⟩,
  ⟨104,16,[-1],242⟩,
  ⟨104,17,[-1],242⟩,
  ⟨104,18,[-1],242⟩,
  ⟨104,19,[-1],242⟩,
  ⟨104,20,[-1],245⟩,
  ⟨104,21,[-1],245⟩,
  ⟨104,22,[-1],245⟩,
  ⟨104,23,[-1],245⟩,
  ⟨104,24,[-1],242⟩,
  ⟨104,25,[-1],242⟩
]

private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨104,26,[-1],242⟩,
  ⟨104,27,[-1],242⟩,
  ⟨104,28,[-1],260⟩,
  ⟨104,29,[-1],253⟩,
  ⟨104,30,[-1],256⟩,
  ⟨104,31,[-1],269⟩,
  ⟨104,32,[-1],243⟩,
  ⟨104,33,[-1],243⟩,
  ⟨104,34,[-1],243⟩,
  ⟨104,35,[-1],243⟩,
  ⟨104,36,[-1],243⟩,
  ⟨104,37,[-1],243⟩,
  ⟨104,38,[-1],243⟩,
  ⟨104,39,[-1],243⟩,
  ⟨104,40,[-1],266⟩,
  ⟨104,41,[-1],266⟩
]

private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨104,42,[-1],266⟩,
  ⟨104,43,[-1],266⟩,
  ⟨104,44,[-1],266⟩,
  ⟨104,45,[-1],266⟩,
  ⟨104,46,[-1],266⟩,
  ⟨104,47,[-1],266⟩,
  ⟨104,48,[-1],242⟩,
  ⟨104,49,[-1],242⟩,
  ⟨104,50,[-1],242⟩,
  ⟨104,51,[-1],242⟩,
  ⟨104,52,[-1],245⟩,
  ⟨104,53,[-1],245⟩,
  ⟨104,54,[-1],245⟩,
  ⟨104,55,[-1],245⟩,
  ⟨104,56,[-1],242⟩,
  ⟨104,57,[-1],242⟩
]

private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨104,58,[-1],242⟩,
  ⟨104,59,[-1],242⟩,
  ⟨104,60,[-1],260⟩,
  ⟨104,61,[-1],253⟩,
  ⟨104,62,[-1],256⟩,
  ⟨104,63,[-1],269⟩,
  ⟨105,0,[-1],224⟩,
  ⟨105,1,[-1],224⟩,
  ⟨105,2,[-1],224⟩,
  ⟨105,3,[-1],224⟩,
  ⟨105,4,[-1],799⟩,
  ⟨105,5,[-1],799⟩,
  ⟨105,6,[-1],799⟩,
  ⟨105,7,[-1],799⟩,
  ⟨105,8,[-1],929⟩,
  ⟨105,9,[-1],1121⟩
]

private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨105,10,[-1],1193⟩,
  ⟨105,11,[-1],669⟩,
  ⟨105,12,[-1],799⟩,
  ⟨105,13,[-1],799⟩,
  ⟨105,14,[-1],799⟩,
  ⟨105,15,[-1],799⟩,
  ⟨105,16,[-1],1175⟩,
  ⟨105,17,[-1],1175⟩,
  ⟨105,18,[-1],1175⟩,
  ⟨105,19,[-1],1175⟩,
  ⟨105,20,[-1],1175⟩,
  ⟨105,21,[-1],1175⟩,
  ⟨105,22,[-1],1175⟩,
  ⟨105,23,[-1],1175⟩,
  ⟨105,24,[-1],997⟩,
  ⟨105,25,[-1],997⟩
]

private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨105,26,[-1],997⟩,
  ⟨105,27,[-1],997⟩,
  ⟨105,28,[-1],997⟩,
  ⟨105,29,[-1],997⟩,
  ⟨105,30,[-1],997⟩,
  ⟨105,31,[-1],997⟩,
  ⟨105,32,[-1],224⟩,
  ⟨105,33,[-1],224⟩,
  ⟨105,34,[-1],224⟩,
  ⟨105,35,[-1],224⟩,
  ⟨105,36,[-1],799⟩,
  ⟨105,37,[-1],799⟩,
  ⟨105,38,[-1],799⟩,
  ⟨105,39,[-1],799⟩,
  ⟨105,40,[-1],929⟩,
  ⟨105,41,[-1],1121⟩
]

private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨105,42,[-1],1193⟩,
  ⟨105,43,[-1],669⟩,
  ⟨105,44,[-1],799⟩,
  ⟨105,45,[-1],799⟩,
  ⟨105,46,[-1],799⟩,
  ⟨105,47,[-1],799⟩,
  ⟨105,48,[-1],1175⟩,
  ⟨105,49,[-1],1175⟩,
  ⟨105,50,[-1],1175⟩,
  ⟨105,51,[-1],1175⟩,
  ⟨105,52,[-1],1175⟩,
  ⟨105,53,[-1],1175⟩,
  ⟨105,54,[-1],1175⟩,
  ⟨105,55,[-1],1175⟩,
  ⟨105,56,[-1],997⟩,
  ⟨105,57,[-1],997⟩
]

private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨105,58,[-1],997⟩,
  ⟨105,59,[-1],997⟩,
  ⟨105,60,[-1],997⟩,
  ⟨105,61,[-1],997⟩,
  ⟨105,62,[-1],997⟩,
  ⟨105,63,[-1],997⟩,
  ⟨107,0,[-1],237⟩,
  ⟨107,1,[-1],267⟩,
  ⟨107,2,[-1],246⟩,
  ⟨107,3,[-1],270⟩,
  ⟨107,4,[-1],237⟩,
  ⟨107,5,[-1],267⟩,
  ⟨107,6,[-1],254⟩,
  ⟨107,7,[-1],252⟩,
  ⟨107,8,[-1],237⟩,
  ⟨107,9,[-1],267⟩
]

private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨107,10,[-1],246⟩,
  ⟨107,11,[-1],251⟩,
  ⟨107,12,[-1],237⟩,
  ⟨107,13,[-1],267⟩,
  ⟨107,14,[-1],246⟩,
  ⟨107,15,[-1],263⟩,
  ⟨108,0,[-1],467⟩,
  ⟨108,1,[-1],469⟩,
  ⟨108,2,[-1],468⟩,
  ⟨108,3,[-1],468⟩,
  ⟨108,4,[-1],1082⟩,
  ⟨108,5,[-1],1032⟩,
  ⟨108,6,[-1],905⟩,
  ⟨108,7,[-1],614⟩,
  ⟨108,8,[-1],716⟩,
  ⟨108,9,[-1],720⟩
]

private theorem refs_valid_18 : ∀ rec ∈ chunk_18, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨108,10,[-1],719⟩,
  ⟨108,11,[-1],719⟩,
  ⟨108,12,[-1],1163⟩,
  ⟨108,13,[-1],1165⟩,
  ⟨108,14,[-1],1164⟩,
  ⟨108,15,[-1],1164⟩,
  ⟨110,0,[-1],234⟩,
  ⟨110,1,[-1],271⟩,
  ⟨110,2,[-1],238⟩,
  ⟨110,3,[-1],272⟩,
  ⟨110,4,[-1],234⟩,
  ⟨110,5,[-1],271⟩,
  ⟨110,6,[-1],249⟩,
  ⟨110,7,[-1],257⟩,
  ⟨110,8,[-1],234⟩,
  ⟨110,9,[-1],271⟩
]

private theorem refs_valid_19 : ∀ rec ∈ chunk_19, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨110,10,[-1],238⟩,
  ⟨110,11,[-1],248⟩,
  ⟨110,12,[-1],234⟩,
  ⟨110,13,[-1],271⟩,
  ⟨110,14,[-1],238⟩,
  ⟨110,15,[-1],264⟩,
  ⟨111,0,[-1],8⟩,
  ⟨111,1,[-1],8⟩,
  ⟨111,2,[-1],8⟩,
  ⟨111,3,[-1],8⟩,
  ⟨111,4,[-1],592⟩,
  ⟨111,5,[-1],705⟩,
  ⟨111,6,[-1],599⟩,
  ⟨111,7,[-1],1002⟩,
  ⟨111,8,[-1],763⟩,
  ⟨111,9,[-1],763⟩
]

private theorem refs_valid_20 : ∀ rec ∈ chunk_20, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_21 : List MiddleCertRecord := [
  ⟨111,10,[-1],763⟩,
  ⟨111,11,[-1],763⟩,
  ⟨111,12,[-1],687⟩,
  ⟨111,13,[-1],687⟩,
  ⟨111,14,[-1],687⟩,
  ⟨111,15,[-1],687⟩,
  ⟨112,0,[-1],449⟩,
  ⟨112,1,[-1],449⟩,
  ⟨112,2,[-1],449⟩,
  ⟨112,3,[-1],449⟩,
  ⟨112,4,[-1],605⟩,
  ⟨112,5,[-1],827⟩,
  ⟨112,6,[-1],924⟩,
  ⟨112,7,[-1],926⟩,
  ⟨112,8,[-1],733⟩,
  ⟨112,9,[-1],736⟩
]

private theorem refs_valid_21 : ∀ rec ∈ chunk_21, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_22 : List MiddleCertRecord := [
  ⟨112,10,[-1],734⟩,
  ⟨112,11,[-1],734⟩,
  ⟨112,12,[-1],1151⟩,
  ⟨112,13,[-1],1152⟩,
  ⟨112,14,[-1],1151⟩,
  ⟨112,15,[-1],1151⟩,
  ⟨114,0,[-1],335⟩,
  ⟨114,1,[-1],340⟩,
  ⟨114,2,[-1],338⟩,
  ⟨114,3,[-1],336⟩,
  ⟨114,4,[-1],335⟩,
  ⟨114,5,[-1],340⟩,
  ⟨114,6,[-1],338⟩,
  ⟨114,7,[-1],342⟩,
  ⟨114,8,[-1],233⟩,
  ⟨114,9,[-1],261⟩
]

private theorem refs_valid_22 : ∀ rec ∈ chunk_22, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_23 : List MiddleCertRecord := [
  ⟨114,10,[-1],244⟩,
  ⟨114,11,[-1],235⟩,
  ⟨114,12,[-1],233⟩,
  ⟨114,13,[-1],261⟩,
  ⟨114,14,[-1],244⟩,
  ⟨114,15,[-1],250⟩,
  ⟨114,16,[-1],834⟩,
  ⟨114,17,[-1],845⟩,
  ⟨114,18,[-1],839⟩,
  ⟨114,19,[-1],835⟩,
  ⟨114,20,[-1],834⟩,
  ⟨114,21,[-1],845⟩,
  ⟨114,22,[-1],839⟩,
  ⟨114,23,[-1],841⟩,
  ⟨114,24,[-1],1106⟩,
  ⟨114,25,[-1],1111⟩
]

private theorem refs_valid_23 : ∀ rec ∈ chunk_23, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_24 : List MiddleCertRecord := [
  ⟨114,26,[-1],1109⟩,
  ⟨114,27,[-1],1107⟩,
  ⟨114,28,[-1],1106⟩,
  ⟨114,29,[-1],1111⟩,
  ⟨114,30,[-1],1109⟩,
  ⟨114,31,[-1],1113⟩,
  ⟨116,0,[-1],236⟩,
  ⟨116,1,[-1],262⟩,
  ⟨116,2,[-1],235⟩,
  ⟨116,3,[-1],235⟩,
  ⟨116,4,[-1],236⟩,
  ⟨116,5,[-1],262⟩,
  ⟨116,6,[-1],235⟩,
  ⟨116,7,[-1],235⟩,
  ⟨116,8,[-1],236⟩,
  ⟨116,9,[-1],262⟩
]

private theorem refs_valid_24 : ∀ rec ∈ chunk_24, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_25 : List MiddleCertRecord := [
  ⟨116,10,[-1],235⟩,
  ⟨116,11,[-1],235⟩,
  ⟨116,12,[-1],236⟩,
  ⟨116,13,[-1],262⟩,
  ⟨116,14,[-1],235⟩,
  ⟨116,15,[-1],235⟩,
  ⟨116,16,[-1],543⟩,
  ⟨116,17,[-1],561⟩,
  ⟨116,18,[-1],542⟩,
  ⟨116,19,[-1],542⟩,
  ⟨116,20,[-1],543⟩,
  ⟨116,21,[-1],561⟩,
  ⟨116,22,[-1],542⟩,
  ⟨116,23,[-1],542⟩,
  ⟨116,24,[-1],956⟩,
  ⟨116,25,[-1],974⟩
]

private theorem refs_valid_25 : ∀ rec ∈ chunk_25, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_26 : List MiddleCertRecord := [
  ⟨116,26,[-1],955⟩,
  ⟨116,27,[-1],955⟩,
  ⟨116,28,[-1],956⟩,
  ⟨116,29,[-1],974⟩,
  ⟨116,30,[-1],955⟩,
  ⟨116,31,[-1],955⟩,
  ⟨116,32,[-1],236⟩,
  ⟨116,33,[-1],262⟩,
  ⟨116,34,[-1],241⟩,
  ⟨116,35,[-1],268⟩,
  ⟨116,36,[-1],236⟩,
  ⟨116,37,[-1],262⟩,
  ⟨116,38,[-1],241⟩,
  ⟨116,39,[-1],268⟩,
  ⟨116,40,[-1],236⟩,
  ⟨116,41,[-1],262⟩
]

private theorem refs_valid_26 : ∀ rec ∈ chunk_26, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_27 : List MiddleCertRecord := [
  ⟨116,42,[-1],241⟩,
  ⟨116,43,[-1],255⟩,
  ⟨116,44,[-1],236⟩,
  ⟨116,45,[-1],262⟩,
  ⟨116,46,[-1],241⟩,
  ⟨116,47,[-1],255⟩,
  ⟨116,48,[-1],543⟩,
  ⟨116,49,[-1],561⟩,
  ⟨116,50,[-1],547⟩,
  ⟨116,51,[-1],557⟩,
  ⟨116,52,[-1],543⟩,
  ⟨116,53,[-1],561⟩,
  ⟨116,54,[-1],547⟩,
  ⟨116,55,[-1],557⟩,
  ⟨116,56,[-1],956⟩,
  ⟨116,57,[-1],974⟩
]

private theorem refs_valid_27 : ∀ rec ∈ chunk_27, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_28 : List MiddleCertRecord := [
  ⟨116,58,[-1],960⟩,
  ⟨116,59,[-1],971⟩,
  ⟨116,60,[-1],956⟩,
  ⟨116,61,[-1],974⟩,
  ⟨116,62,[-1],960⟩,
  ⟨116,63,[-1],971⟩
]

private theorem refs_valid_28 : ∀ rec ∈ chunk_28, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent)
        (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def selectedRecords : List MiddleCertRecord := [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28].flatten

private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by
  decide +kernel

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([6] : List ℕ)))
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end RetRow6

open RetRow6

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([6] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)

#print axioms solution
