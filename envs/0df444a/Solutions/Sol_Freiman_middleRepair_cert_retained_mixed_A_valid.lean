-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_mixed_A_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T11:02:29.872186+00:00
-- url     : https://prove2.me/submissions/13cf6e0d-f4e8-48fc-b534-c4f4e275ba9f

import Definitions.Def_Freiman_middleRepairLedger
import Mathlib.Tactic.IntervalCases

open Freiman

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) :
    Decidable (middleCertPairValid C p direction) := by
  unfold middleCertPairValid
  infer_instance
local instance (C : MiddleCertCatalog) (p : MiddleCertProof) :
    Decidable (middleCertProofValid C p) := by
  cases p <;> unfold middleCertProofValid <;> infer_instance
local instance (C : MiddleCertCatalog) (r : MiddleCertRecord) :
    Decidable (middleCertRecordValid C r) := by
  unfold middleCertRecordValid
  infer_instance
local instance (C : MiddleCertCatalog) (g : MiddleCertGoal) (sp : MiddleCertSpec) :
    Decidable (middleCertGoalMatches C g sp) := by
  unfold middleCertGoalMatches
  infer_instance
local instance (C : MiddleCertCatalog) (goal branch : ℕ) (parent : ℤ) :
    Decidable (middleCertRecorded C goal branch parent) := by
  unfold middleCertRecorded
  infer_instance

local instance (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect)
    (rec : MiddleCertRecord) (parent : ℤ) : Decidable (middleRepairRecordValid C redirects rec parent) := by
  unfold middleRepairRecordValid
  infer_instance

set_option profiler true
set_option profiler.threshold 100
set_option linter.unusedSimpArgs false
namespace M8Sep10Retained_mixed_A

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
private def branches_1 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,681⟩,⟨false,false,626⟩],(.bound ⟨true,false,701⟩)),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨true,false,556⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,681⟩,⟨true,false,556⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,681⟩,⟨false,false,626⟩],.impossible),
([⟨false,false,633⟩,⟨false,false,681⟩,⟨false,true,556⟩,⟨true,true,681⟩,⟨true,true,626⟩],(.bound ⟨true,false,679⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,681⟩,⟨true,false,556⟩],(.bound ⟨false,false,701⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨false,false,626⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,681⟩,⟨true,false,556⟩],.impossible),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨false,false,681⟩,⟨false,true,556⟩],(.bound ⟨false,false,679⟩)),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,681⟩,⟨false,false,626⟩],.impossible),
([⟨false,false,633⟩,⟨true,true,681⟩,⟨true,true,626⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,681⟩,⟨false,false,626⟩],(.bound ⟨true,false,701⟩)),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨true,false,556⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,681⟩,⟨true,false,556⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,681⟩,⟨false,false,626⟩],.impossible),
([⟨true,true,633⟩,⟨false,true,681⟩,⟨false,true,556⟩,⟨true,true,681⟩,⟨true,true,626⟩],(.bound ⟨true,false,679⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,681⟩,⟨true,false,556⟩],(.bound ⟨false,false,701⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨false,false,626⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,681⟩,⟨true,false,556⟩],.impossible),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨false,false,681⟩,⟨false,true,556⟩],(.bound ⟨false,false,679⟩)),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,681⟩,⟨false,false,626⟩],.impossible),
([⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,626⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic)]
private theorem branches_1_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 1) = branches_1.map decodeBranch := by
  decide +kernel
private def branches_2 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,633⟩,⟨false,false,629⟩,⟨true,false,148⟩],.automatic),
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
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,633⟩,⟨true,false,629⟩,⟨true,true,90⟩],.automatic)]
private theorem branches_2_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 2) = branches_2.map decodeBranch := by
  decide +kernel
private def branches_3 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,681⟩,⟨true,false,176⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨false,false,681⟩,⟨true,false,176⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,681⟩,⟨true,false,176⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨false,false,681⟩,⟨true,false,176⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic)]
private theorem branches_3_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 3) = branches_3.map decodeBranch := by
  decide +kernel
private def branches_4 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,659⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,624⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,171⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,623⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,659⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,624⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,171⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,623⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,101⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,102⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,151⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,57⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,101⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,102⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,151⟩)),
([⟨false,false,296⟩,⟨false,false,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,57⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,113⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,150⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,272⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,55⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,113⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,150⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,272⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,55⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,651⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,166⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,291⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,620⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,651⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,166⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,291⟩)),
([⟨false,false,296⟩,⟨true,true,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,620⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,659⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,624⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,171⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,623⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,659⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,624⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,171⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨true,false,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,623⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,101⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,102⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,151⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,57⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,101⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,102⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,151⟩)),
([⟨true,true,296⟩,⟨false,true,641⟩,⟨false,true,611⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,57⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,113⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,150⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,272⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,55⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,113⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,150⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,272⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨false,false,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,55⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,651⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨false,false,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,166⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,291⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨false,false,634⟩,⟨true,true,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,620⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨true,false,432⟩],(.bound ⟨true,false,651⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨false,true,297⟩,⟨false,true,432⟩],(.bound ⟨true,false,166⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨false,false,452⟩],(.bound ⟨true,false,291⟩)),
([⟨true,true,296⟩,⟨true,false,641⟩,⟨true,true,674⟩,⟨true,true,634⟩,⟨true,false,297⟩,⟨true,true,452⟩],(.bound ⟨true,false,620⟩))]
private theorem branches_4_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 4) = branches_4.map decodeBranch := by
  decide +kernel
private def branches_5 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,22⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,594⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,162⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,6⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,22⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,594⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,162⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,6⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,12⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,7⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,3⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,703⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,12⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,7⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,3⟩)),
([⟨false,true,734⟩,⟨false,false,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,703⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,5⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,789⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,784⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,83⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,5⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,789⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,784⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,83⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,8⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,50⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,87⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,4⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,8⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,50⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,87⟩)),
([⟨false,true,734⟩,⟨true,true,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,4⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,22⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,594⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,162⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,6⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,22⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,594⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,162⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨true,false,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,6⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,12⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,7⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,3⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,703⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,12⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,7⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,3⟩)),
([⟨true,false,734⟩,⟨false,true,688⟩,⟨false,true,47⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,703⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,5⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,789⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,784⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,83⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,5⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,789⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,784⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨false,false,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,83⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,8⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨false,false,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,50⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,87⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨false,true,696⟩,⟨true,true,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,4⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨true,false,729⟩],(.bound ⟨false,false,8⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨false,true,744⟩,⟨false,true,729⟩],(.bound ⟨false,false,50⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨false,false,764⟩],(.bound ⟨false,false,87⟩)),
([⟨true,false,734⟩,⟨true,false,688⟩,⟨true,true,26⟩,⟨true,false,696⟩,⟨true,false,744⟩,⟨true,true,764⟩],(.bound ⟨false,false,4⟩))]
private theorem branches_5_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 5) = branches_5.map decodeBranch := by
  decide +kernel
private def branches_6 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
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
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic)]
private theorem branches_6_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 6) = branches_6.map decodeBranch := by
  decide +kernel
private def branches_7 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,223⟩,⟨false,false,255⟩,⟨true,false,509⟩,⟨false,false,216⟩,⟨false,false,265⟩,⟨true,false,427⟩],(.bound ⟨true,false,524⟩)),
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
([⟨true,true,223⟩,⟨true,false,255⟩,⟨true,true,553⟩,⟨true,true,216⟩,⟨true,false,265⟩,⟨true,true,447⟩],(.bound ⟨true,false,484⟩))]
private theorem branches_7_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 7) = branches_7.map decodeBranch := by
  decide +kernel
private def branches_8 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,true,634⟩,⟨false,false,568⟩,⟨true,false,176⟩,⟨false,true,567⟩,⟨false,false,642⟩,⟨true,false,606⟩],(.bound ⟨false,false,200⟩)),
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
([⟨true,false,634⟩,⟨true,false,568⟩,⟨true,true,109⟩,⟨true,false,567⟩,⟨true,false,642⟩,⟨true,true,669⟩],(.bound ⟨false,false,130⟩))]
private theorem branches_8_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 8) = branches_8.map decodeBranch := by
  decide +kernel
private def branches_9 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,681⟩,⟨true,false,176⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨false,false,681⟩,⟨true,false,176⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨false,false,681⟩,⟨true,false,176⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨false,false,681⟩,⟨true,false,176⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨false,false,681⟩,⟨false,true,176⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨true,true,681⟩,⟨false,false,109⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨false,false,629⟩,⟨true,false,432⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨false,false,629⟩,⟨false,true,432⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨true,true,629⟩,⟨false,false,452⟩],.automatic),
([⟨true,true,681⟩,⟨true,true,109⟩,⟨true,true,629⟩,⟨true,true,452⟩],.automatic)]
private theorem branches_9_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 9) = branches_9.map decodeBranch := by
  decide +kernel
private def branches_10 : List (List MiddleCertBoundRef × RefComparison) := [([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨false,false,629⟩,⟨true,false,148⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨false,false,629⟩,⟨false,true,148⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,90⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,681⟩,⟨true,false,556⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨false,false,681⟩,⟨false,true,556⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,681⟩,⟨false,false,626⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,90⟩,⟨true,true,681⟩,⟨true,true,626⟩],.automatic)]
private theorem branches_10_eq :
    middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData 10) = branches_10.map decodeBranch := by
  decide +kernel
private def parents_false : List (List MiddleCertBoundRef) := [[⟨true,false,583⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,433⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨true,false,516⟩],
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
[⟨false,false,24⟩,⟨true,true,633⟩,⟨true,false,695⟩,⟨true,false,567⟩,⟨true,true,110⟩,⟨true,false,681⟩,⟨true,false,696⟩,⟨true,true,723⟩]]
private theorem parents_false_eq : middleRepairCertParents false = parents_false.map (middleCertBounds middleCertData) := by
  decide +kernel
private def parents_true : List (List MiddleCertBoundRef) := [[⟨true,false,583⟩,⟨false,false,633⟩,⟨false,false,222⟩,⟨true,false,517⟩,⟨false,false,629⟩,⟨true,false,432⟩],
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
[⟨false,false,24⟩,⟨true,true,633⟩,⟨true,false,681⟩,⟨true,true,109⟩,⟨true,false,695⟩,⟨true,true,724⟩]]
private theorem parents_true_eq : middleRepairCertParents true = parents_true.map (middleCertBounds middleCertData) := by
  decide +kernel

private def cachedBranches : ℕ → List (List MiddleCertBoundRef × RefComparison)
  | 1 => branches_1
  | 2 => branches_2
  | 3 => branches_3
  | 4 => branches_4
  | 5 => branches_5
  | 6 => branches_6
  | 7 => branches_7
  | 8 => branches_8
  | 9 => branches_9
  | 10 => branches_10
  | _ => []
private def cachedParents (p : Bool) : List (List MiddleCertBoundRef) := if p then parents_true else parents_false
private def refComplement (b : MiddleCertBoundRef) : MiddleCertBoundRef := ⟨!b.lower,!b.strict,b.threshold⟩
private def refConditions (rec : MiddleCertRecord) (parent : ℤ) : List MiddleCertBoundRef :=
  let g := middleCertGoal middleCertData rec.goal
  let b := (cachedBranches rec.goal)[rec.branch]?.getD ([],.impossible)
  g.hypotheses ++ b.1 ++
    (if parent < 0 then [] else (cachedParents (middleCertParity g.family))[parent.toNat]?.getD []) ++
    (match b.2 with | .bound t => [refComplement t] | _ => [])

private def selectedGoals : List ℕ := [1,2,3,4,5,6,7,8,9,10]
private theorem conditions_eq (rec : MiddleCertRecord) (parent : ℤ)
    (hg : rec.goal ∈ selectedGoals) :
    middleRepairCertConditions middleCertData rec parent = middleCertBounds middleCertData (refConditions rec parent) := by
  have hp (p : Bool) : middleRepairCertParents p = (cachedParents p).map (middleCertBounds middleCertData) := by
    cases p
    · exact parents_false_eq
    · exact parents_true_eq
  have hb : middleRepairCertGoalBranches middleCertData (middleCertGoal middleCertData rec.goal) =
      (cachedBranches rec.goal).map decodeBranch := by
    simp only [selectedGoals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
    · simpa only [hg, cachedBranches] using branches_1_eq
    · simpa only [hg, cachedBranches] using branches_2_eq
    · simpa only [hg, cachedBranches] using branches_3_eq
    · simpa only [hg, cachedBranches] using branches_4_eq
    · simpa only [hg, cachedBranches] using branches_5_eq
    · simpa only [hg, cachedBranches] using branches_6_eq
    · simpa only [hg, cachedBranches] using branches_7_eq
    · simpa only [hg, cachedBranches] using branches_8_eq
    · simpa only [hg, cachedBranches] using branches_9_eq
    · simpa only [hg, cachedBranches] using branches_10_eq
  have hget : ((cachedBranches rec.goal).map decodeBranch)[rec.branch]?.getD ([],.impossible) =
      decodeBranch ((cachedBranches rec.goal)[rec.branch]?.getD ([],.impossible)) := by
    simp only [List.getElem?_map]
    exact Option.getD_map decodeBranch ([],.impossible) ((cachedBranches rec.goal)[rec.branch]?)
  have hpget (p : Bool) : ((cachedParents p).map (middleCertBounds middleCertData))[parent.toNat]?.getD [] =
      middleCertBounds middleCertData ((cachedParents p)[parent.toNat]?.getD []) := by
    simp only [List.getElem?_map]
    exact Option.getD_map (middleCertBounds middleCertData) [] ((cachedParents p)[parent.toNat]?)
  simp only [middleRepairCertConditions, middleRepairCertBranch, hb, hget, decodeBranch,
    hp, hpget, refConditions, middleCertBounds, List.map_append]
  split_ifs <;>
    cases hc : ((cachedBranches rec.goal)[rec.branch]?.getD ([],RefComparison.impossible)).2 <;>
    simp [decodeComparison, middleCertBounds, refComplement, middleCertBound, lowerHistoryComplement]
local instance (C : MiddleCertCatalog) (bs : List MiddleCertBoundRef) (p : MiddleCertProof) : Decidable (proofReady C bs p) := by
  cases p <;> unfold proofReady pairReady refMatches refStrict <;> infer_instance
private theorem from_refs (rec : MiddleCertRecord) (parent : ℤ)
    (hg : rec.goal ∈ selectedGoals)
    (hn : middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none)
    (hf : proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof)) :
    middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  have he : middleRepairEffectiveProof middleCertData middleRepairRedirects rec parent =
      adaptProof middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
    simp only [middleRepairEffectiveProof, hn, conditions_eq rec parent hg]
    cases middleCertProof middleCertData rec.proof <;> rfl
  simpa only [middleRepairRecordValid, he, conditions_eq rec parent hg] using proof_ready _ _ _ hf

private def selectedRecords : List MiddleCertRecord := [
  ⟨1,2,[-1],917⟩,
  ⟨1,4,[-1],222⟩,
  ⟨1,6,[-1],917⟩,
  ⟨1,7,[-1],917⟩,
  ⟨1,8,[-1],917⟩,
  ⟨1,12,[-1],917⟩,
  ⟨1,13,[-1],917⟩,
  ⟨1,14,[-1],814⟩,
  ⟨1,18,[-1],917⟩,
  ⟨1,20,[-1],739⟩,
  ⟨1,22,[-1],739⟩,
  ⟨1,23,[-1],917⟩,
  ⟨1,24,[-1],917⟩,
  ⟨1,28,[-1],739⟩,
  ⟨1,29,[-1],917⟩,
  ⟨1,30,[-1],739⟩,
  ⟨2,1,[-1],172⟩,
  ⟨2,2,[-1],1218⟩,
  ⟨2,3,[-1],1218⟩,
  ⟨2,5,[-1],739⟩,
  ⟨2,6,[-1],739⟩,
  ⟨2,7,[-1],739⟩,
  ⟨2,11,[-1],1218⟩,
  ⟨2,15,[-1],739⟩,
  ⟨2,16,[-1],1218⟩,
  ⟨2,17,[-1],1218⟩,
  ⟨2,19,[-1],699⟩,
  ⟨2,20,[-1],739⟩,
  ⟨2,21,[-1],739⟩,
  ⟨2,23,[-1],739⟩,
  ⟨2,25,[-1],1218⟩,
  ⟨2,29,[-1],739⟩,
  ⟨4,0,[-1],459⟩,
  ⟨4,1,[-1],466⟩,
  ⟨4,2,[-1],458⟩,
  ⟨4,3,[-1],458⟩,
  ⟨4,4,[-1],741⟩,
  ⟨4,5,[-1],752⟩,
  ⟨4,6,[-1],740⟩,
  ⟨4,7,[-1],740⟩,
  ⟨4,8,[-1],779⟩,
  ⟨4,9,[-1],789⟩,
  ⟨4,10,[-1],778⟩,
  ⟨4,11,[-1],778⟩,
  ⟨4,12,[-1],741⟩,
  ⟨4,13,[-1],752⟩,
  ⟨4,14,[-1],740⟩,
  ⟨4,15,[-1],740⟩,
  ⟨4,16,[-1],725⟩,
  ⟨4,17,[-1],732⟩,
  ⟨4,18,[-1],724⟩,
  ⟨4,19,[-1],724⟩,
  ⟨4,20,[-1],725⟩,
  ⟨4,21,[-1],732⟩,
  ⟨4,22,[-1],724⟩,
  ⟨4,23,[-1],724⟩,
  ⟨4,24,[-1],1155⟩,
  ⟨4,25,[-1],1162⟩,
  ⟨4,26,[-1],1154⟩,
  ⟨4,27,[-1],1154⟩,
  ⟨4,28,[-1],1155⟩,
  ⟨4,29,[-1],1162⟩,
  ⟨4,30,[-1],1154⟩,
  ⟨4,31,[-1],1154⟩,
  ⟨4,32,[-1],459⟩,
  ⟨4,33,[-1],466⟩,
  ⟨4,34,[-1],462⟩,
  ⟨4,35,[-1],463⟩,
  ⟨4,36,[-1],741⟩,
  ⟨4,37,[-1],752⟩,
  ⟨4,38,[-1],742⟩,
  ⟨4,39,[-1],748⟩,
  ⟨4,40,[-1],779⟩,
  ⟨4,41,[-1],789⟩,
  ⟨4,42,[-1],782⟩,
  ⟨4,43,[-1],784⟩,
  ⟨4,44,[-1],741⟩,
  ⟨4,45,[-1],752⟩,
  ⟨4,46,[-1],742⟩,
  ⟨4,47,[-1],746⟩,
  ⟨4,48,[-1],725⟩,
  ⟨4,49,[-1],732⟩,
  ⟨4,50,[-1],728⟩,
  ⟨4,51,[-1],729⟩,
  ⟨4,52,[-1],725⟩,
  ⟨4,53,[-1],732⟩,
  ⟨4,54,[-1],728⟩,
  ⟨4,55,[-1],729⟩,
  ⟨4,56,[-1],1155⟩,
  ⟨4,57,[-1],1162⟩,
  ⟨4,58,[-1],1158⟩,
  ⟨4,59,[-1],1159⟩,
  ⟨4,60,[-1],1155⟩,
  ⟨4,61,[-1],1162⟩,
  ⟨4,62,[-1],1158⟩,
  ⟨4,63,[-1],1159⟩,
  ⟨5,0,[-1],496⟩,
  ⟨5,1,[-1],796⟩,
  ⟨5,2,[-1],1124⟩,
  ⟨5,3,[-1],818⟩,
  ⟨5,4,[-1],496⟩,
  ⟨5,5,[-1],796⟩,
  ⟨5,6,[-1],1124⟩,
  ⟨5,7,[-1],818⟩,
  ⟨5,8,[-1],496⟩,
  ⟨5,9,[-1],594⟩,
  ⟨5,10,[-1],1124⟩,
  ⟨5,11,[-1],818⟩,
  ⟨5,12,[-1],496⟩,
  ⟨5,13,[-1],594⟩,
  ⟨5,14,[-1],1124⟩,
  ⟨5,15,[-1],818⟩,
  ⟨5,16,[-1],496⟩,
  ⟨5,17,[-1],901⟩,
  ⟨5,18,[-1],1124⟩,
  ⟨5,19,[-1],818⟩,
  ⟨5,20,[-1],496⟩,
  ⟨5,21,[-1],901⟩,
  ⟨5,22,[-1],1124⟩,
  ⟨5,23,[-1],818⟩,
  ⟨5,24,[-1],496⟩,
  ⟨5,25,[-1],665⟩,
  ⟨5,26,[-1],1124⟩,
  ⟨5,27,[-1],818⟩,
  ⟨5,28,[-1],496⟩,
  ⟨5,29,[-1],665⟩,
  ⟨5,30,[-1],1124⟩,
  ⟨5,31,[-1],818⟩,
  ⟨5,32,[-1],776⟩,
  ⟨5,33,[-1],776⟩,
  ⟨5,34,[-1],1124⟩,
  ⟨5,35,[-1],818⟩,
  ⟨5,36,[-1],776⟩,
  ⟨5,37,[-1],776⟩,
  ⟨5,38,[-1],1124⟩,
  ⟨5,39,[-1],818⟩,
  ⟨5,40,[-1],776⟩,
  ⟨5,41,[-1],776⟩,
  ⟨5,42,[-1],1124⟩,
  ⟨5,43,[-1],818⟩,
  ⟨5,44,[-1],776⟩,
  ⟨5,45,[-1],776⟩,
  ⟨5,46,[-1],1124⟩,
  ⟨5,47,[-1],818⟩,
  ⟨5,48,[-1],776⟩,
  ⟨5,49,[-1],776⟩,
  ⟨5,50,[-1],1124⟩,
  ⟨5,51,[-1],818⟩,
  ⟨5,52,[-1],776⟩,
  ⟨5,53,[-1],776⟩,
  ⟨5,54,[-1],1124⟩,
  ⟨5,55,[-1],818⟩,
  ⟨5,56,[-1],776⟩,
  ⟨5,57,[-1],776⟩,
  ⟨5,58,[-1],1124⟩,
  ⟨5,59,[-1],818⟩,
  ⟨5,60,[-1],776⟩,
  ⟨5,61,[-1],776⟩,
  ⟨5,62,[-1],1124⟩,
  ⟨5,63,[-1],818⟩,
  ⟨7,0,[-1],780⟩,
  ⟨7,1,[-1],780⟩,
  ⟨7,2,[-1],780⟩,
  ⟨7,3,[-1],780⟩,
  ⟨7,4,[-1],780⟩,
  ⟨7,5,[-1],780⟩,
  ⟨7,6,[-1],780⟩,
  ⟨7,7,[-1],780⟩,
  ⟨7,8,[-1],787⟩,
  ⟨7,9,[-1],787⟩,
  ⟨7,10,[-1],787⟩,
  ⟨7,11,[-1],787⟩,
  ⟨7,12,[-1],787⟩,
  ⟨7,13,[-1],787⟩,
  ⟨7,14,[-1],787⟩,
  ⟨7,15,[-1],787⟩,
  ⟨7,16,[-1],781⟩,
  ⟨7,17,[-1],781⟩,
  ⟨7,18,[-1],781⟩,
  ⟨7,19,[-1],781⟩,
  ⟨7,20,[-1],783⟩,
  ⟨7,21,[-1],783⟩,
  ⟨7,22,[-1],783⟩,
  ⟨7,23,[-1],783⟩,
  ⟨7,24,[-1],781⟩,
  ⟨7,25,[-1],781⟩,
  ⟨7,26,[-1],781⟩,
  ⟨7,27,[-1],781⟩,
  ⟨7,28,[-1],790⟩,
  ⟨7,29,[-1],786⟩,
  ⟨7,30,[-1],785⟩,
  ⟨7,31,[-1],788⟩,
  ⟨7,32,[-1],780⟩,
  ⟨7,33,[-1],780⟩,
  ⟨7,34,[-1],780⟩,
  ⟨7,35,[-1],780⟩,
  ⟨7,36,[-1],780⟩,
  ⟨7,37,[-1],780⟩,
  ⟨7,38,[-1],780⟩,
  ⟨7,39,[-1],780⟩,
  ⟨7,40,[-1],787⟩,
  ⟨7,41,[-1],787⟩,
  ⟨7,42,[-1],787⟩,
  ⟨7,43,[-1],787⟩,
  ⟨7,44,[-1],787⟩,
  ⟨7,45,[-1],787⟩,
  ⟨7,46,[-1],787⟩,
  ⟨7,47,[-1],787⟩,
  ⟨7,48,[-1],781⟩,
  ⟨7,49,[-1],781⟩,
  ⟨7,50,[-1],781⟩,
  ⟨7,51,[-1],781⟩,
  ⟨7,52,[-1],783⟩,
  ⟨7,53,[-1],783⟩,
  ⟨7,54,[-1],783⟩,
  ⟨7,55,[-1],783⟩,
  ⟨7,56,[-1],781⟩,
  ⟨7,57,[-1],781⟩,
  ⟨7,58,[-1],781⟩,
  ⟨7,59,[-1],781⟩,
  ⟨7,60,[-1],790⟩,
  ⟨7,61,[-1],786⟩,
  ⟨7,62,[-1],785⟩,
  ⟨7,63,[-1],788⟩,
  ⟨8,0,[-1],4⟩,
  ⟨8,1,[-1],7⟩,
  ⟨8,2,[-1],3⟩,
  ⟨8,3,[-1],3⟩,
  ⟨8,4,[-1],761⟩,
  ⟨8,5,[-1],766⟩,
  ⟨8,6,[-1],760⟩,
  ⟨8,7,[-1],760⟩,
  ⟨8,8,[-1],589⟩,
  ⟨8,9,[-1],708⟩,
  ⟨8,10,[-1],597⟩,
  ⟨8,11,[-1],1005⟩,
  ⟨8,12,[-1],761⟩,
  ⟨8,13,[-1],766⟩,
  ⟨8,14,[-1],760⟩,
  ⟨8,15,[-1],760⟩,
  ⟨8,16,[-1],769⟩,
  ⟨8,17,[-1],772⟩,
  ⟨8,18,[-1],768⟩,
  ⟨8,19,[-1],768⟩,
  ⟨8,20,[-1],769⟩,
  ⟨8,21,[-1],772⟩,
  ⟨8,22,[-1],768⟩,
  ⟨8,23,[-1],768⟩,
  ⟨8,24,[-1],683⟩,
  ⟨8,25,[-1],686⟩,
  ⟨8,26,[-1],682⟩,
  ⟨8,27,[-1],682⟩,
  ⟨8,28,[-1],683⟩,
  ⟨8,29,[-1],686⟩,
  ⟨8,30,[-1],682⟩,
  ⟨8,31,[-1],682⟩,
  ⟨8,32,[-1],4⟩,
  ⟨8,33,[-1],7⟩,
  ⟨8,34,[-1],2⟩,
  ⟨8,35,[-1],2⟩,
  ⟨8,36,[-1],761⟩,
  ⟨8,37,[-1],766⟩,
  ⟨8,38,[-1],759⟩,
  ⟨8,39,[-1],759⟩,
  ⟨8,40,[-1],589⟩,
  ⟨8,41,[-1],708⟩,
  ⟨8,42,[-1],596⟩,
  ⟨8,43,[-1],1004⟩,
  ⟨8,44,[-1],761⟩,
  ⟨8,45,[-1],766⟩,
  ⟨8,46,[-1],759⟩,
  ⟨8,47,[-1],759⟩,
  ⟨8,48,[-1],769⟩,
  ⟨8,49,[-1],772⟩,
  ⟨8,50,[-1],767⟩,
  ⟨8,51,[-1],767⟩,
  ⟨8,52,[-1],769⟩,
  ⟨8,53,[-1],772⟩,
  ⟨8,54,[-1],767⟩,
  ⟨8,55,[-1],767⟩,
  ⟨8,56,[-1],683⟩,
  ⟨8,57,[-1],686⟩,
  ⟨8,58,[-1],681⟩,
  ⟨8,59,[-1],681⟩,
  ⟨8,60,[-1],683⟩,
  ⟨8,61,[-1],686⟩,
  ⟨8,62,[-1],681⟩,
  ⟨8,63,[-1],681⟩]
private theorem selected_goals : ∀ r ∈ selectedRecords, r.goal ∈ selectedGoals := by decide +kernel
private theorem records_eq :
    middleCertData.records.filter (fun r => decide ((middleCertGoal middleCertData r.goal).family ∈ ([0] : List ℕ))) = selectedRecords := by
  decide +kernel

private def chunk_0 : List MiddleCertRecord := [
  ⟨1,2,[-1],917⟩,
  ⟨1,4,[-1],222⟩,
  ⟨1,6,[-1],917⟩,
  ⟨1,7,[-1],917⟩,
  ⟨1,8,[-1],917⟩,
  ⟨1,12,[-1],917⟩,
  ⟨1,13,[-1],917⟩,
  ⟨1,14,[-1],814⟩,
  ⟨1,18,[-1],917⟩,
  ⟨1,20,[-1],739⟩,
  ⟨1,22,[-1],739⟩,
  ⟨1,23,[-1],917⟩,
  ⟨1,24,[-1],917⟩,
  ⟨1,28,[-1],739⟩,
  ⟨1,29,[-1],917⟩,
  ⟨1,30,[-1],739⟩]
private theorem refs_valid_0 : ∀ rec ∈ chunk_0, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨2,1,[-1],172⟩,
  ⟨2,2,[-1],1218⟩,
  ⟨2,3,[-1],1218⟩,
  ⟨2,5,[-1],739⟩,
  ⟨2,6,[-1],739⟩,
  ⟨2,7,[-1],739⟩,
  ⟨2,11,[-1],1218⟩,
  ⟨2,15,[-1],739⟩,
  ⟨2,16,[-1],1218⟩,
  ⟨2,17,[-1],1218⟩,
  ⟨2,19,[-1],699⟩,
  ⟨2,20,[-1],739⟩,
  ⟨2,21,[-1],739⟩,
  ⟨2,23,[-1],739⟩,
  ⟨2,25,[-1],1218⟩,
  ⟨2,29,[-1],739⟩]
private theorem refs_valid_1 : ∀ rec ∈ chunk_1, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨4,0,[-1],459⟩,
  ⟨4,1,[-1],466⟩,
  ⟨4,2,[-1],458⟩,
  ⟨4,3,[-1],458⟩,
  ⟨4,4,[-1],741⟩,
  ⟨4,5,[-1],752⟩,
  ⟨4,6,[-1],740⟩,
  ⟨4,7,[-1],740⟩,
  ⟨4,8,[-1],779⟩,
  ⟨4,9,[-1],789⟩,
  ⟨4,10,[-1],778⟩,
  ⟨4,11,[-1],778⟩,
  ⟨4,12,[-1],741⟩,
  ⟨4,13,[-1],752⟩,
  ⟨4,14,[-1],740⟩,
  ⟨4,15,[-1],740⟩]
private theorem refs_valid_2 : ∀ rec ∈ chunk_2, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨4,16,[-1],725⟩,
  ⟨4,17,[-1],732⟩,
  ⟨4,18,[-1],724⟩,
  ⟨4,19,[-1],724⟩,
  ⟨4,20,[-1],725⟩,
  ⟨4,21,[-1],732⟩,
  ⟨4,22,[-1],724⟩,
  ⟨4,23,[-1],724⟩,
  ⟨4,24,[-1],1155⟩,
  ⟨4,25,[-1],1162⟩,
  ⟨4,26,[-1],1154⟩,
  ⟨4,27,[-1],1154⟩,
  ⟨4,28,[-1],1155⟩,
  ⟨4,29,[-1],1162⟩,
  ⟨4,30,[-1],1154⟩,
  ⟨4,31,[-1],1154⟩]
private theorem refs_valid_3 : ∀ rec ∈ chunk_3, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨4,32,[-1],459⟩,
  ⟨4,33,[-1],466⟩,
  ⟨4,34,[-1],462⟩,
  ⟨4,35,[-1],463⟩,
  ⟨4,36,[-1],741⟩,
  ⟨4,37,[-1],752⟩,
  ⟨4,38,[-1],742⟩,
  ⟨4,39,[-1],748⟩,
  ⟨4,40,[-1],779⟩,
  ⟨4,41,[-1],789⟩,
  ⟨4,42,[-1],782⟩,
  ⟨4,43,[-1],784⟩,
  ⟨4,44,[-1],741⟩,
  ⟨4,45,[-1],752⟩,
  ⟨4,46,[-1],742⟩,
  ⟨4,47,[-1],746⟩]
private theorem refs_valid_4 : ∀ rec ∈ chunk_4, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨4,48,[-1],725⟩,
  ⟨4,49,[-1],732⟩,
  ⟨4,50,[-1],728⟩,
  ⟨4,51,[-1],729⟩,
  ⟨4,52,[-1],725⟩,
  ⟨4,53,[-1],732⟩,
  ⟨4,54,[-1],728⟩,
  ⟨4,55,[-1],729⟩,
  ⟨4,56,[-1],1155⟩,
  ⟨4,57,[-1],1162⟩,
  ⟨4,58,[-1],1158⟩,
  ⟨4,59,[-1],1159⟩,
  ⟨4,60,[-1],1155⟩,
  ⟨4,61,[-1],1162⟩,
  ⟨4,62,[-1],1158⟩,
  ⟨4,63,[-1],1159⟩]
private theorem refs_valid_5 : ∀ rec ∈ chunk_5, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨5,0,[-1],496⟩,
  ⟨5,1,[-1],796⟩,
  ⟨5,2,[-1],1124⟩,
  ⟨5,3,[-1],818⟩,
  ⟨5,4,[-1],496⟩,
  ⟨5,5,[-1],796⟩,
  ⟨5,6,[-1],1124⟩,
  ⟨5,7,[-1],818⟩,
  ⟨5,8,[-1],496⟩,
  ⟨5,9,[-1],594⟩,
  ⟨5,10,[-1],1124⟩,
  ⟨5,11,[-1],818⟩,
  ⟨5,12,[-1],496⟩,
  ⟨5,13,[-1],594⟩,
  ⟨5,14,[-1],1124⟩,
  ⟨5,15,[-1],818⟩]
private theorem refs_valid_6 : ∀ rec ∈ chunk_6, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨5,16,[-1],496⟩,
  ⟨5,17,[-1],901⟩,
  ⟨5,18,[-1],1124⟩,
  ⟨5,19,[-1],818⟩,
  ⟨5,20,[-1],496⟩,
  ⟨5,21,[-1],901⟩,
  ⟨5,22,[-1],1124⟩,
  ⟨5,23,[-1],818⟩,
  ⟨5,24,[-1],496⟩,
  ⟨5,25,[-1],665⟩,
  ⟨5,26,[-1],1124⟩,
  ⟨5,27,[-1],818⟩,
  ⟨5,28,[-1],496⟩,
  ⟨5,29,[-1],665⟩,
  ⟨5,30,[-1],1124⟩,
  ⟨5,31,[-1],818⟩]
private theorem refs_valid_7 : ∀ rec ∈ chunk_7, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨5,32,[-1],776⟩,
  ⟨5,33,[-1],776⟩,
  ⟨5,34,[-1],1124⟩,
  ⟨5,35,[-1],818⟩,
  ⟨5,36,[-1],776⟩,
  ⟨5,37,[-1],776⟩,
  ⟨5,38,[-1],1124⟩,
  ⟨5,39,[-1],818⟩,
  ⟨5,40,[-1],776⟩,
  ⟨5,41,[-1],776⟩,
  ⟨5,42,[-1],1124⟩,
  ⟨5,43,[-1],818⟩,
  ⟨5,44,[-1],776⟩,
  ⟨5,45,[-1],776⟩,
  ⟨5,46,[-1],1124⟩,
  ⟨5,47,[-1],818⟩]
private theorem refs_valid_8 : ∀ rec ∈ chunk_8, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨5,48,[-1],776⟩,
  ⟨5,49,[-1],776⟩,
  ⟨5,50,[-1],1124⟩,
  ⟨5,51,[-1],818⟩,
  ⟨5,52,[-1],776⟩,
  ⟨5,53,[-1],776⟩,
  ⟨5,54,[-1],1124⟩,
  ⟨5,55,[-1],818⟩,
  ⟨5,56,[-1],776⟩,
  ⟨5,57,[-1],776⟩,
  ⟨5,58,[-1],1124⟩,
  ⟨5,59,[-1],818⟩,
  ⟨5,60,[-1],776⟩,
  ⟨5,61,[-1],776⟩,
  ⟨5,62,[-1],1124⟩,
  ⟨5,63,[-1],818⟩]
private theorem refs_valid_9 : ∀ rec ∈ chunk_9, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨7,0,[-1],780⟩,
  ⟨7,1,[-1],780⟩,
  ⟨7,2,[-1],780⟩,
  ⟨7,3,[-1],780⟩,
  ⟨7,4,[-1],780⟩,
  ⟨7,5,[-1],780⟩,
  ⟨7,6,[-1],780⟩,
  ⟨7,7,[-1],780⟩,
  ⟨7,8,[-1],787⟩,
  ⟨7,9,[-1],787⟩,
  ⟨7,10,[-1],787⟩,
  ⟨7,11,[-1],787⟩,
  ⟨7,12,[-1],787⟩,
  ⟨7,13,[-1],787⟩,
  ⟨7,14,[-1],787⟩,
  ⟨7,15,[-1],787⟩]
private theorem refs_valid_10 : ∀ rec ∈ chunk_10, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨7,16,[-1],781⟩,
  ⟨7,17,[-1],781⟩,
  ⟨7,18,[-1],781⟩,
  ⟨7,19,[-1],781⟩,
  ⟨7,20,[-1],783⟩,
  ⟨7,21,[-1],783⟩,
  ⟨7,22,[-1],783⟩,
  ⟨7,23,[-1],783⟩,
  ⟨7,24,[-1],781⟩,
  ⟨7,25,[-1],781⟩,
  ⟨7,26,[-1],781⟩,
  ⟨7,27,[-1],781⟩,
  ⟨7,28,[-1],790⟩,
  ⟨7,29,[-1],786⟩,
  ⟨7,30,[-1],785⟩,
  ⟨7,31,[-1],788⟩]
private theorem refs_valid_11 : ∀ rec ∈ chunk_11, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨7,32,[-1],780⟩,
  ⟨7,33,[-1],780⟩,
  ⟨7,34,[-1],780⟩,
  ⟨7,35,[-1],780⟩,
  ⟨7,36,[-1],780⟩,
  ⟨7,37,[-1],780⟩,
  ⟨7,38,[-1],780⟩,
  ⟨7,39,[-1],780⟩,
  ⟨7,40,[-1],787⟩,
  ⟨7,41,[-1],787⟩,
  ⟨7,42,[-1],787⟩,
  ⟨7,43,[-1],787⟩,
  ⟨7,44,[-1],787⟩,
  ⟨7,45,[-1],787⟩,
  ⟨7,46,[-1],787⟩,
  ⟨7,47,[-1],787⟩]
private theorem refs_valid_12 : ∀ rec ∈ chunk_12, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨7,48,[-1],781⟩,
  ⟨7,49,[-1],781⟩,
  ⟨7,50,[-1],781⟩,
  ⟨7,51,[-1],781⟩,
  ⟨7,52,[-1],783⟩,
  ⟨7,53,[-1],783⟩,
  ⟨7,54,[-1],783⟩,
  ⟨7,55,[-1],783⟩,
  ⟨7,56,[-1],781⟩,
  ⟨7,57,[-1],781⟩,
  ⟨7,58,[-1],781⟩,
  ⟨7,59,[-1],781⟩,
  ⟨7,60,[-1],790⟩,
  ⟨7,61,[-1],786⟩,
  ⟨7,62,[-1],785⟩,
  ⟨7,63,[-1],788⟩]
private theorem refs_valid_13 : ∀ rec ∈ chunk_13, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨8,0,[-1],4⟩,
  ⟨8,1,[-1],7⟩,
  ⟨8,2,[-1],3⟩,
  ⟨8,3,[-1],3⟩,
  ⟨8,4,[-1],761⟩,
  ⟨8,5,[-1],766⟩,
  ⟨8,6,[-1],760⟩,
  ⟨8,7,[-1],760⟩,
  ⟨8,8,[-1],589⟩,
  ⟨8,9,[-1],708⟩,
  ⟨8,10,[-1],597⟩,
  ⟨8,11,[-1],1005⟩,
  ⟨8,12,[-1],761⟩,
  ⟨8,13,[-1],766⟩,
  ⟨8,14,[-1],760⟩,
  ⟨8,15,[-1],760⟩]
private theorem refs_valid_14 : ∀ rec ∈ chunk_14, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨8,16,[-1],769⟩,
  ⟨8,17,[-1],772⟩,
  ⟨8,18,[-1],768⟩,
  ⟨8,19,[-1],768⟩,
  ⟨8,20,[-1],769⟩,
  ⟨8,21,[-1],772⟩,
  ⟨8,22,[-1],768⟩,
  ⟨8,23,[-1],768⟩,
  ⟨8,24,[-1],683⟩,
  ⟨8,25,[-1],686⟩,
  ⟨8,26,[-1],682⟩,
  ⟨8,27,[-1],682⟩,
  ⟨8,28,[-1],683⟩,
  ⟨8,29,[-1],686⟩,
  ⟨8,30,[-1],682⟩,
  ⟨8,31,[-1],682⟩]
private theorem refs_valid_15 : ∀ rec ∈ chunk_15, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨8,32,[-1],4⟩,
  ⟨8,33,[-1],7⟩,
  ⟨8,34,[-1],2⟩,
  ⟨8,35,[-1],2⟩,
  ⟨8,36,[-1],761⟩,
  ⟨8,37,[-1],766⟩,
  ⟨8,38,[-1],759⟩,
  ⟨8,39,[-1],759⟩,
  ⟨8,40,[-1],589⟩,
  ⟨8,41,[-1],708⟩,
  ⟨8,42,[-1],596⟩,
  ⟨8,43,[-1],1004⟩,
  ⟨8,44,[-1],761⟩,
  ⟨8,45,[-1],766⟩,
  ⟨8,46,[-1],759⟩,
  ⟨8,47,[-1],759⟩]
private theorem refs_valid_16 : ∀ rec ∈ chunk_16, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨8,48,[-1],769⟩,
  ⟨8,49,[-1],772⟩,
  ⟨8,50,[-1],767⟩,
  ⟨8,51,[-1],767⟩,
  ⟨8,52,[-1],769⟩,
  ⟨8,53,[-1],772⟩,
  ⟨8,54,[-1],767⟩,
  ⟨8,55,[-1],767⟩,
  ⟨8,56,[-1],683⟩,
  ⟨8,57,[-1],686⟩,
  ⟨8,58,[-1],681⟩,
  ⟨8,59,[-1],681⟩,
  ⟨8,60,[-1],683⟩,
  ⟨8,61,[-1],686⟩,
  ⟨8,62,[-1],681⟩,
  ⟨8,63,[-1],681⟩]
private theorem refs_valid_17 : ∀ rec ∈ chunk_17, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  decide +kernel
private theorem chunks_eq : ([chunk_0,chunk_1,chunk_2,chunk_3,chunk_4,chunk_5,chunk_6,chunk_7,chunk_8,chunk_9,chunk_10,chunk_11,chunk_12,chunk_13,chunk_14,chunk_15,chunk_16,chunk_17] : List (List MiddleCertRecord)).flatten = selectedRecords := by
  decide +kernel
private theorem refs_valid : ∀ rec ∈ selectedRecords, ∀ parent ∈ rec.parents,
    middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      proofReady middleCertData (refConditions rec parent) (middleCertProof middleCertData rec.proof) := by
  intro rec hr
  rw [← chunks_eq] at hr
  obtain ⟨chunk,hc,hr⟩ := List.mem_flatten.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
end M8Sep10Retained_mixed_A

open M8Sep10Retained_mixed_A

theorem solution :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈ ([0] : List ℕ) →
      ∀ parent ∈ rec.parents,
        middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
        middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr hfamily parent hp hn
  have hs : rec ∈ selectedRecords := by
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr,by simpa only [decide_eq_true_eq] using hfamily⟩
  exact from_refs rec parent (selected_goals rec hs) hn (refs_valid rec hs parent hp hn)
#print axioms solution
