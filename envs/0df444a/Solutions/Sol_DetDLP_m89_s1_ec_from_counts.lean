-- Prove2me | solution 1 for DetDLP.m89_s1_ec_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:36:54.25+00:00
-- url     : https://prove2.me/submissions/ed222b51-b1e6-4041-8817-156f9250580c

import Theorems.Thm_DetDLP_m89_s1_ec_plan_prepare
import Theorems.Thm_DetDLP_m89_s1_ec_plan_enumerate
import Theorems.Thm_DetDLP_m89_s1_ec_plan_decode
import Theorems.Thm_DetDLP_m89_s1_word_pipe
import Definitions.Def_DetDLP_M89_MachineComp
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    CountOracle →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount)
       (M_dec : PrimitiveMachine) (out_dec : Fin M_dec.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let b := bitLen p
          let m := blockCount b
          ∃ F : Fin m → List E.toAffine.Point,
            (∀ i : Fin m, (F i).Nodup) ∧
            ecBase E (fun i => (F i).toFinset) ∧
            RunsWithin M_enum out_enum (encodeCurveInput p E) (encodeECFactorBlocks F)
              (mainSpaceBound C b) (mainSpaceBound C b) ∧
            ∀ X : E.toAffine.Point,
              (∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X) →
              ∃ A B : Fin m → E.toAffine.Point,
                (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
                (∑ i : Fin m, (A i + B i)) = X ∧
                RunsWithin M_dec out_dec
                  (Encoding.encodeList id [encodeCurveInput p E, encodeNatListBin (pointCoords X)])
                  (encodeECDecomp A B)
                  (mainSpaceBound C b) (polyBound C b)) := by
  classical
  intro Q
  obtain ⟨U,u,V,v,J,prep⟩ := m89_s1_ec_plan_prepare Q
  obtain ⟨R,r,I,enumerate⟩ := m89_s1_ec_plan_enumerate Q
  obtain ⟨D,d,H,decode⟩ := m89_s1_ec_plan_decode Q
  obtain ⟨N,a,Z,pipe'⟩ := m89_s1_word_pipe V v D d J H true
  obtain ⟨Cj, hj⟩ := stage1_complexity_dominance.2.2.1 J 0
  obtain ⟨M',o',K',pipeE⟩ := m89_s1_word_pipe U u R r (max J Cj) I false
  refine ⟨M',o',N,a,max K' Z,?_⟩
  intro p inst hp E instE
  have hp2 := (Fact.out : Nat.Prime p).two_le
  have hb : 1 ≤ bitLen p := by
    by_contra! hn
    have hzero : bitLen p = 0 := by omega
    have hpow := Nat.le_pow_clog (by decide : 1 < 2) p
    change p ≤ 2^(bitLen p) at hpow
    rw [hzero] at hpow
    omega
  obtain ⟨L,hok,hu,hv⟩ := prep p hp E
  obtain ⟨F,hF,hr⟩ := enumerate p hp E L hok
  have hbase : ecBase E (fun i => (F i).toFinset) := by
    cases L with
    | none => exact Or.inl ⟨hok, fun i => (hF i).2⟩
    | some pair =>
      rcases pair with ⟨t,s⟩
      rcases hok with ⟨h₁,h₂,rfl,hs⟩
      exact Or.inr ⟨h₁,h₂,s,hs,fun i => (hF i).2⟩
  have mono := stage1_complexity_dominance.1
  have hJS := (hj p 0 hp2 (by omega)).1
  have hu' := MachineComposition.runsWithin_mono hu (mono _ _ _ (le_max_left J Cj)).1 (hJS.trans (mono _ _ _ (le_max_right J Cj)).1)
  have henum := pipeE _ hb _ _ _ hu' hr
  refine ⟨F,fun i => (hF i).1,hbase,MachineComposition.runsWithin_mono henum (mono _ _ _ (le_max_left K' Z)).1 (mono _ _ _ (le_max_left K' Z)).1,?_⟩
  intro X hex
  have hmem (i) (x : E.toAffine.Point) : x ∈ F i ↔ x ∈ m89_ec_plan_block E L i := by
    rw [← (hF i).2, List.mem_toFinset]
  obtain ⟨A,B,hm,he,hd⟩ := decode p hp E L hok X (by simpa only [← hmem] using hex)
  refine ⟨A,B,?_,he,?_⟩
  · simpa only [hmem] using hm
  · exact MachineComposition.runsWithin_mono (pipe' _ hb _ _ _ (hv X) hd) (mono _ _ _ (le_max_right K' Z)).1 (mono _ _ _ (le_max_right K' Z)).2
