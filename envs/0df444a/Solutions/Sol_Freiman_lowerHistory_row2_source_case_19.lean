-- Prove2me | solution 1 for Freiman.lowerHistory_row2_source_case_19
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T01:04:10.144375+00:00
-- url     : https://prove2.me/submissions/d058d3eb-7ac5-48f7-90cd-d09195611880

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Basic
set_option linter.all false

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace H5Row2Lite

private def baseBounds (p : LowerHistoryPath) : List CertBound :=
  if p.catalog = .initial then
    [lowerHistoryZero, lowerHistoryHN,
      lowerHistoryConstantBound (729/1024) true true,
      lowerHistoryConstantBound (225/289) false true]
  else [lowerHistoryZero, lowerHistoryHN, lowerHistoryH7,
      lowerHistoryComplement lowerHistoryH9]

private def normalAt (p : LowerHistoryPath) (j : Nat) : CertBound :=
  lowerHistoryNormalization (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider
    (if j = 0 then false else decide
      (((p.steps[j-1]?.getD (([],[]),false)).1) ∈
        [(([2],[]) : LowerLabel),([3],[]),([],[1])]))

private def fixedBounds (p : LowerHistoryPath) : List CertBound :=
  baseBounds p ++ (List.range (p.steps.length+1)).map (normalAt p) ++
    (lowerHistoryFinalCuts p.row).map (fun b => lowerHistoryPull b
      (lowerHistoryWordsAt p p.steps.length) p.finalWider)

private def choiceAt (p : LowerHistoryPath) (j : Nat) : List (List CertBound) :=
  (lowerHistorySourceChoices (lowerHistoryStateAt p j)
    (p.steps[j]?.getD (([],[]),false)).1).map fun bs => bs.map fun b =>
      lowerHistoryPull b (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider

private def joinChoices (fixed : List CertBound) (choices : List (List (List CertBound))) :
    List (List CertBound) :=
  choices.foldr (fun ch acc => ch.flatMap (fun a => acc.map (fun b => a ++ b))) [fixed]

private def sources (p : LowerHistoryPath) : List (List CertBound) :=
  joinChoices (fixedBounds p) ((List.range p.steps.length).map (choiceAt p))

private theorem conditions_append (base : LowerPair) (a b : List CertBound)
    (ha : lowerHistoryAtBase base a) (hb : lowerHistoryAtBase base b) :
    lowerHistoryAtBase base (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha c hc
  · exact hb c hc

private theorem joinChoices_sound (base : LowerPair) (fixed : List CertBound)
    (choices : List (List (List CertBound)))
    (hf : lowerHistoryAtBase base fixed)
    (hc : ∀ cs ∈ choices, ∃ bs ∈ cs, lowerHistoryAtBase base bs) :
    ∃ bs ∈ joinChoices fixed choices, lowerHistoryAtBase base bs := by
  induction choices with
  | nil => exact ⟨fixed, List.mem_singleton_self _, hf⟩
  | cons ch rest ih =>
    obtain ⟨a, ha, hpa⟩ := hc ch List.mem_cons_self
    obtain ⟨b, hb, hpb⟩ := ih (fun cs hcs => hc cs (List.mem_cons_of_mem _ hcs))
    refine ⟨a ++ b, ?_, conditions_append base a b hpa hpb⟩
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

private theorem base_sound (base : LowerPair) (p : LowerHistoryPath)
    (he : lowerHistoryBaseEvent base p) : lowerHistoryAtBase base (baseBounds p) := by
  obtain ⟨bs, hbs, hs⟩ := he
  unfold lowerHistoryBasePremises at hbs
  unfold baseBounds
  split_ifs with hi
  · rw [if_pos hi] at hbs
    cases Option.some.inj hbs
    exact hs
  · rw [if_neg hi] at hbs
    cases hg : lowerHistoryRelaxedGoodness ⟨(p.context,[3,1]),(false,false)⟩ with
    | none => simp [hg] at hbs
    | some good =>
      simp only [hg, Option.map_some, Option.some.injEq] at hbs
      subst bs
      intro b hb
      exact hs b (List.mem_append_left _ hb)

private theorem source_sound (base : LowerPair) (p : LowerHistoryPath)
    (he : LowerHistorySourceEvents base p) :
    ∃ bs ∈ sources p, lowerHistoryAtBase base bs := by
  apply joinChoices_sound
  · apply conditions_append
    · apply conditions_append
      · exact base_sound base p he.baseEvent
      · intro b hb
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        exact he.normalizationEvents j (Nat.le_of_lt_succ (List.mem_range.mp hj))
          _ (List.mem_singleton_self _)
    · exact he.finalEvent
  · intro cs hcs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcs
    have hjlt : j < p.steps.length := List.mem_range.mp hj
    let step := p.steps[j]
    have hstep : p.steps[j]? = some step := List.getElem?_eq_getElem hjlt
    obtain ⟨bs, hbs, hs⟩ := he.choiceEvents j step.1 step.2 hstep
    refine ⟨_, ?_, hs⟩
    unfold choiceAt
    rw [hstep]
    exact List.mem_map.mpr ⟨bs, hbs, rfl⟩

end H5Row2Lite


open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace H5Row2Fast
private theorem inv_three (a b : ℚ) :
    lowerHistoryInv ⟨a,b,0,0⟩ =
      ⟨a / (a^2 - 3*b^2), -b / (a^2 - 3*b^2), 0, 0⟩ := by
  have hd : (a^2 + 3*b^2)^2 - 3*(2*a*b)^2 = (a^2-3*b^2)^2 := by ring
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  rw [hd]
  by_cases h : a^2 - 3*b^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring

private theorem inv_twenty_one (a d : ℚ) :
    lowerHistoryInv ⟨a,0,0,d⟩ =
      ⟨a / (a^2 - 21*d^2), 0, 0, -d / (a^2 - 21*d^2)⟩ := by
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  by_cases h : a^2 - 21*d^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring
end H5Row2Fast
private theorem bsize0 : lowerHistoryBounds01.size = 200 := by rfl
private theorem bsize1 : lowerHistoryBounds02.size = 200 := by rfl
private theorem bsize2 : lowerHistoryBounds03.size = 200 := by rfl
private theorem bsize3 : lowerHistoryBounds04.size = 200 := by rfl
private theorem bsize4 : lowerHistoryBounds05.size = 200 := by rfl
private theorem bsize5 : lowerHistoryBounds06.size = 188 := by rfl
private def p0 : LowerHistoryPath := ⟨.initial,40,[2],([1],[]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false)],([2,1,3,1],[3,1,3,1]),(true,true),false,2,⟨(1/3),(9/25),(5/19),(4/15)⟩,1⟩
private theorem canonical_source : H5Row2Lite.sources p0 = [[799,1140,1115,1108,371,843,433,1162,839,434,832,830,150,830].map lowerHistoryBound] := by
  norm_num only [List.map_cons, List.map_nil, lowerHistoryBound, lowerHistoryBounds, Array.getElem?_append, Array.size_append, bsize0, bsize1, bsize2, bsize3, bsize4, bsize5]
  change H5Row2Lite.sources p0 = [[⟨false,false,⟨⟨(371/1100),(-1/220),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩,
⟨false,true,⟨⟨(871317/2766500),(-100161/5533000),0,0⟩,⟨(735/1006),(1/1006),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩,
⟨false,true,⟨⟨(25047/134000),0,0,(3243/938000)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(519/670),0,0,(-1/670)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩,
⟨false,true,⟨⟨(2093/16500),(161/4125),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/11),(-1/33),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩,
⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩,
⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩,
⟨true,true,⟨⟨(729/1024),0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩,
⟨false,true,⟨⟨(225/289),0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩,
⟨false,false,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩,
⟨true,true,⟨⟨(9/10),0,0,(-13/70)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩,
⟨false,false,⟨⟨(7/10),0,0,(-9/70)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩,
⟨false,false,⟨⟨(113/166),0,0,(-23/166)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(125/166),0,0,(1/166)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩,
⟨true,false,⟨⟨(9551131/783196700),(2818489/783196700),0,0⟩,⟨(94/121),(1/121),0,0⟩,⟨(607/766),(-1/766),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩,
⟨false,false,⟨⟨(113/166),0,0,(-23/166)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(125/166),0,0,(1/166)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩]]
  have hcat : LowerHistoryCatalog.right ≠ LowerHistoryCatalog.initial := by decide
  norm_num (maxSteps := 1000000) [hcat,List.range_succ,List.range_zero,p0,H5Row2Lite.sources,H5Row2Lite.joinChoices,H5Row2Lite.fixedBounds,H5Row2Lite.baseBounds,H5Row2Lite.choiceAt,H5Row2Lite.normalAt,lowerHistoryStateAt,lowerHistoryWordsAt,lowerHistoryReplay,lowerHistoryRawStep,lowerHistoryInitialState,lowerHistoryAdvance,lowerHistorySourceChoices,lowerHistoryNormalization,lowerHistoryFinalCuts,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryZero,lowerHistoryConstantBound,lowerHistoryPB,lowerHistoryTheta,lowerHistoryTau,lowerHistoryComplement,lowerHistoryPull,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryRat,certFieldAdd,certFieldSub,certFieldMul,certFieldScale,H5Row2Fast.inv_three,H5Row2Fast.inv_twenty_one,lowerHistoryPick,← List.isSuffixOf_iff_suffix,List.isSuffixOf,List.isPrefixOf,beq_iff_eq]
private theorem source_cases (p : LowerHistoryPath) (hp : p ∈ [p0]) :
  H5Row2Lite.sources p = [[799,1140,1115,1108,371,843,433,1162,839,434,832,830,150,830].map lowerHistoryBound] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  subst p
  exact canonical_source
theorem solution : ∀ (base : LowerPair) (p : LowerHistoryPath), p ∈ [lowerHistoryPathsH[39]] →
  LowerHistorySourceEvents base p →
  ∃ bs ∈ ([[799,1140,1115,1108,371,843,433,1162,839,434,832,830,150,830].map lowerHistoryBound] : List (List CertBound)), lowerHistoryAtBase base bs := by
  intro base p hp he
  change p ∈ [p0] at hp
  obtain ⟨bs, hbs, hs⟩ := H5Row2Lite.source_sound base p he
  rw [source_cases p hp] at hbs
  exact ⟨bs, hbs, hs⟩
#print axioms solution
