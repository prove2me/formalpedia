-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0685_0690
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T01:44:23.900171+00:00
-- url     : https://prove2.me/submissions/3b6e9b5b-2f79-4c16-8886-c9e80711b195

import Definitions.Def_Freiman_lowerHistorySource
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Freiman_lowerHistoryVerification

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace M7SplitSep17
namespace RootInv18
theorem quadratic_three (a b : ℚ) :
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

theorem quadratic_twenty_one (a d : ℚ) :
    lowerHistoryInv ⟨a,0,0,d⟩ =
      ⟨a / (a^2 - 21*d^2), 0, 0, -d / (a^2 - 21*d^2)⟩ := by
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  by_cases h : a^2 - 21*d^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring
end RootInv18
namespace BindingNumeric20
def h2 : CertBound := ⟨true,true,⟨⟨37/50,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨125/214,-1/214,0,0⟩,⟨52/73,1/73,0,0⟩⟩⟩
def h5 : CertBound := ⟨false,true,⟨⟨279/500,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨66/179,-1/537,0,0⟩,⟨4/13,1/13,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
def h6 : CertBound := ⟨false,true,⟨⟨69/200,0,0,0⟩,⟨39/134,0,0,1/402⟩,⟨15/34,0,0,-1/34⟩,⟨1/10,0,0,1/10⟩,⟨119/202,0,0,-1/202⟩⟩⟩
def h7 : CertBound := ⟨true,false,⟨⟨31/100,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h7m : CertBound := ⟨false,true,⟨⟨161/500,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h9 : CertBound := ⟨false,false,⟨⟨3/2,-1/2,0,0⟩,⟨-1/2,1/2,0,0⟩,⟨4/13,1/13,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h21 : CertBound := ⟨false,true,⟨⟨-2334/781,1646/781,0,0⟩,⟨4/13,1/13,0,0⟩,⟨2,-1,0,0⟩,⟨42/143,1/429,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h23 : CertBound := ⟨true,true,⟨⟨139/250,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨1/2,1/6,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
def hn : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨-3/2,0,0,1/2⟩,⟨-1/2,0,0,1/6⟩,⟨-3/2,0,0,1/2⟩,⟨-1/2,0,0,1/6⟩⟩⟩
theorem bases : lowerHistoryH2=h2 ∧ lowerHistoryH5=h5 ∧ lowerHistoryH6=h6 ∧ lowerHistoryH7=h7 ∧ lowerHistoryH7Mixed=h7m ∧ lowerHistoryH9=h9 ∧ lowerHistoryH21=h21 ∧ lowerHistoryH23=h23 ∧ lowerHistoryHN=hn := by
  norm_num [h2,h5,h6,h7,h7m,h9,h21,h23,hn,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryPB,lowerHistoryTheta,lowerHistoryConstantBound,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,RootInv18.quadratic_three,RootInv18.quadratic_twenty_one,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryTau,lowerHistoryRat,certFieldScale,certFieldMul,certFieldAdd,certFieldSub]
theorem bh2 : lowerHistoryH2=h2 := bases.1
theorem bh5 : lowerHistoryH5=h5 := bases.2.1
theorem bh6 : lowerHistoryH6=h6 := bases.2.2.1
theorem bh7 : lowerHistoryH7=h7 := bases.2.2.2.1
theorem bh7m : lowerHistoryH7Mixed=h7m := bases.2.2.2.2.1
theorem bh9 : lowerHistoryH9=h9 := bases.2.2.2.2.2.1
theorem bh21 : lowerHistoryH21=h21 := bases.2.2.2.2.2.2.1
theorem bh23 : lowerHistoryH23=h23 := bases.2.2.2.2.2.2.2.1
theorem bhn : lowerHistoryHN=hn := bases.2.2.2.2.2.2.2.2
theorem initial_base : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
    [⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩,⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩,⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩,⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩] := by
  rw [bhn, bh7, bh9]
  rfl

end BindingNumeric20
end M7SplitSep17

open Freiman
namespace M7SplitSep17
namespace RootOps19
structure SourceOps where
  relaxed : LowerHistoryContext → Option (List CertBound)
  necessary : LowerHistoryState → LowerPair → Option (List CertBound)
  normalization : LowerPair → Bool → Bool → CertBound
  pull : CertBound → LowerPair → Bool → CertBound

def actualOps : SourceOps :=
  ⟨lowerHistoryRelaxedGoodness, lowerHistoryNecessary, lowerHistoryNormalization, lowerHistoryPull⟩

def eval (ops : SourceOps) (p : LowerHistoryPath) : List (List CertBound) := Id.run do
  let base : LowerPair := (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  let mut alternatives : List (List CertBound) := []
  if p.catalog = .initial then
    alternatives := [[lowerHistoryZero,lowerHistoryHN,
      lowerHistoryConstantBound (729/1024) true true,
      lowerHistoryConstantBound (225/289) false true]]
  else
    match ops.relaxed ⟨base,(false,false)⟩ with
    | none => return []
    | some good => alternatives := [[lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,
        lowerHistoryComplement lowerHistoryH9] ++ good]
  let mut words := lowerHistoryRawStep ([],[]) false p.entry
  let mut s := lowerHistoryInitialState p
  alternatives := alternatives.map fun cs => cs ++ [ops.normalization words s.wider false]
  for (l,reflect) in p.steps do
    match ops.necessary s words with
    | none => return []
    | some good =>
      alternatives := alternatives.flatMap fun cs =>
        (lowerHistorySourceChoices s l).map fun ch =>
          cs ++ good ++ ch.map (fun b => ops.pull b words s.wider)
    words := lowerHistoryRawStep words s.wider l
    s := lowerHistoryAdvance s l reflect
    let forced := decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])])
    alternatives := alternatives.map fun cs => cs ++ [ops.normalization words s.wider forced]
  match ops.necessary s words with
  | none => return []
  | some good =>
    let final := good ++ (lowerHistoryFinalCuts p.row).map (fun b => ops.pull b words s.wider)
    return alternatives.map fun cs => (cs ++ final).eraseDups

theorem actual_eval (p : LowerHistoryPath) : eval actualOps p = lowerHistorySourcePremises p := by
  rfl

end RootOps19
end M7SplitSep17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv5 : CertBound := ⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv7 : CertBound := ⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),(0),(0)⟩,⟨(109/251),(1/753),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv211 : CertBound := ⟨true,false,⟨⟨(4341/86941),(0),(0),(560/86941)⟩,⟨(193/454),(0),(0),(1/454)⟩,⟨(339/766),(0),(0),(-1/766)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv223 : CertBound := ⟨true,false,⟨⟨(3687/48134),(0),(0),(31/48134)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(487/1174),(0),(0),(-1/1174)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv228 : CertBound := ⟨true,false,⟨⟨(767/8399),(0),(0),(96/8399)⟩,⟨(29/74),(0),(0),(1/222)⟩,⟨(193/454),(0),(0),(-1/454)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv230 : CertBound := ⟨true,false,⟨⟨(551966364900/5786984313539),(9947987200/17360952940617),(0),(0)⟩,⟨(13997/32149),(-1/32149),(0),(0)⟩,⟨(12542/28787),(1/86361),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv231 : CertBound := ⟨true,false,⟨⟨(268142813350/2731343647201),(5462261750/8194030941603),(0),(0)⟩,⟨(12645/30862),(-1/30862),(0),(0)⟩,⟨(11607/28307),(1/84921),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv239 : CertBound := ⟨true,false,⟨⟨(10794293/86578700),(1930959/86578700),(0),(0)⟩,⟨(529/1222),(1/1222),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv243 : CertBound := ⟨true,false,⟨⟨(82907566100/478723971011),(506816000/478723971011),(0),(0)⟩,⟨(7298/17677),(-1/17677),(0),(0)⟩,⟨(19695/47641),(1/47641),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv250 : CertBound := ⟨true,false,⟨⟨(27904867/127104900),(6016573/127104900),(0),(0)⟩,⟨(89/218),(1/654),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv251 : CertBound := ⟨true,false,⟨⟨(359490461150/1636553162387),(1650599750/1636553162387),(0),(0)⟩,⟨(6265/14278),(-1/14278),(0),(0)⟩,⟨(16112/36661),(1/36661),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv256 : CertBound := ⟨true,false,⟨⟨(1167/4454),(0),(0),(71/4454)⟩,⟨(105/262),(0),(0),(1/262)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv264 : CertBound := ⟨true,false,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(73/170),(0),(0),(1/510)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv265 : CertBound := ⟨true,false,⟨⟨(68586194850/178709345581),(991451750/536128036743),(0),(0)⟩,⟨(1137/2714),(-1/8142),(0),(0)⟩,⟨(8849/21061),(1/21061),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv406 : CertBound := ⟨true,true,⟨⟨(4341/86941),(0),(0),(560/86941)⟩,⟨(193/454),(0),(0),(1/454)⟩,⟨(339/766),(0),(0),(-1/766)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv408 : CertBound := ⟨true,true,⟨⟨(3687/48134),(0),(0),(31/48134)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(487/1174),(0),(0),(-1/1174)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv411 : CertBound := ⟨true,true,⟨⟨(767/8399),(0),(0),(96/8399)⟩,⟨(29/74),(0),(0),(1/222)⟩,⟨(193/454),(0),(0),(-1/454)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv442 : CertBound := ⟨true,true,⟨⟨(3317/299),(-1683/299),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1),(-1/3),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv695 : CertBound := ⟨false,false,⟨⟨(1397574/21865727),(9535016/65597181),(0),(0)⟩,⟨(89/218),(1/654),(0),(0)⟩,⟨(12645/30862),(-1/30862),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv697 : CertBound := ⟨false,false,⟨⟨(482605/7364591),(3580367/22093773),(0),(0)⟩,⟨(109/251),(1/753),(0),(0)⟩,⟨(984/2257),(-1/2257),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv734 : CertBound := ⟨false,false,⟨⟨(765379/6640933),(1959179/6640933),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(517/1249),(-1/1249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv739 : CertBound := ⟨false,false,⟨⟨(42679914000/350435536433),(30287639500/9461759483691),(0),(0)⟩,⟨(11607/28307),(1/84921),(0),(0)⟩,⟨(1833/4462),(-1/4462),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv740 : CertBound := ⟨false,false,⟨⟨(757714257500/6143085145791),(40506921500/18429255437373),(0),(0)⟩,⟨(12542/28787),(1/86361),(0),(0)⟩,⟨(1865/4273),(-1/4273),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv775 : CertBound := ⟨false,false,⟨⟨(1259317038500/5655451533237),(23941271500/5655451533237),(0),(0)⟩,⟨(19695/47641),(1/47641),(0),(0)⟩,⟨(986/2377),(-1/2377),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv788 : CertBound := ⟨false,false,⟨⟨(534009/1863433),(1199347/5590299),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv793 : CertBound := ⟨false,false,⟨⟨(453773786500/1470202261803),(-2455000/1470202261803),(0),(0)⟩,⟨(16112/36661),(1/36661),(0),(0)⟩,⟨(709/1606),(-1/1606),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv801 : CertBound := ⟨false,false,⟨⟨(254992/735839),(472767/735839),(0),(0)⟩,⟨(89/214),(1/214),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv814 : CertBound := ⟨false,false,⟨⟨(537/1010),(0),(0),(-13/1010)⟩,⟨(83/202),(0),(0),(1/202)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv815 : CertBound := ⟨false,false,⟨⟨(29268009500/55044587319),(817282000/495401285871),(0),(0)⟩,⟨(8849/21061),(1/21061),(0),(0)⟩,⟨(133/314),(-1/942),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv817 : CertBound := ⟨false,false,⟨⟨(753/1394),(0),(0),(91/1394)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv850 : CertBound := ⟨false,false,⟨⟨(45303/35893),(-58924/107679),(0),(0)⟩,⟨(9/22),(1/66),(0),(0)⟩,⟨(109/251),(1/753),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv868 : CertBound := ⟨false,false,⟨⟨(16701/5317),(-7898/5317),(0),(0)⟩,⟨(9/26),(1/26),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv1107 : CertBound := ⟨false,true,⟨⟨(10794293/86578700),(1930959/86578700),(0),(0)⟩,⟨(529/1222),(1/1222),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv1125 : CertBound := ⟨false,true,⟨⟨(27904867/127104900),(6016573/127104900),(0),(0)⟩,⟨(89/218),(1/654),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op148 : lowerHistoryRelaxedGoodness ⟨([1],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op149 : lowerHistoryNecessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
theorem op44 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = bv275 := by
  norm_num [bv275, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op45 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = bv442 := by
  norm_num [bv442, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op46 : lowerHistoryNormalization ([2,3],[3,1]) false false = bv814 := by
  norm_num [bv814, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op150 : lowerHistoryNecessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [bv7] := by
  decide +kernel
theorem op151 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2,3],[3,1]) false = bv1107 := by
  norm_num [bv1107, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op48 : lowerHistoryPull (lowerHistoryH7) ([2,3],[3,1]) false = bv239 := by
  norm_num [bv239, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op157 : lowerHistoryPull (lowerHistoryH9) ([2,3],[3,1]) false = bv850 := by
  norm_num [bv850, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op158 : lowerHistoryNormalization ([2,3,2],[3,1]) true true = bv406 := by
  norm_num [bv406, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
open BindingNumeric20
theorem op159 : lowerHistoryNecessary ⟨⟨([1,2,3,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,2],[3,1]) = some [bv697] := by
  decide +kernel
theorem op160 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,3,2],[3,1]) true = bv230 := by
  norm_num [bv230, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op161 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,3,2],[3,1]) true = bv740 := by
  norm_num [bv740, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op162 : lowerHistoryPull (lowerHistoryHN) ([2,3,2],[3,1]) true = bv211 := by
  norm_num [bv211, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op163 : lowerHistoryNormalization ([2,3,1],[3,1]) true false = bv264 := by
  norm_num [bv264, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op164 : lowerHistoryNecessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [bv788] := by
  decide +kernel
theorem op165 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) true = bv251 := by
  norm_num [bv251, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op166 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) true = bv793 := by
  norm_num [bv793, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op167 : lowerHistoryPull (lowerHistoryHN) ([2,3,1],[3,1]) true = bv264 := by
  norm_num [bv264, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op50 : lowerHistoryNormalization ([2,2],[3,1]) false false = bv817 := by
  norm_num [bv817, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op168 : lowerHistoryNecessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [bv5] := by
  decide +kernel
theorem op169 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2,2],[3,1]) false = bv1125 := by
  norm_num [bv1125, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def path686 : LowerHistoryPath := ⟨.mixed,2,[1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true)],([1,2,3,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
noncomputable def raw686 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv1107,bv406,bv697,bv230,bv740,bv211],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv239,bv850,bv406,bv697,bv230,bv740,bv211]]
noncomputable def expected686 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv1107,bv406,bv697,bv230,bv740,bv211],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv239,bv850,bv406,bv697,bv230,bv740,bv211]]
theorem structural686 (ops : RootOps19.SourceOps) (b3 b7 b21 b211 b230 b239 b260 b275 b371 b406 b440 b442 b697 b740 b814 b843 b850 b856 b1107 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h148 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h149 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h44 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h45 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h46 : ops.normalization ([2,3],[3,1]) false false = b814)
    (h150 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (h151 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,3],[3,1]) false = b1107)
    (h48 : ops.pull (lowerHistoryH7) ([2,3],[3,1]) false = b239)
    (h157 : ops.pull (lowerHistoryH9) ([2,3],[3,1]) false = b850)
    (h158 : ops.normalization ([2,3,2],[3,1]) true true = b406)
    (h159 : ops.necessary ⟨⟨([1,2,3,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,2],[3,1]) = some [b697])
    (h160 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,2],[3,1]) true = b230)
    (h161 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,2],[3,1]) true = b740)
    (h162 : ops.pull (lowerHistoryHN) ([2,3,2],[3,1]) true = b211)
    : RootOps19.eval ops path686 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b211],[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b211]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path686, h0, h148, h2, h149, h44, h45, h46, h150, h151, h48, h157, h158, h159, h160, h161, h162, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource686 : lowerHistorySourcePremises path686 = raw686.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural686 RootOps19.actualOps bv3 bv7 bv21 bv211 bv230 bv239 bv260 bv275 bv371 bv406 bv440 bv442 bv697 bv740 bv814 bv843 bv850 bv856 bv1107 op0 op148 op2 op149 op44 op45 op46 op150 op151 op48 op157 op158 op159 op160 op161 op162
theorem dedup686 : raw686.map List.eraseDups = expected686 := by
  decide +kernel
theorem source686 : lowerHistorySourcePremises path686 = expected686 := (rawSource686).trans (dedup686)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
open Freiman
namespace M7SplitSep17
namespace BoundCompact16
set_option maxRecDepth 30000

def emptyBound : CertBound :=
  ⟨true,false,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

theorem bound_of_option (id : ℕ) (target : CertBound)
    (h : lowerHistoryBounds[id - 1]? = some target) :
    lowerHistoryBound id = target := by
  unfold lowerHistoryBound
  exact (congrArg (fun o : Option CertBound => o.getD emptyBound) h).trans rfl

theorem size01 : lowerHistoryBounds01.size = 200 := by rfl
theorem size02 : lowerHistoryBounds02.size = 200 := by rfl
theorem size03 : lowerHistoryBounds03.size = 200 := by rfl
theorem size04 : lowerHistoryBounds04.size = 200 := by rfl
theorem size05 : lowerHistoryBounds05.size = 200 := by rfl

theorem global_to_chunk1 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[i]? = lowerHistoryBounds01[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  exact Array.getElem?_append_left (by rw [size01]; omega)

theorem global_to_chunk2 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[200 + i]? = lowerHistoryBounds02[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01) (by rw [size01]; omega), size01]
  exact congrArg (fun j => lowerHistoryBounds02[j]?) (by omega)

theorem global_to_chunk3 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[400 + i]? = lowerHistoryBounds03[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  simp only [Array.size_append, size01, size02]
  exact congrArg (fun j => lowerHistoryBounds03[j]?) (by omega)

theorem global_to_chunk4 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[600 + i]? = lowerHistoryBounds04[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  simp only [Array.size_append, size01, size02, size03]
  exact congrArg (fun j => lowerHistoryBounds04[j]?) (by omega)

theorem global_to_chunk5 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[800 + i]? = lowerHistoryBounds05[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04]
  exact congrArg (fun j => lowerHistoryBounds05[j]?) (by omega)

theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryBounds[1000 + i]? = lowerHistoryBounds06[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryBounds06[j]?) (by omega)

end BoundCompact16
namespace PremiseCompact50

variable {α : Type} (a b c d e f : Array α)
  (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
  (hd : d.size = 200) (he : e.size = 200)
include ha hb hc hd he

theorem lookup_chunk1 (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[i]? = a[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e)
    (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d)
    (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c)
    (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b)
    (by simp only [Array.size_append, ha, hb]; omega)]
  exact Array.getElem?_append_left (xs := a) (by omega)

theorem lookup_chunk2 (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[200 + i]? = b[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e)
    (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d)
    (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c)
    (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b)
    (by simp only [Array.size_append, ha, hb]; omega)]
  rw [Array.getElem?_append_right (xs := a) (by omega), ha]
  exact congrArg (fun j => b[j]?) (by omega)

end PremiseCompact50
namespace WitnessCompact16
set_option maxRecDepth 30000

def witnessShape (w : CertWitness) : CertBound × CertBound × CertRectangle :=
  (w.lowerBound, w.upperBound, w.rectangle)

def emptyWitness : CertWitness :=
  ⟨lowerHistoryBound 0, lowerHistoryBound 0, ⟨0,1,0,1⟩,
    fun _ _ => ⟨0,0,0,0⟩, fun _ _ => 0⟩

theorem lowerHistoryWitness_def (id : ℕ) :
    lowerHistoryWitness id =
      (lowerHistoryWitnesses[id - 1]?).getD emptyWitness := by
  rfl

theorem projections_of_shape (w : CertWitness) (l u : CertBound)
    (r : CertRectangle) (h : witnessShape w = (l, u, r)) :
    w.lowerBound = l ∧ w.upperBound = u ∧ w.rectangle = r := by
  simpa only [witnessShape, Prod.mk.injEq] using h

theorem shape_of_global_option (id : ℕ)
    (target : CertBound × CertBound × CertRectangle)
    (h : (lowerHistoryWitnesses[id - 1]?).map witnessShape = some target) :
    witnessShape (lowerHistoryWitness id) = target := by
  have hs : witnessShape ((lowerHistoryWitnesses[id - 1]?).getD emptyWitness) =
      target := by
    cases ho : lowerHistoryWitnesses[id - 1]? <;> simp_all
  exact (congrArg witnessShape (lowerHistoryWitness_def id)).trans hs

theorem projection_of_global_option (id : ℕ)
    (l u : CertBound) (r : CertRectangle)
    (h : (lowerHistoryWitnesses[id - 1]?).map witnessShape = some (l, u, r)) :
    (lowerHistoryWitness id).lowerBound = l ∧
    (lowerHistoryWitness id).upperBound = u ∧
    (lowerHistoryWitness id).rectangle = r := by
  exact projections_of_shape _ _ _ _ (shape_of_global_option id (l, u, r) h)

theorem size01 : lowerHistoryWitnesses01.size = 200 := by rfl
theorem size02 : lowerHistoryWitnesses02.size = 200 := by rfl
theorem size03 : lowerHistoryWitnesses03.size = 200 := by rfl
theorem size04 : lowerHistoryWitnesses04.size = 200 := by rfl
theorem size05 : lowerHistoryWitnesses05.size = 200 := by rfl

theorem global_to_chunk5 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[800 + i]? = lowerHistoryWitnesses05[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04]
  exact congrArg (fun j => lowerHistoryWitnesses05[j]?) (by omega)

theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryWitnesses[1000 + i]? = lowerHistoryWitnesses06[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryWitnesses06[j]?) (by omega)

end WitnessCompact16
namespace BindingIds19
set_option Elab.async false
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def extras (p : LowerHistoryPath) (branch : Nat) : List CertBound :=
  let comp := (lowerHistoryEndpointComparisons p)[branch]?.getD ([],.automatic)
  comp.1 ++ (match comp.2 with | .bound b => [lowerHistoryComplement b] | _ => [])

def residualIds (src ext : List (List Nat)) (r : LowerHistoryRecord) : List Nat :=
  if r.endpointBranch < 0 then src[r.alternative]?.getD []
  else src[r.alternative]?.getD [] ++ ext[r.endpointBranch.toNat]?.getD []

instance survivorDecidable (p : LowerHistoryPath) : Decidable (lowerHistorySurvivor p) := by
  unfold lowerHistorySurvivor
  infer_instance

def recordCheck (p : LowerHistoryPath) (src ext : List (List Nat))
    (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat) (r : LowerHistoryRecord) : Bool :=
  if r.survivor then decide (lowerHistorySurvivor p ∧ r.alternative = 0) else
  decide (0 < r.premiseId ∧ r.premiseId ≤ np ∧
    0 < r.witnessId ∧ r.witnessId ≤ nw ∧
    (r.endpointBranch < 0 ∨ r.endpointBranch.toNat < ext.length) ∧
    (preIDs r.premiseId).toFinset = (residualIds src ext r).toFinset ∧
    (wids r.witnessId).1 ∈ preIDs r.premiseId ∧
    (wids r.witnessId).2 ∈ preIDs r.premiseId)

theorem map_getD (xs : List (List Nat)) (i : Nat) :
    ((xs.map (List.map lowerHistoryBound))[i]?).getD [] =
      (xs[i]?.getD []).map lowerHistoryBound := by
  cases h : xs[i]? <;> simp [List.getElem?_map, h]

theorem mapped_finset_congr (a b : List Nat) (h : a.toFinset = b.toFinset) :
    (a.map lowerHistoryBound).toFinset = (b.map lowerHistoryBound).toFinset := by
  have hm : ∀ x, x ∈ a ↔ x ∈ b := by
    intro x
    simpa only [List.mem_toFinset] using
      (Iff.of_eq (congrArg (fun s : Finset Nat => x ∈ s) h))
  ext x
  simp only [List.mem_toFinset, List.mem_map, hm]

theorem residual_values (p : LowerHistoryPath) (src ext : List (List Nat))
    (r : LowerHistoryRecord)
    (hs : lowerHistorySourcePremises p = src.map (List.map lowerHistoryBound))
    (he : (List.range ext.length).map (extras p) = ext.map (List.map lowerHistoryBound))
    (hb : r.endpointBranch < 0 ∨ r.endpointBranch.toNat < ext.length) :
    (lowerHistoryResidual p r.alternative r.endpointBranch).toFinset =
      ((residualIds src ext r).map lowerHistoryBound).toFinset := by
  by_cases hn : r.endpointBranch < 0
  · simp only [lowerHistoryResidual, residualIds, hn, ↓reduceIte, hs, map_getD]
  · have hbi : r.endpointBranch.toNat < ext.length := hb.resolve_left hn
    have hget : extras p r.endpointBranch.toNat =
        (ext[r.endpointBranch.toNat]?.getD []).map lowerHistoryBound := by
      have hm := congrArg (fun bs : List (List CertBound) => bs[r.endpointBranch.toNat]?.getD []) he
      simpa [List.getElem?_map, List.getElem?_range, hbi, map_getD] using hm
    have hdup (bs : List CertBound) : bs.eraseDups.toFinset = bs.toFinset := by
      ext b
      simp only [List.mem_toFinset, List.mem_eraseDups]
    simp only [lowerHistoryResidual, hn, ↓reduceIte]
    rw [hdup]
    rw [List.append_assoc]
    change ((lowerHistorySourcePremises p)[r.alternative]?.getD [] ++
      extras p r.endpointBranch.toNat).toFinset = _
    rw [hs, map_getD, hget]
    simp only [residualIds, hn, ↓reduceIte, List.map_append]

theorem recordCheck_sound (p : LowerHistoryPath) (src ext : List (List Nat))
    (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat) (r : LowerHistoryRecord)
    (hz : lowerHistoryPremises.size = np ∧ lowerHistoryWitnesses.size = nw)
    (hs : lowerHistorySourcePremises p = src.map (List.map lowerHistoryBound))
    (he : (List.range ext.length).map (extras p) = ext.map (List.map lowerHistoryBound))
    (hprem : r.survivor = false → lowerHistoryPremise r.premiseId =
      (preIDs r.premiseId).map lowerHistoryBound)
    (hw : r.survivor = false →
      (lowerHistoryWitness r.witnessId).lowerBound = lowerHistoryBound (wids r.witnessId).1 ∧
      (lowerHistoryWitness r.witnessId).upperBound = lowerHistoryBound (wids r.witnessId).2 ∧
      (lowerHistoryWitness r.witnessId).rectangle = p.rectangle)
    (hc : recordCheck p src ext wids preIDs np nw r = true) : lowerHistoryRecordBinding p r := by
  cases hr : r.survivor
  · simp only [recordCheck, hr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hc
    rcases hc with ⟨hp, hps, hwpos, hws, hb, hf, hl, hu⟩
    have hres := residual_values p src ext r hs he hb
    have hw' := hw hr
    have hpre := hprem hr
    simp only [lowerHistoryRecordBinding, hr, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hp, ?_, hwpos, ?_, ?_, ?_, ?_, hw'.2.2⟩
    · rwa [hz.1]
    · rwa [hz.2]
    · rw [hpre]
      exact (mapped_finset_congr _ _ hf).trans hres.symm
    · rw [hw'.1, hpre]
      exact List.mem_map.mpr ⟨_, hl, rfl⟩
    · rw [hw'.2.1, hpre]
      exact List.mem_map.mpr ⟨_, hu, rfl⟩
  · simpa only [recordCheck, lowerHistoryRecordBinding, hr, ↓reduceIte, decide_eq_true_eq] using hc

theorem pathBinding_from_ids (p : LowerHistoryPath) (src ext : List (List Nat))
    (rs : List LowerHistoryRecord) (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat)
    (hz : lowerHistoryPremises.size = np ∧ lowerHistoryWitnesses.size = nw)
    (hs : lowerHistorySourcePremises p = src.map (List.map lowerHistoryBound))
    (he : (List.range ext.length).map (extras p) = ext.map (List.map lowerHistoryBound))
    (hrs : lowerHistoryRecordsFor p = rs) (hlen : p.alternatives = src.length)
    (hprem : ∀ r ∈ rs, r.survivor = false → lowerHistoryPremise r.premiseId =
      (preIDs r.premiseId).map lowerHistoryBound)
    (hw : ∀ r ∈ rs, r.survivor = false →
      (lowerHistoryWitness r.witnessId).lowerBound = lowerHistoryBound (wids r.witnessId).1 ∧
      (lowerHistoryWitness r.witnessId).upperBound = lowerHistoryBound (wids r.witnessId).2 ∧
      (lowerHistoryWitness r.witnessId).rectangle = p.rectangle)
    (hcheck : rs.all (recordCheck p src ext wids preIDs np nw) = true)
    (hcover : lowerHistoryRecordCoverage p) : lowerHistoryPathBinding p := by
  refine ⟨?_, ?_, hcover⟩
  · simpa [hs] using hlen
  · intro r hr
    rw [hrs] at hr
    exact recordCheck_sound p src ext wids preIDs np nw r hz hs he (hprem r hr) (hw r hr)
      ((List.all_eq_true.mp hcheck) r hr)
end BindingIds19
namespace BatchCoverage15

def coverageCheck (p : LowerHistoryPath) (rs : List LowerHistoryRecord) (ai : ℕ) : Bool :=
  rs.any (fun r => decide (r.alternative = ai ∧ r.endpointBranch < 0)) ||
    (decide (p.catalog ≠ .initial ∧ p.row ≠ 4) &&
      ((lowerHistoryEndpointComparisons p).zipIdx.all fun (cg,bi) =>
        decide (cg.2 = .automatic) || rs.any fun r =>
          decide (r.alternative = ai ∧ r.endpointBranch = (bi : ℤ) ∧ r.survivor = false)))

theorem coverage_sound (p : LowerHistoryPath) (rs : List LowerHistoryRecord)
    (hrs : lowerHistoryRecordsFor p = rs)
    (hlen : p.alternatives = (lowerHistorySourcePremises p).length)
    (hcheck : (List.range p.alternatives).all (coverageCheck p rs) = true) :
    lowerHistoryRecordCoverage p := by
  intro ai hai
  have hai' : ai < p.alternatives := by rwa [hlen]
  have ha := (List.all_eq_true.mp hcheck) ai (List.mem_range.mpr hai')
  simp only [coverageCheck, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true, decide_eq_true_eq] at ha
  rcases ha with ha | ⟨⟨hi,hr⟩,hc⟩
  · left
    obtain ⟨r,hm,halt,hbranch⟩ := ha
    exact ⟨r,Eq.mpr (congrArg (fun zs : List LowerHistoryRecord => r ∈ zs) hrs) hm,
      halt,hbranch⟩
  · right
    refine ⟨hi,hr,?_⟩
    intro bi cs g hget hna
    have hm : ((cs,g),bi) ∈ (lowerHistoryEndpointComparisons p).zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr hget
    rcases hc ((cs,g),bi) hm with hauto | hw
    · exact False.elim (hna hauto)
    · obtain ⟨r,hm,hrest⟩ := hw
      exact ⟨r,Eq.mpr (congrArg (fun zs : List LowerHistoryRecord => r ∈ zs) hrs) hm,hrest⟩

end BatchCoverage15
namespace BatchLookup20
theorem nonleft_catalogs :
  (∀ r ∈ lowerHistoryRecordsR.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsM.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsX.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsH.toList, r.catalog ≠ .left) := by
  decide +kernel
theorem filter_nonleft (xs : List LowerHistoryRecord)
    (h : ∀ r ∈ xs, r.catalog ≠ .left) (id : Nat) :
    xs.filter (fun r => decide (r.catalog = .left ∧ r.pathId = id)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  simpa only [decide_eq_true_eq] using (show ¬ (r.catalog = .left ∧ r.pathId = id) from fun hri => h r hr hri.1)
theorem left_filter (id : Nat) :
    lowerHistoryRecordsFor (⟨.left,id,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) =
      lowerHistoryRecordsL.toList.filter (fun r => decide (r.catalog = .left ∧ r.pathId = id)) := by
  unfold lowerHistoryRecordsFor lowerHistoryRecords
  simp only [Array.toList_append, List.filter_append]
  rw [filter_nonleft _ nonleft_catalogs.1,
      filter_nonleft _ nonleft_catalogs.2.1,
      filter_nonleft _ nonleft_catalogs.2.2.1,
      filter_nonleft _ nonleft_catalogs.2.2.2]
  simp only [List.append_nil]
end BatchLookup20
theorem premise_size : lowerHistoryPremises.size = 1025 := by
  simp only [lowerHistoryPremises, Array.size_append]
  rfl
theorem witness_size : lowerHistoryWitnesses.size = 1194 := by
  simp only [lowerHistoryWitnesses, Array.size_append]
  rfl
end M7SplitSep17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
theorem bound3 : lowerHistoryBound 3 = bv3 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[2]? = some bv3 := Eq.refl (some bv3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hl
theorem bound5 : lowerHistoryBound 5 = bv5 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[4]? = some bv5 := Eq.refl (some bv5)
  exact (BoundCompact16.global_to_chunk1 4 (by decide)).trans hl
theorem bound7 : lowerHistoryBound 7 = bv7 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[6]? = some bv7 := Eq.refl (some bv7)
  exact (BoundCompact16.global_to_chunk1 6 (by decide)).trans hl
theorem bound21 : lowerHistoryBound 21 = bv21 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[20]? = some bv21 := Eq.refl (some bv21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hl
theorem bound211 : lowerHistoryBound 211 = bv211 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[10]? = some bv211 := Eq.refl (some bv211)
  exact (BoundCompact16.global_to_chunk2 10 (by decide)).trans hl
theorem bound223 : lowerHistoryBound 223 = bv223 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[22]? = some bv223 := Eq.refl (some bv223)
  exact (BoundCompact16.global_to_chunk2 22 (by decide)).trans hl
theorem bound228 : lowerHistoryBound 228 = bv228 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[27]? = some bv228 := Eq.refl (some bv228)
  exact (BoundCompact16.global_to_chunk2 27 (by decide)).trans hl
theorem bound230 : lowerHistoryBound 230 = bv230 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[29]? = some bv230 := Eq.refl (some bv230)
  exact (BoundCompact16.global_to_chunk2 29 (by decide)).trans hl
theorem bound231 : lowerHistoryBound 231 = bv231 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[30]? = some bv231 := Eq.refl (some bv231)
  exact (BoundCompact16.global_to_chunk2 30 (by decide)).trans hl
theorem bound239 : lowerHistoryBound 239 = bv239 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[38]? = some bv239 := Eq.refl (some bv239)
  exact (BoundCompact16.global_to_chunk2 38 (by decide)).trans hl
theorem bound243 : lowerHistoryBound 243 = bv243 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[42]? = some bv243 := Eq.refl (some bv243)
  exact (BoundCompact16.global_to_chunk2 42 (by decide)).trans hl
theorem bound250 : lowerHistoryBound 250 = bv250 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[49]? = some bv250 := Eq.refl (some bv250)
  exact (BoundCompact16.global_to_chunk2 49 (by decide)).trans hl
theorem bound251 : lowerHistoryBound 251 = bv251 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[50]? = some bv251 := Eq.refl (some bv251)
  exact (BoundCompact16.global_to_chunk2 50 (by decide)).trans hl
theorem bound256 : lowerHistoryBound 256 = bv256 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[55]? = some bv256 := Eq.refl (some bv256)
  exact (BoundCompact16.global_to_chunk2 55 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound264 : lowerHistoryBound 264 = bv264 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[63]? = some bv264 := Eq.refl (some bv264)
  exact (BoundCompact16.global_to_chunk2 63 (by decide)).trans hl
theorem bound265 : lowerHistoryBound 265 = bv265 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[64]? = some bv265 := Eq.refl (some bv265)
  exact (BoundCompact16.global_to_chunk2 64 (by decide)).trans hl
theorem bound275 : lowerHistoryBound 275 = bv275 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[74]? = some bv275 := Eq.refl (some bv275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound406 : lowerHistoryBound 406 = bv406 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[5]? = some bv406 := Eq.refl (some bv406)
  exact (BoundCompact16.global_to_chunk3 5 (by decide)).trans hl
theorem bound408 : lowerHistoryBound 408 = bv408 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[7]? = some bv408 := Eq.refl (some bv408)
  exact (BoundCompact16.global_to_chunk3 7 (by decide)).trans hl
theorem bound411 : lowerHistoryBound 411 = bv411 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[10]? = some bv411 := Eq.refl (some bv411)
  exact (BoundCompact16.global_to_chunk3 10 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound442 : lowerHistoryBound 442 = bv442 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[41]? = some bv442 := Eq.refl (some bv442)
  exact (BoundCompact16.global_to_chunk3 41 (by decide)).trans hl
theorem bound695 : lowerHistoryBound 695 = bv695 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[94]? = some bv695 := Eq.refl (some bv695)
  exact (BoundCompact16.global_to_chunk4 94 (by decide)).trans hl
theorem bound697 : lowerHistoryBound 697 = bv697 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[96]? = some bv697 := Eq.refl (some bv697)
  exact (BoundCompact16.global_to_chunk4 96 (by decide)).trans hl
theorem bound734 : lowerHistoryBound 734 = bv734 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[133]? = some bv734 := Eq.refl (some bv734)
  exact (BoundCompact16.global_to_chunk4 133 (by decide)).trans hl
theorem bound739 : lowerHistoryBound 739 = bv739 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[138]? = some bv739 := Eq.refl (some bv739)
  exact (BoundCompact16.global_to_chunk4 138 (by decide)).trans hl
theorem bound740 : lowerHistoryBound 740 = bv740 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[139]? = some bv740 := Eq.refl (some bv740)
  exact (BoundCompact16.global_to_chunk4 139 (by decide)).trans hl
theorem bound775 : lowerHistoryBound 775 = bv775 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[174]? = some bv775 := Eq.refl (some bv775)
  exact (BoundCompact16.global_to_chunk4 174 (by decide)).trans hl
theorem bound788 : lowerHistoryBound 788 = bv788 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[187]? = some bv788 := Eq.refl (some bv788)
  exact (BoundCompact16.global_to_chunk4 187 (by decide)).trans hl
theorem bound793 : lowerHistoryBound 793 = bv793 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[192]? = some bv793 := Eq.refl (some bv793)
  exact (BoundCompact16.global_to_chunk4 192 (by decide)).trans hl
theorem bound801 : lowerHistoryBound 801 = bv801 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[0]? = some bv801 := Eq.refl (some bv801)
  exact (BoundCompact16.global_to_chunk5 0 (by decide)).trans hl
theorem bound814 : lowerHistoryBound 814 = bv814 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[13]? = some bv814 := Eq.refl (some bv814)
  exact (BoundCompact16.global_to_chunk5 13 (by decide)).trans hl
theorem bound815 : lowerHistoryBound 815 = bv815 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[14]? = some bv815 := Eq.refl (some bv815)
  exact (BoundCompact16.global_to_chunk5 14 (by decide)).trans hl
theorem bound817 : lowerHistoryBound 817 = bv817 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[16]? = some bv817 := Eq.refl (some bv817)
  exact (BoundCompact16.global_to_chunk5 16 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound850 : lowerHistoryBound 850 = bv850 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[49]? = some bv850 := Eq.refl (some bv850)
  exact (BoundCompact16.global_to_chunk5 49 (by decide)).trans hl
theorem bound856 : lowerHistoryBound 856 = bv856 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[55]? = some bv856 := Eq.refl (some bv856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hl
theorem bound868 : lowerHistoryBound 868 = bv868 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[67]? = some bv868 := Eq.refl (some bv868)
  exact (BoundCompact16.global_to_chunk5 67 (by decide)).trans hl
theorem bound1107 : lowerHistoryBound 1107 = bv1107 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[106]? = some bv1107 := Eq.refl (some bv1107)
  exact (BoundCompact16.global_to_chunk6 106).trans hl
theorem bound1125 : lowerHistoryBound 1125 = bv1125 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[124]? = some bv1125 := Eq.refl (some bv1125)
  exact (BoundCompact16.global_to_chunk6 124).trans hl
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Freiman
namespace M7ContinueSep17.CatalogueGeneral

def catalogRecords : LowerHistoryCatalog → List LowerHistoryRecord
  | .left => lowerHistoryRecordsL.toList
  | .right => lowerHistoryRecordsR.toList
  | .mixed => lowerHistoryRecordsM.toList
  | .rightMixed => lowerHistoryRecordsX.toList
  | .initial => lowerHistoryRecordsH.toList

theorem records_catalog (c : LowerHistoryCatalog) :
    ∀ r ∈ catalogRecords c, r.catalog = c := by
  cases c <;> decide +kernel

theorem filter_other (c d : LowerHistoryCatalog) (hne : c ≠ d) (id : Nat) :
    (catalogRecords c).filter (fun r => decide (r.catalog = d ∧ r.pathId = id)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  simp only [decide_eq_true_eq]
  intro h
  exact hne ((records_catalog c r hr).symm.trans h.1)

theorem records_partition : lowerHistoryRecords.toList =
    catalogRecords .left ++ catalogRecords .right ++ catalogRecords .mixed ++
    catalogRecords .rightMixed ++ catalogRecords .initial := by
  simp only [lowerHistoryRecords, Array.toList_append, catalogRecords]

theorem records_for_catalog (p : LowerHistoryPath) : lowerHistoryRecordsFor p =
    (catalogRecords p.catalog).filter (fun r => decide (r.catalog = p.catalog ∧ r.pathId = p.id)) := by
  unfold lowerHistoryRecordsFor
  rw [records_partition]
  simp only [List.filter_append]
  cases hc : p.catalog
  · rw [filter_other .right .left (by decide), filter_other .mixed .left (by decide),
      filter_other .rightMixed .left (by decide), filter_other .initial .left (by decide)]
    simp only [List.append_nil]
  · rw [filter_other .left .right (by decide), filter_other .mixed .right (by decide),
      filter_other .rightMixed .right (by decide), filter_other .initial .right (by decide)]
    simp only [List.append_nil, List.nil_append]
  · rw [filter_other .left .mixed (by decide), filter_other .right .mixed (by decide),
      filter_other .rightMixed .mixed (by decide), filter_other .initial .mixed (by decide)]
    simp only [List.append_nil, List.nil_append]
  · rw [filter_other .left .rightMixed (by decide), filter_other .right .rightMixed (by decide),
      filter_other .mixed .rightMixed (by decide), filter_other .initial .rightMixed (by decide)]
    simp only [List.append_nil, List.nil_append]
  · rw [filter_other .left .initial (by decide), filter_other .right .initial (by decide),
      filter_other .mixed .initial (by decide), filter_other .rightMixed .initial (by decide)]
    simp only [List.nil_append]
end M7ContinueSep17.CatalogueGeneral

set_option maxRecDepth 100000
open Freiman
namespace M7ContinueSep17.CatalogueGeneral
theorem catalogListM : catalogRecords .mixed = [
⟨.mixed,1,0,(-1),false,223,1072⟩,
⟨.mixed,2,0,(-1),false,231,1084⟩,
⟨.mixed,2,1,(-1),false,229,1084⟩,
⟨.mixed,3,0,(-1),false,235,1108⟩,
⟨.mixed,4,0,(-1),false,120,1078⟩,
⟨.mixed,5,0,(-1),false,132,1096⟩,
⟨.mixed,5,1,(-1),false,129,1096⟩,
⟨.mixed,6,0,(-1),false,157,1120⟩,
⟨.mixed,7,0,(-1),false,342,584⟩,
⟨.mixed,8,0,(-1),false,341,596⟩,
⟨.mixed,8,1,(-1),false,340,596⟩,
⟨.mixed,9,0,(-1),false,343,632⟩,
⟨.mixed,10,0,(-1),false,435,1013⟩,
⟨.mixed,11,0,(-1),false,224,650⟩,
⟨.mixed,12,0,(-1),false,232,692⟩,
⟨.mixed,12,1,(-1),false,230,692⟩,
⟨.mixed,13,0,(-1),false,236,752⟩,
⟨.mixed,14,0,(-1),false,276,590⟩,
⟨.mixed,14,1,(-1),false,274,590⟩,
⟨.mixed,14,2,(-1),false,275,590⟩,
⟨.mixed,14,3,(-1),false,273,590⟩,
⟨.mixed,15,0,(-1),false,272,614⟩,
⟨.mixed,15,1,(-1),false,268,614⟩,
⟨.mixed,15,2,(-1),false,270,614⟩,
⟨.mixed,15,3,(-1),false,266,614⟩,
⟨.mixed,15,4,(-1),false,271,614⟩,
⟨.mixed,15,5,(-1),false,267,614⟩,
⟨.mixed,15,6,(-1),false,269,614⟩,
⟨.mixed,15,7,(-1),false,265,614⟩,
⟨.mixed,16,0,(-1),false,280,662⟩,
⟨.mixed,16,1,(-1),false,278,662⟩,
⟨.mixed,16,2,(-1),false,279,662⟩,
⟨.mixed,16,3,(-1),false,277,662⟩,
⟨.mixed,17,0,(-1),false,439,1030⟩,
⟨.mixed,17,1,(-1),false,437,722⟩,
⟨.mixed,17,2,(-1),false,438,1030⟩,
⟨.mixed,17,3,(-1),false,436,722⟩,
⟨.mixed,18,0,(-1),false,121,686⟩,
⟨.mixed,18,1,(-1),false,119,686⟩,
⟨.mixed,19,0,(-1),false,133,728⟩,
⟨.mixed,19,1,(-1),false,130,728⟩,
⟨.mixed,19,2,(-1),false,131,728⟩,
⟨.mixed,19,3,(-1),false,128,728⟩,
⟨.mixed,20,0,(-1),false,158,776⟩,
⟨.mixed,20,1,(-1),false,156,776⟩,
⟨.mixed,21,0,(-1),false,188,626⟩,
⟨.mixed,21,1,(-1),false,187,80⟩,
⟨.mixed,22,0,(-1),false,186,656⟩,
⟨.mixed,22,1,(-1),false,184,656⟩,
⟨.mixed,22,2,(-1),false,185,86⟩,
⟨.mixed,22,3,(-1),false,183,86⟩,
⟨.mixed,23,0,(-1),false,192,698⟩,
⟨.mixed,23,1,(-1),false,191,92⟩,
⟨.mixed,24,0,0,false,492,72⟩,
⟨.mixed,24,0,1,false,484,72⟩,
⟨.mixed,24,0,2,false,460,28⟩,
⟨.mixed,24,0,3,false,480,558⟩,
⟨.mixed,24,0,4,false,482,175⟩,
⟨.mixed,24,0,5,false,449,76⟩,
⟨.mixed,24,0,6,false,447,76⟩,
⟨.mixed,24,0,7,false,441,32⟩,
⟨.mixed,24,0,8,false,445,562⟩,
⟨.mixed,24,0,9,false,446,179⟩,
⟨.mixed,24,0,10,false,488,314⟩,
⟨.mixed,24,0,11,false,472,314⟩,
⟨.mixed,24,0,12,false,456,18⟩,
⟨.mixed,24,0,13,false,468,548⟩,
⟨.mixed,24,0,14,false,469,165⟩,
⟨.mixed,24,0,15,false,489,60⟩,
⟨.mixed,24,0,16,false,473,60⟩,
⟨.mixed,24,0,17,false,457,22⟩,
⟨.mixed,24,0,18,false,470,552⟩,
⟨.mixed,24,0,19,false,471,169⟩,
⟨.mixed,24,1,0,false,490,155⟩,
⟨.mixed,24,1,1,false,478,155⟩,
⟨.mixed,24,1,2,false,458,28⟩,
⟨.mixed,24,1,3,false,474,558⟩,
⟨.mixed,24,1,4,false,476,175⟩,
⟨.mixed,24,1,5,false,448,159⟩,
⟨.mixed,24,1,6,false,444,159⟩,
⟨.mixed,24,1,7,false,440,32⟩,
⟨.mixed,24,1,8,false,442,562⟩,
⟨.mixed,24,1,9,false,443,179⟩,
⟨.mixed,24,1,10,false,486,314⟩,
⟨.mixed,24,1,11,false,466,314⟩,
⟨.mixed,24,1,12,false,454,18⟩,
⟨.mixed,24,1,13,false,462,548⟩,
⟨.mixed,24,1,14,false,463,165⟩,
⟨.mixed,24,1,15,false,487,113⟩,
⟨.mixed,24,1,16,false,467,113⟩,
⟨.mixed,24,1,17,false,455,22⟩,
⟨.mixed,24,1,18,false,464,552⟩,
⟨.mixed,24,1,19,false,465,169⟩,
⟨.mixed,25,0,(-1),false,45,746⟩,
⟨.mixed,26,0,(-1),false,44,764⟩,
⟨.mixed,26,1,(-1),false,43,764⟩,
⟨.mixed,27,0,0,false,74,72⟩,
⟨.mixed,27,0,1,false,70,72⟩,
⟨.mixed,27,0,2,false,58,28⟩,
⟨.mixed,27,0,3,false,66,558⟩,
⟨.mixed,27,0,4,false,68,175⟩,
⟨.mixed,27,0,5,false,50,76⟩,
⟨.mixed,27,0,6,false,49,76⟩,
⟨.mixed,27,0,7,false,46,32⟩,
⟨.mixed,27,0,8,false,47,562⟩,
⟨.mixed,27,0,9,false,48,179⟩,
⟨.mixed,27,0,10,false,72,314⟩,
⟨.mixed,27,0,11,false,64,314⟩,
⟨.mixed,27,0,12,false,56,18⟩,
⟨.mixed,27,0,13,false,60,548⟩,
⟨.mixed,27,0,14,false,61,165⟩,
⟨.mixed,27,0,15,false,73,60⟩,
⟨.mixed,27,0,16,false,65,60⟩,
⟨.mixed,27,0,17,false,57,22⟩,
⟨.mixed,27,0,18,false,62,552⟩,
⟨.mixed,27,0,19,false,63,169⟩,
⟨.mixed,28,0,(-1),false,415,746⟩,
⟨.mixed,28,1,(-1),false,410,746⟩,
⟨.mixed,28,2,(-1),false,416,746⟩,
⟨.mixed,29,0,(-1),false,377,608⟩,
⟨.mixed,29,1,(-1),false,373,608⟩,
⟨.mixed,29,2,(-1),false,376,608⟩,
⟨.mixed,29,3,(-1),false,372,608⟩,
⟨.mixed,29,4,(-1),false,378,608⟩,
⟨.mixed,29,5,(-1),false,374,608⟩,
⟨.mixed,30,0,(-1),false,381,644⟩,
⟨.mixed,30,1,(-1),false,380,644⟩,
⟨.mixed,30,2,(-1),false,382,644⟩,
⟨.mixed,31,0,(-1),false,412,764⟩,
⟨.mixed,32,0,(-1),false,317,602⟩,
⟨.mixed,33,0,(-1),false,315,620⟩,
⟨.mixed,33,1,(-1),false,313,620⟩,
⟨.mixed,34,0,(-1),false,319,668⟩,
⟨.mixed,35,0,(-1),false,33,746⟩,
⟨.mixed,36,0,(-1),false,32,764⟩,
⟨.mixed,36,1,(-1),false,31,764⟩,
⟨.mixed,37,0,(-1),false,35,54⟩,
⟨.mixed,38,0,(-1),false,379,608⟩,
⟨.mixed,38,1,(-1),false,375,608⟩,
⟨.mixed,39,0,(-1),false,383,644⟩,
⟨.mixed,40,0,(-1),false,417,746⟩,
⟨.mixed,41,0,(-1),false,318,602⟩,
⟨.mixed,42,0,(-1),false,316,620⟩,
⟨.mixed,42,1,(-1),false,314,620⟩,
⟨.mixed,43,0,(-1),false,320,668⟩,
⟨.mixed,44,0,(-1),false,413,1042⟩,
⟨.mixed,45,0,(-1),false,167,626⟩,
⟨.mixed,46,0,(-1),false,166,656⟩,
⟨.mixed,46,1,(-1),false,165,656⟩,
⟨.mixed,47,0,(-1),false,169,698⟩,
⟨.mixed,48,0,(-1),false,414,54⟩,
⟨.mixed,49,0,(-1),false,9,203⟩,
⟨.mixed,50,0,(-1),false,8,209⟩,
⟨.mixed,50,1,(-1),false,7,209⟩,
⟨.mixed,51,0,(-1),false,11,215⟩,
⟨.mixed,52,0,(-1),false,517,296⟩,
⟨.mixed,53,0,(-1),false,223,1071⟩,
⟨.mixed,54,0,(-1),false,231,1083⟩,
⟨.mixed,54,1,(-1),false,229,1083⟩,
⟨.mixed,55,0,(-1),false,235,1107⟩,
⟨.mixed,56,0,(-1),false,120,1077⟩,
⟨.mixed,57,0,(-1),false,132,1095⟩,
⟨.mixed,57,1,(-1),false,129,1095⟩,
⟨.mixed,58,0,(-1),false,157,1119⟩,
⟨.mixed,59,0,(-1),false,342,583⟩,
⟨.mixed,60,0,(-1),false,341,595⟩,
⟨.mixed,60,1,(-1),false,340,595⟩,
⟨.mixed,61,0,(-1),false,343,631⟩,
⟨.mixed,62,0,(-1),false,435,1012⟩,
⟨.mixed,63,0,(-1),false,224,649⟩,
⟨.mixed,64,0,(-1),false,232,691⟩,
⟨.mixed,64,1,(-1),false,230,691⟩,
⟨.mixed,65,0,(-1),false,236,751⟩,
⟨.mixed,66,0,(-1),false,276,589⟩,
⟨.mixed,66,1,(-1),false,274,589⟩,
⟨.mixed,66,2,(-1),false,275,589⟩,
⟨.mixed,66,3,(-1),false,273,589⟩,
⟨.mixed,67,0,(-1),false,272,613⟩,
⟨.mixed,67,1,(-1),false,268,613⟩,
⟨.mixed,67,2,(-1),false,270,613⟩,
⟨.mixed,67,3,(-1),false,266,613⟩,
⟨.mixed,67,4,(-1),false,271,613⟩,
⟨.mixed,67,5,(-1),false,267,613⟩,
⟨.mixed,67,6,(-1),false,269,613⟩,
⟨.mixed,67,7,(-1),false,265,613⟩,
⟨.mixed,68,0,(-1),false,280,661⟩,
⟨.mixed,68,1,(-1),false,278,661⟩,
⟨.mixed,68,2,(-1),false,279,661⟩,
⟨.mixed,68,3,(-1),false,277,661⟩,
⟨.mixed,69,0,(-1),false,439,1029⟩,
⟨.mixed,69,1,(-1),false,437,721⟩,
⟨.mixed,69,2,(-1),false,438,1029⟩,
⟨.mixed,69,3,(-1),false,436,721⟩,
⟨.mixed,70,0,(-1),false,121,685⟩,
⟨.mixed,70,1,(-1),false,119,685⟩,
⟨.mixed,71,0,(-1),false,133,727⟩,
⟨.mixed,71,1,(-1),false,130,727⟩,
⟨.mixed,71,2,(-1),false,131,727⟩,
⟨.mixed,71,3,(-1),false,128,727⟩,
⟨.mixed,72,0,(-1),false,158,775⟩,
⟨.mixed,72,1,(-1),false,156,775⟩,
⟨.mixed,73,0,(-1),false,188,625⟩,
⟨.mixed,73,1,(-1),false,187,79⟩,
⟨.mixed,74,0,(-1),false,186,655⟩,
⟨.mixed,74,1,(-1),false,184,655⟩,
⟨.mixed,74,2,(-1),false,185,85⟩,
⟨.mixed,74,3,(-1),false,183,85⟩,
⟨.mixed,75,0,(-1),false,192,697⟩,
⟨.mixed,75,1,(-1),false,191,91⟩,
⟨.mixed,76,0,0,false,492,71⟩,
⟨.mixed,76,0,1,false,484,71⟩,
⟨.mixed,76,0,2,false,460,27⟩,
⟨.mixed,76,0,3,false,480,557⟩,
⟨.mixed,76,0,4,false,482,174⟩,
⟨.mixed,76,0,5,false,449,75⟩,
⟨.mixed,76,0,6,false,447,75⟩,
⟨.mixed,76,0,7,false,441,31⟩,
⟨.mixed,76,0,8,false,445,561⟩,
⟨.mixed,76,0,9,false,446,178⟩,
⟨.mixed,76,0,10,false,488,313⟩,
⟨.mixed,76,0,11,false,472,313⟩,
⟨.mixed,76,0,12,false,456,17⟩,
⟨.mixed,76,0,13,false,468,547⟩,
⟨.mixed,76,0,14,false,469,164⟩,
⟨.mixed,76,0,15,false,489,59⟩,
⟨.mixed,76,0,16,false,473,59⟩,
⟨.mixed,76,0,17,false,457,21⟩,
⟨.mixed,76,0,18,false,470,551⟩,
⟨.mixed,76,0,19,false,471,168⟩,
⟨.mixed,76,1,0,false,490,154⟩,
⟨.mixed,76,1,1,false,478,154⟩,
⟨.mixed,76,1,2,false,458,27⟩,
⟨.mixed,76,1,3,false,474,557⟩,
⟨.mixed,76,1,4,false,476,174⟩,
⟨.mixed,76,1,5,false,448,158⟩,
⟨.mixed,76,1,6,false,444,158⟩,
⟨.mixed,76,1,7,false,440,31⟩,
⟨.mixed,76,1,8,false,442,561⟩,
⟨.mixed,76,1,9,false,443,178⟩,
⟨.mixed,76,1,10,false,486,109⟩,
⟨.mixed,76,1,11,false,466,109⟩,
⟨.mixed,76,1,12,false,454,17⟩,
⟨.mixed,76,1,13,false,462,547⟩,
⟨.mixed,76,1,14,false,463,164⟩,
⟨.mixed,76,1,15,false,487,112⟩,
⟨.mixed,76,1,16,false,467,112⟩,
⟨.mixed,76,1,17,false,455,21⟩,
⟨.mixed,76,1,18,false,464,551⟩,
⟨.mixed,76,1,19,false,465,168⟩,
⟨.mixed,77,0,(-1),false,45,745⟩,
⟨.mixed,78,0,(-1),false,44,763⟩,
⟨.mixed,78,1,(-1),false,43,763⟩,
⟨.mixed,79,0,0,false,74,71⟩,
⟨.mixed,79,0,1,false,70,71⟩,
⟨.mixed,79,0,2,false,58,27⟩,
⟨.mixed,79,0,3,false,66,557⟩,
⟨.mixed,79,0,4,false,68,174⟩,
⟨.mixed,79,0,5,false,50,75⟩,
⟨.mixed,79,0,6,false,49,75⟩,
⟨.mixed,79,0,7,false,46,31⟩,
⟨.mixed,79,0,8,false,47,561⟩,
⟨.mixed,79,0,9,false,48,178⟩,
⟨.mixed,79,0,10,false,72,313⟩,
⟨.mixed,79,0,11,false,64,313⟩,
⟨.mixed,79,0,12,false,56,17⟩,
⟨.mixed,79,0,13,false,60,547⟩,
⟨.mixed,79,0,14,false,61,164⟩,
⟨.mixed,79,0,15,false,73,59⟩,
⟨.mixed,79,0,16,false,65,59⟩,
⟨.mixed,79,0,17,false,57,21⟩,
⟨.mixed,79,0,18,false,62,551⟩,
⟨.mixed,79,0,19,false,63,168⟩,
⟨.mixed,80,0,(-1),false,415,745⟩,
⟨.mixed,80,1,(-1),false,410,745⟩,
⟨.mixed,80,2,(-1),false,416,745⟩,
⟨.mixed,81,0,(-1),false,377,607⟩,
⟨.mixed,81,1,(-1),false,373,607⟩,
⟨.mixed,81,2,(-1),false,376,607⟩,
⟨.mixed,81,3,(-1),false,372,607⟩,
⟨.mixed,81,4,(-1),false,378,607⟩,
⟨.mixed,81,5,(-1),false,374,607⟩,
⟨.mixed,82,0,(-1),false,381,643⟩,
⟨.mixed,82,1,(-1),false,380,643⟩,
⟨.mixed,82,2,(-1),false,382,643⟩,
⟨.mixed,83,0,(-1),false,412,763⟩,
⟨.mixed,84,0,(-1),false,317,601⟩,
⟨.mixed,85,0,(-1),false,315,619⟩,
⟨.mixed,85,1,(-1),false,313,619⟩,
⟨.mixed,86,0,(-1),false,319,667⟩,
⟨.mixed,87,0,(-1),false,33,745⟩,
⟨.mixed,88,0,(-1),false,32,763⟩,
⟨.mixed,88,1,(-1),false,31,763⟩,
⟨.mixed,89,0,(-1),false,35,53⟩,
⟨.mixed,90,0,(-1),false,379,607⟩,
⟨.mixed,90,1,(-1),false,375,607⟩,
⟨.mixed,91,0,(-1),false,383,643⟩,
⟨.mixed,92,0,(-1),false,417,745⟩,
⟨.mixed,93,0,(-1),false,318,601⟩,
⟨.mixed,94,0,(-1),false,316,619⟩,
⟨.mixed,94,1,(-1),false,314,619⟩,
⟨.mixed,95,0,(-1),false,320,667⟩,
⟨.mixed,96,0,(-1),false,413,1041⟩,
⟨.mixed,97,0,(-1),false,167,625⟩,
⟨.mixed,98,0,(-1),false,166,655⟩,
⟨.mixed,98,1,(-1),false,165,655⟩,
⟨.mixed,99,0,(-1),false,169,697⟩,
⟨.mixed,100,0,(-1),false,414,53⟩,
⟨.mixed,101,0,(-1),false,9,202⟩,
⟨.mixed,102,0,(-1),false,8,208⟩,
⟨.mixed,102,1,(-1),false,7,208⟩,
⟨.mixed,103,0,(-1),false,11,220⟩,
⟨.mixed,104,0,(-1),false,517,295⟩,
⟨.mixed,105,0,(-1),false,223,1069⟩,
⟨.mixed,106,0,(-1),false,231,1081⟩,
⟨.mixed,106,1,(-1),false,229,1081⟩,
⟨.mixed,107,0,(-1),false,235,1105⟩,
⟨.mixed,108,0,(-1),false,120,1075⟩,
⟨.mixed,109,0,(-1),false,132,1093⟩,
⟨.mixed,109,1,(-1),false,129,1093⟩,
⟨.mixed,110,0,(-1),false,157,1117⟩,
⟨.mixed,111,0,(-1),false,342,581⟩,
⟨.mixed,112,0,(-1),false,341,593⟩,
⟨.mixed,112,1,(-1),false,340,593⟩,
⟨.mixed,113,0,(-1),false,343,629⟩,
⟨.mixed,114,0,(-1),false,435,1010⟩,
⟨.mixed,115,0,(-1),false,224,647⟩,
⟨.mixed,116,0,(-1),false,232,689⟩,
⟨.mixed,116,1,(-1),false,230,689⟩,
⟨.mixed,117,0,(-1),false,236,749⟩,
⟨.mixed,118,0,(-1),false,276,587⟩,
⟨.mixed,118,1,(-1),false,274,587⟩,
⟨.mixed,118,2,(-1),false,275,587⟩,
⟨.mixed,118,3,(-1),false,273,587⟩,
⟨.mixed,119,0,(-1),false,272,611⟩,
⟨.mixed,119,1,(-1),false,268,611⟩,
⟨.mixed,119,2,(-1),false,270,611⟩,
⟨.mixed,119,3,(-1),false,266,611⟩,
⟨.mixed,119,4,(-1),false,271,611⟩,
⟨.mixed,119,5,(-1),false,267,611⟩,
⟨.mixed,119,6,(-1),false,269,611⟩,
⟨.mixed,119,7,(-1),false,265,611⟩,
⟨.mixed,120,0,(-1),false,280,659⟩,
⟨.mixed,120,1,(-1),false,278,659⟩,
⟨.mixed,120,2,(-1),false,279,659⟩,
⟨.mixed,120,3,(-1),false,277,659⟩,
⟨.mixed,121,0,(-1),false,439,1027⟩,
⟨.mixed,121,1,(-1),false,437,719⟩,
⟨.mixed,121,2,(-1),false,438,1027⟩,
⟨.mixed,121,3,(-1),false,436,719⟩,
⟨.mixed,122,0,(-1),false,121,683⟩,
⟨.mixed,122,1,(-1),false,119,683⟩,
⟨.mixed,123,0,(-1),false,133,725⟩,
⟨.mixed,123,1,(-1),false,130,725⟩,
⟨.mixed,123,2,(-1),false,131,725⟩,
⟨.mixed,123,3,(-1),false,128,725⟩,
⟨.mixed,124,0,(-1),false,158,773⟩,
⟨.mixed,124,1,(-1),false,156,773⟩,
⟨.mixed,125,0,(-1),false,188,623⟩,
⟨.mixed,125,1,(-1),false,187,77⟩,
⟨.mixed,126,0,(-1),false,186,653⟩,
⟨.mixed,126,1,(-1),false,184,653⟩,
⟨.mixed,126,2,(-1),false,185,83⟩,
⟨.mixed,126,3,(-1),false,183,83⟩,
⟨.mixed,127,0,(-1),false,192,695⟩,
⟨.mixed,127,1,(-1),false,191,89⟩,
⟨.mixed,128,0,0,false,492,69⟩,
⟨.mixed,128,0,1,false,484,69⟩,
⟨.mixed,128,0,2,false,460,25⟩,
⟨.mixed,128,0,3,false,480,555⟩,
⟨.mixed,128,0,4,false,482,172⟩,
⟨.mixed,128,0,5,false,449,73⟩,
⟨.mixed,128,0,6,false,447,73⟩,
⟨.mixed,128,0,7,false,441,29⟩,
⟨.mixed,128,0,8,false,445,559⟩,
⟨.mixed,128,0,9,false,446,176⟩,
⟨.mixed,128,0,10,false,488,311⟩,
⟨.mixed,128,0,11,false,472,311⟩,
⟨.mixed,128,0,12,false,456,15⟩,
⟨.mixed,128,0,13,false,468,545⟩,
⟨.mixed,128,0,14,false,469,162⟩,
⟨.mixed,128,0,15,false,489,57⟩,
⟨.mixed,128,0,16,false,473,57⟩,
⟨.mixed,128,0,17,false,457,19⟩,
⟨.mixed,128,0,18,false,470,549⟩,
⟨.mixed,128,0,19,false,471,166⟩,
⟨.mixed,128,1,0,false,490,152⟩,
⟨.mixed,128,1,1,false,478,152⟩,
⟨.mixed,128,1,2,false,458,25⟩,
⟨.mixed,128,1,3,false,474,555⟩,
⟨.mixed,128,1,4,false,476,172⟩,
⟨.mixed,128,1,5,false,448,156⟩,
⟨.mixed,128,1,6,false,444,156⟩,
⟨.mixed,128,1,7,false,440,29⟩,
⟨.mixed,128,1,8,false,442,559⟩,
⟨.mixed,128,1,9,false,443,176⟩,
⟨.mixed,128,1,10,false,486,107⟩,
⟨.mixed,128,1,11,false,466,107⟩,
⟨.mixed,128,1,12,false,454,15⟩,
⟨.mixed,128,1,13,false,462,545⟩,
⟨.mixed,128,1,14,false,463,162⟩,
⟨.mixed,128,1,15,false,487,110⟩,
⟨.mixed,128,1,16,false,467,110⟩,
⟨.mixed,128,1,17,false,455,19⟩,
⟨.mixed,128,1,18,false,464,549⟩,
⟨.mixed,128,1,19,false,465,166⟩,
⟨.mixed,129,0,(-1),false,45,743⟩,
⟨.mixed,130,0,(-1),false,44,761⟩,
⟨.mixed,130,1,(-1),false,43,761⟩,
⟨.mixed,131,0,0,false,74,69⟩,
⟨.mixed,131,0,1,false,70,69⟩,
⟨.mixed,131,0,2,false,58,25⟩,
⟨.mixed,131,0,3,false,66,555⟩,
⟨.mixed,131,0,4,false,68,172⟩,
⟨.mixed,131,0,5,false,50,73⟩,
⟨.mixed,131,0,6,false,49,73⟩,
⟨.mixed,131,0,7,false,46,29⟩,
⟨.mixed,131,0,8,false,47,559⟩,
⟨.mixed,131,0,9,false,48,176⟩,
⟨.mixed,131,0,10,false,72,311⟩,
⟨.mixed,131,0,11,false,64,311⟩,
⟨.mixed,131,0,12,false,56,15⟩,
⟨.mixed,131,0,13,false,60,545⟩,
⟨.mixed,131,0,14,false,61,162⟩,
⟨.mixed,131,0,15,false,73,57⟩,
⟨.mixed,131,0,16,false,65,57⟩,
⟨.mixed,131,0,17,false,57,19⟩,
⟨.mixed,131,0,18,false,62,549⟩,
⟨.mixed,131,0,19,false,63,166⟩,
⟨.mixed,132,0,(-1),false,415,743⟩,
⟨.mixed,132,1,(-1),false,410,743⟩,
⟨.mixed,132,2,(-1),false,416,743⟩,
⟨.mixed,133,0,(-1),false,377,605⟩,
⟨.mixed,133,1,(-1),false,373,605⟩,
⟨.mixed,133,2,(-1),false,376,605⟩,
⟨.mixed,133,3,(-1),false,372,605⟩,
⟨.mixed,133,4,(-1),false,378,605⟩,
⟨.mixed,133,5,(-1),false,374,605⟩,
⟨.mixed,134,0,(-1),false,381,641⟩,
⟨.mixed,134,1,(-1),false,380,641⟩,
⟨.mixed,134,2,(-1),false,382,641⟩,
⟨.mixed,135,0,(-1),false,412,761⟩,
⟨.mixed,136,0,(-1),false,317,599⟩,
⟨.mixed,137,0,(-1),false,315,617⟩,
⟨.mixed,137,1,(-1),false,313,617⟩,
⟨.mixed,138,0,(-1),false,319,665⟩,
⟨.mixed,139,0,(-1),false,33,743⟩,
⟨.mixed,140,0,(-1),false,32,761⟩,
⟨.mixed,140,1,(-1),false,31,761⟩,
⟨.mixed,141,0,(-1),false,35,51⟩,
⟨.mixed,142,0,(-1),false,379,605⟩,
⟨.mixed,142,1,(-1),false,375,605⟩,
⟨.mixed,143,0,(-1),false,383,641⟩,
⟨.mixed,144,0,(-1),false,417,743⟩,
⟨.mixed,145,0,(-1),false,318,599⟩,
⟨.mixed,146,0,(-1),false,316,617⟩,
⟨.mixed,146,1,(-1),false,314,617⟩,
⟨.mixed,147,0,(-1),false,320,665⟩,
⟨.mixed,148,0,(-1),false,413,1039⟩,
⟨.mixed,149,0,(-1),false,167,623⟩,
⟨.mixed,150,0,(-1),false,166,653⟩,
⟨.mixed,150,1,(-1),false,165,653⟩,
⟨.mixed,151,0,(-1),false,169,695⟩,
⟨.mixed,152,0,(-1),false,414,51⟩,
⟨.mixed,153,0,(-1),false,9,200⟩,
⟨.mixed,154,0,(-1),false,8,206⟩,
⟨.mixed,154,1,(-1),false,7,206⟩,
⟨.mixed,155,0,(-1),false,11,218⟩,
⟨.mixed,156,0,(-1),false,517,293⟩,
⟨.mixed,157,0,(-1),false,223,1073⟩,
⟨.mixed,158,0,(-1),false,231,1085⟩,
⟨.mixed,158,1,(-1),false,229,1085⟩,
⟨.mixed,159,0,(-1),false,235,1109⟩,
⟨.mixed,160,0,(-1),false,120,1079⟩,
⟨.mixed,161,0,(-1),false,132,1097⟩,
⟨.mixed,161,1,(-1),false,129,1097⟩,
⟨.mixed,162,0,(-1),false,157,1121⟩,
⟨.mixed,163,0,(-1),false,342,585⟩,
⟨.mixed,164,0,(-1),false,341,597⟩,
⟨.mixed,164,1,(-1),false,340,597⟩,
⟨.mixed,165,0,(-1),false,343,633⟩,
⟨.mixed,166,0,(-1),false,435,1014⟩,
⟨.mixed,167,0,(-1),false,224,651⟩,
⟨.mixed,168,0,(-1),false,232,693⟩,
⟨.mixed,168,1,(-1),false,230,693⟩,
⟨.mixed,169,0,(-1),false,236,753⟩,
⟨.mixed,170,0,(-1),false,276,591⟩,
⟨.mixed,170,1,(-1),false,274,591⟩,
⟨.mixed,170,2,(-1),false,275,591⟩,
⟨.mixed,170,3,(-1),false,273,591⟩,
⟨.mixed,171,0,(-1),false,272,615⟩,
⟨.mixed,171,1,(-1),false,268,615⟩,
⟨.mixed,171,2,(-1),false,270,615⟩,
⟨.mixed,171,3,(-1),false,266,615⟩,
⟨.mixed,171,4,(-1),false,271,615⟩,
⟨.mixed,171,5,(-1),false,267,615⟩,
⟨.mixed,171,6,(-1),false,269,615⟩,
⟨.mixed,171,7,(-1),false,265,615⟩,
⟨.mixed,172,0,(-1),false,280,663⟩,
⟨.mixed,172,1,(-1),false,278,663⟩,
⟨.mixed,172,2,(-1),false,279,663⟩,
⟨.mixed,172,3,(-1),false,277,663⟩,
⟨.mixed,173,0,(-1),false,439,1031⟩,
⟨.mixed,173,1,(-1),false,437,723⟩,
⟨.mixed,173,2,(-1),false,438,1031⟩,
⟨.mixed,173,3,(-1),false,436,723⟩,
⟨.mixed,174,0,(-1),false,121,687⟩,
⟨.mixed,174,1,(-1),false,119,687⟩,
⟨.mixed,175,0,(-1),false,133,729⟩,
⟨.mixed,175,1,(-1),false,130,729⟩,
⟨.mixed,175,2,(-1),false,131,729⟩,
⟨.mixed,175,3,(-1),false,128,729⟩,
⟨.mixed,176,0,(-1),false,158,777⟩,
⟨.mixed,176,1,(-1),false,156,777⟩,
⟨.mixed,177,0,(-1),false,188,627⟩,
⟨.mixed,177,1,(-1),false,187,81⟩,
⟨.mixed,178,0,(-1),false,186,657⟩,
⟨.mixed,178,1,(-1),false,184,657⟩,
⟨.mixed,178,2,(-1),false,185,87⟩,
⟨.mixed,178,3,(-1),false,183,87⟩,
⟨.mixed,179,0,(-1),false,192,699⟩,
⟨.mixed,179,1,(-1),false,191,93⟩,
⟨.mixed,180,0,0,false,493,61⟩,
⟨.mixed,180,0,1,false,485,61⟩,
⟨.mixed,180,0,2,false,461,23⟩,
⟨.mixed,180,0,3,false,481,553⟩,
⟨.mixed,180,0,4,false,483,170⟩,
⟨.mixed,180,1,0,false,491,114⟩,
⟨.mixed,180,1,1,false,479,114⟩,
⟨.mixed,180,1,2,false,459,23⟩,
⟨.mixed,180,1,3,false,475,553⟩,
⟨.mixed,180,1,4,false,477,170⟩,
⟨.mixed,181,0,(-1),false,45,747⟩,
⟨.mixed,182,0,(-1),false,44,765⟩,
⟨.mixed,182,1,(-1),false,43,765⟩,
⟨.mixed,183,0,0,false,75,61⟩,
⟨.mixed,183,0,1,false,71,61⟩,
⟨.mixed,183,0,2,false,59,23⟩,
⟨.mixed,183,0,3,false,67,553⟩,
⟨.mixed,183,0,4,false,69,170⟩,
⟨.mixed,184,0,(-1),false,415,747⟩,
⟨.mixed,184,1,(-1),false,410,747⟩,
⟨.mixed,184,2,(-1),false,416,747⟩,
⟨.mixed,185,0,(-1),false,377,609⟩,
⟨.mixed,185,1,(-1),false,373,609⟩,
⟨.mixed,185,2,(-1),false,376,609⟩,
⟨.mixed,185,3,(-1),false,372,609⟩,
⟨.mixed,185,4,(-1),false,378,609⟩,
⟨.mixed,185,5,(-1),false,374,609⟩,
⟨.mixed,186,0,(-1),false,381,645⟩,
⟨.mixed,186,1,(-1),false,380,645⟩,
⟨.mixed,186,2,(-1),false,382,645⟩,
⟨.mixed,187,0,(-1),false,412,765⟩,
⟨.mixed,188,0,(-1),false,317,603⟩,
⟨.mixed,189,0,(-1),false,315,621⟩,
⟨.mixed,189,1,(-1),false,313,621⟩,
⟨.mixed,190,0,(-1),false,319,669⟩,
⟨.mixed,191,0,(-1),false,33,747⟩,
⟨.mixed,192,0,(-1),false,32,765⟩,
⟨.mixed,192,1,(-1),false,31,765⟩,
⟨.mixed,193,0,(-1),false,35,55⟩,
⟨.mixed,194,0,(-1),false,379,609⟩,
⟨.mixed,194,1,(-1),false,375,609⟩,
⟨.mixed,195,0,(-1),false,383,645⟩,
⟨.mixed,196,0,(-1),false,417,747⟩,
⟨.mixed,197,0,(-1),false,318,603⟩,
⟨.mixed,198,0,(-1),false,316,621⟩,
⟨.mixed,198,1,(-1),false,314,621⟩,
⟨.mixed,199,0,(-1),false,320,669⟩,
⟨.mixed,200,0,(-1),false,413,1043⟩,
⟨.mixed,201,0,(-1),false,167,627⟩,
⟨.mixed,202,0,(-1),false,166,657⟩,
⟨.mixed,202,1,(-1),false,165,657⟩,
⟨.mixed,203,0,(-1),false,169,699⟩,
⟨.mixed,204,0,(-1),false,414,55⟩,
⟨.mixed,205,0,(-1),false,9,204⟩,
⟨.mixed,206,0,(-1),false,8,210⟩,
⟨.mixed,206,1,(-1),false,7,210⟩,
⟨.mixed,207,0,(-1),false,11,216⟩,
⟨.mixed,208,0,(-1),false,517,297⟩,
⟨.mixed,209,0,(-1),false,223,1070⟩,
⟨.mixed,210,0,(-1),false,231,1082⟩,
⟨.mixed,210,1,(-1),false,229,1082⟩,
⟨.mixed,211,0,(-1),false,235,1106⟩,
⟨.mixed,212,0,(-1),false,120,1076⟩,
⟨.mixed,213,0,(-1),false,132,1094⟩,
⟨.mixed,213,1,(-1),false,129,1094⟩,
⟨.mixed,214,0,(-1),false,157,1118⟩,
⟨.mixed,215,0,(-1),false,342,582⟩,
⟨.mixed,216,0,(-1),false,341,594⟩,
⟨.mixed,216,1,(-1),false,340,594⟩,
⟨.mixed,217,0,(-1),false,343,630⟩,
⟨.mixed,218,0,(-1),false,435,1011⟩,
⟨.mixed,219,0,(-1),false,224,648⟩,
⟨.mixed,220,0,(-1),false,232,690⟩,
⟨.mixed,220,1,(-1),false,230,690⟩,
⟨.mixed,221,0,(-1),false,236,750⟩,
⟨.mixed,222,0,(-1),false,276,588⟩,
⟨.mixed,222,1,(-1),false,274,588⟩,
⟨.mixed,222,2,(-1),false,275,588⟩,
⟨.mixed,222,3,(-1),false,273,588⟩,
⟨.mixed,223,0,(-1),false,272,612⟩,
⟨.mixed,223,1,(-1),false,268,612⟩,
⟨.mixed,223,2,(-1),false,270,612⟩,
⟨.mixed,223,3,(-1),false,266,612⟩,
⟨.mixed,223,4,(-1),false,271,612⟩,
⟨.mixed,223,5,(-1),false,267,612⟩,
⟨.mixed,223,6,(-1),false,269,612⟩,
⟨.mixed,223,7,(-1),false,265,612⟩,
⟨.mixed,224,0,(-1),false,280,660⟩,
⟨.mixed,224,1,(-1),false,278,660⟩,
⟨.mixed,224,2,(-1),false,279,660⟩,
⟨.mixed,224,3,(-1),false,277,660⟩,
⟨.mixed,225,0,(-1),false,439,1028⟩,
⟨.mixed,225,1,(-1),false,437,720⟩,
⟨.mixed,225,2,(-1),false,438,1028⟩,
⟨.mixed,225,3,(-1),false,436,720⟩,
⟨.mixed,226,0,(-1),false,121,684⟩,
⟨.mixed,226,1,(-1),false,119,684⟩,
⟨.mixed,227,0,(-1),false,133,726⟩,
⟨.mixed,227,1,(-1),false,130,726⟩,
⟨.mixed,227,2,(-1),false,131,726⟩,
⟨.mixed,227,3,(-1),false,128,726⟩,
⟨.mixed,228,0,(-1),false,158,774⟩,
⟨.mixed,228,1,(-1),false,156,774⟩,
⟨.mixed,229,0,(-1),false,188,624⟩,
⟨.mixed,229,1,(-1),false,187,78⟩,
⟨.mixed,230,0,(-1),false,186,654⟩,
⟨.mixed,230,1,(-1),false,184,654⟩,
⟨.mixed,230,2,(-1),false,185,84⟩,
⟨.mixed,230,3,(-1),false,183,84⟩,
⟨.mixed,231,0,(-1),false,192,696⟩,
⟨.mixed,231,1,(-1),false,191,90⟩,
⟨.mixed,232,0,0,false,492,70⟩,
⟨.mixed,232,0,1,false,484,70⟩,
⟨.mixed,232,0,2,false,460,26⟩,
⟨.mixed,232,0,3,false,480,556⟩,
⟨.mixed,232,0,4,false,482,173⟩,
⟨.mixed,232,0,5,false,449,74⟩,
⟨.mixed,232,0,6,false,447,74⟩,
⟨.mixed,232,0,7,false,441,30⟩,
⟨.mixed,232,0,8,false,445,560⟩,
⟨.mixed,232,0,9,false,446,177⟩,
⟨.mixed,232,0,10,false,488,312⟩,
⟨.mixed,232,0,11,false,472,312⟩,
⟨.mixed,232,0,12,false,456,16⟩,
⟨.mixed,232,0,13,false,468,546⟩,
⟨.mixed,232,0,14,false,469,163⟩,
⟨.mixed,232,0,15,false,489,58⟩,
⟨.mixed,232,0,16,false,473,58⟩,
⟨.mixed,232,0,17,false,457,20⟩,
⟨.mixed,232,0,18,false,470,550⟩,
⟨.mixed,232,0,19,false,471,167⟩,
⟨.mixed,232,1,0,false,490,153⟩,
⟨.mixed,232,1,1,false,478,153⟩,
⟨.mixed,232,1,2,false,458,26⟩,
⟨.mixed,232,1,3,false,474,556⟩,
⟨.mixed,232,1,4,false,476,173⟩,
⟨.mixed,232,1,5,false,448,157⟩,
⟨.mixed,232,1,6,false,444,157⟩,
⟨.mixed,232,1,7,false,440,30⟩,
⟨.mixed,232,1,8,false,442,560⟩,
⟨.mixed,232,1,9,false,443,177⟩,
⟨.mixed,232,1,10,false,486,108⟩,
⟨.mixed,232,1,11,false,466,108⟩,
⟨.mixed,232,1,12,false,454,16⟩,
⟨.mixed,232,1,13,false,462,546⟩,
⟨.mixed,232,1,14,false,463,163⟩,
⟨.mixed,232,1,15,false,487,111⟩,
⟨.mixed,232,1,16,false,467,111⟩,
⟨.mixed,232,1,17,false,455,20⟩,
⟨.mixed,232,1,18,false,464,550⟩,
⟨.mixed,232,1,19,false,465,167⟩,
⟨.mixed,233,0,(-1),false,45,744⟩,
⟨.mixed,234,0,(-1),false,44,762⟩,
⟨.mixed,234,1,(-1),false,43,762⟩,
⟨.mixed,235,0,0,false,74,70⟩,
⟨.mixed,235,0,1,false,70,70⟩,
⟨.mixed,235,0,2,false,58,26⟩,
⟨.mixed,235,0,3,false,66,556⟩,
⟨.mixed,235,0,4,false,68,173⟩,
⟨.mixed,235,0,5,false,50,74⟩,
⟨.mixed,235,0,6,false,49,74⟩,
⟨.mixed,235,0,7,false,46,30⟩,
⟨.mixed,235,0,8,false,47,560⟩,
⟨.mixed,235,0,9,false,48,177⟩,
⟨.mixed,235,0,10,false,72,312⟩,
⟨.mixed,235,0,11,false,64,312⟩,
⟨.mixed,235,0,12,false,56,16⟩,
⟨.mixed,235,0,13,false,60,546⟩,
⟨.mixed,235,0,14,false,61,163⟩,
⟨.mixed,235,0,15,false,73,58⟩,
⟨.mixed,235,0,16,false,65,58⟩,
⟨.mixed,235,0,17,false,57,20⟩,
⟨.mixed,235,0,18,false,62,550⟩,
⟨.mixed,235,0,19,false,63,167⟩,
⟨.mixed,236,0,(-1),false,415,744⟩,
⟨.mixed,236,1,(-1),false,410,744⟩,
⟨.mixed,236,2,(-1),false,416,744⟩,
⟨.mixed,237,0,(-1),false,377,606⟩,
⟨.mixed,237,1,(-1),false,373,606⟩,
⟨.mixed,237,2,(-1),false,376,606⟩,
⟨.mixed,237,3,(-1),false,372,606⟩,
⟨.mixed,237,4,(-1),false,378,606⟩,
⟨.mixed,237,5,(-1),false,374,606⟩,
⟨.mixed,238,0,(-1),false,381,642⟩,
⟨.mixed,238,1,(-1),false,380,642⟩,
⟨.mixed,238,2,(-1),false,382,642⟩,
⟨.mixed,239,0,(-1),false,412,762⟩,
⟨.mixed,240,0,(-1),false,317,600⟩,
⟨.mixed,241,0,(-1),false,315,618⟩,
⟨.mixed,241,1,(-1),false,313,618⟩,
⟨.mixed,242,0,(-1),false,319,666⟩,
⟨.mixed,243,0,(-1),false,33,744⟩,
⟨.mixed,244,0,(-1),false,32,762⟩,
⟨.mixed,244,1,(-1),false,31,762⟩,
⟨.mixed,245,0,(-1),false,35,52⟩,
⟨.mixed,246,0,(-1),false,379,606⟩,
⟨.mixed,246,1,(-1),false,375,606⟩,
⟨.mixed,247,0,(-1),false,383,642⟩,
⟨.mixed,248,0,(-1),false,417,744⟩,
⟨.mixed,249,0,(-1),false,318,600⟩,
⟨.mixed,250,0,(-1),false,316,618⟩,
⟨.mixed,250,1,(-1),false,314,618⟩,
⟨.mixed,251,0,(-1),false,320,666⟩,
⟨.mixed,252,0,(-1),false,413,1040⟩,
⟨.mixed,253,0,(-1),false,167,624⟩,
⟨.mixed,254,0,(-1),false,166,654⟩,
⟨.mixed,254,1,(-1),false,165,654⟩,
⟨.mixed,255,0,(-1),false,169,696⟩,
⟨.mixed,256,0,(-1),false,414,52⟩,
⟨.mixed,257,0,(-1),false,9,201⟩,
⟨.mixed,258,0,(-1),false,8,207⟩,
⟨.mixed,258,1,(-1),false,7,207⟩,
⟨.mixed,259,0,(-1),false,11,219⟩,
⟨.mixed,260,0,(-1),false,517,294⟩,
⟨.mixed,261,0,(-1),false,223,1074⟩,
⟨.mixed,262,0,(-1),false,231,1086⟩,
⟨.mixed,262,1,(-1),false,229,1086⟩,
⟨.mixed,263,0,(-1),false,235,1110⟩,
⟨.mixed,264,0,(-1),false,120,1080⟩,
⟨.mixed,265,0,(-1),false,132,1098⟩,
⟨.mixed,265,1,(-1),false,129,1098⟩,
⟨.mixed,266,0,(-1),false,157,1122⟩,
⟨.mixed,267,0,(-1),false,342,586⟩,
⟨.mixed,268,0,(-1),false,341,598⟩,
⟨.mixed,268,1,(-1),false,340,598⟩,
⟨.mixed,269,0,(-1),false,343,634⟩,
⟨.mixed,270,0,(-1),false,435,1015⟩,
⟨.mixed,271,0,(-1),false,224,652⟩,
⟨.mixed,272,0,(-1),false,232,694⟩,
⟨.mixed,272,1,(-1),false,230,694⟩,
⟨.mixed,273,0,(-1),false,236,754⟩,
⟨.mixed,274,0,(-1),false,276,592⟩,
⟨.mixed,274,1,(-1),false,274,592⟩,
⟨.mixed,274,2,(-1),false,275,592⟩,
⟨.mixed,274,3,(-1),false,273,592⟩,
⟨.mixed,275,0,(-1),false,272,616⟩,
⟨.mixed,275,1,(-1),false,268,616⟩,
⟨.mixed,275,2,(-1),false,270,616⟩,
⟨.mixed,275,3,(-1),false,266,616⟩,
⟨.mixed,275,4,(-1),false,271,616⟩,
⟨.mixed,275,5,(-1),false,267,616⟩,
⟨.mixed,275,6,(-1),false,269,616⟩,
⟨.mixed,275,7,(-1),false,265,616⟩,
⟨.mixed,276,0,(-1),false,280,664⟩,
⟨.mixed,276,1,(-1),false,278,664⟩,
⟨.mixed,276,2,(-1),false,279,664⟩,
⟨.mixed,276,3,(-1),false,277,664⟩,
⟨.mixed,277,0,(-1),false,439,1032⟩,
⟨.mixed,277,1,(-1),false,437,724⟩,
⟨.mixed,277,2,(-1),false,438,1032⟩,
⟨.mixed,277,3,(-1),false,436,724⟩,
⟨.mixed,278,0,(-1),false,121,688⟩,
⟨.mixed,278,1,(-1),false,119,688⟩,
⟨.mixed,279,0,(-1),false,133,730⟩,
⟨.mixed,279,1,(-1),false,130,730⟩,
⟨.mixed,279,2,(-1),false,131,730⟩,
⟨.mixed,279,3,(-1),false,128,730⟩,
⟨.mixed,280,0,(-1),false,158,778⟩,
⟨.mixed,280,1,(-1),false,156,778⟩,
⟨.mixed,281,0,(-1),false,188,628⟩,
⟨.mixed,281,1,(-1),false,187,82⟩,
⟨.mixed,282,0,(-1),false,186,658⟩,
⟨.mixed,282,1,(-1),false,184,658⟩,
⟨.mixed,282,2,(-1),false,185,88⟩,
⟨.mixed,282,3,(-1),false,183,88⟩,
⟨.mixed,283,0,(-1),false,192,700⟩,
⟨.mixed,283,1,(-1),false,191,94⟩,
⟨.mixed,284,0,0,false,493,62⟩,
⟨.mixed,284,0,1,false,485,62⟩,
⟨.mixed,284,0,2,false,461,24⟩,
⟨.mixed,284,0,3,false,481,554⟩,
⟨.mixed,284,0,4,false,483,171⟩,
⟨.mixed,284,1,0,false,491,115⟩,
⟨.mixed,284,1,1,false,479,115⟩,
⟨.mixed,284,1,2,false,459,24⟩,
⟨.mixed,284,1,3,false,475,554⟩,
⟨.mixed,284,1,4,false,477,171⟩,
⟨.mixed,285,0,(-1),false,45,748⟩,
⟨.mixed,286,0,(-1),false,44,766⟩,
⟨.mixed,286,1,(-1),false,43,766⟩,
⟨.mixed,287,0,0,false,75,62⟩,
⟨.mixed,287,0,1,false,71,62⟩,
⟨.mixed,287,0,2,false,59,24⟩,
⟨.mixed,287,0,3,false,67,554⟩,
⟨.mixed,287,0,4,false,69,171⟩,
⟨.mixed,288,0,(-1),false,415,748⟩,
⟨.mixed,288,1,(-1),false,410,748⟩,
⟨.mixed,288,2,(-1),false,416,748⟩,
⟨.mixed,289,0,(-1),false,377,610⟩,
⟨.mixed,289,1,(-1),false,373,610⟩,
⟨.mixed,289,2,(-1),false,376,610⟩,
⟨.mixed,289,3,(-1),false,372,610⟩,
⟨.mixed,289,4,(-1),false,378,610⟩,
⟨.mixed,289,5,(-1),false,374,610⟩,
⟨.mixed,290,0,(-1),false,381,646⟩,
⟨.mixed,290,1,(-1),false,380,646⟩,
⟨.mixed,290,2,(-1),false,382,646⟩,
⟨.mixed,291,0,(-1),false,412,766⟩,
⟨.mixed,292,0,(-1),false,317,604⟩,
⟨.mixed,293,0,(-1),false,315,622⟩,
⟨.mixed,293,1,(-1),false,313,622⟩,
⟨.mixed,294,0,(-1),false,319,670⟩,
⟨.mixed,295,0,(-1),false,33,748⟩,
⟨.mixed,296,0,(-1),false,32,766⟩,
⟨.mixed,296,1,(-1),false,31,766⟩,
⟨.mixed,297,0,(-1),false,35,56⟩,
⟨.mixed,298,0,(-1),false,379,610⟩,
⟨.mixed,298,1,(-1),false,375,610⟩,
⟨.mixed,299,0,(-1),false,383,646⟩,
⟨.mixed,300,0,(-1),false,417,748⟩,
⟨.mixed,301,0,(-1),false,318,604⟩,
⟨.mixed,302,0,(-1),false,316,622⟩,
⟨.mixed,302,1,(-1),false,314,622⟩,
⟨.mixed,303,0,(-1),false,320,670⟩,
⟨.mixed,304,0,(-1),false,413,1044⟩,
⟨.mixed,305,0,(-1),false,167,628⟩,
⟨.mixed,306,0,(-1),false,166,658⟩,
⟨.mixed,306,1,(-1),false,165,658⟩,
⟨.mixed,307,0,(-1),false,169,700⟩,
⟨.mixed,308,0,(-1),false,414,56⟩,
⟨.mixed,309,0,(-1),false,9,205⟩,
⟨.mixed,310,0,(-1),false,8,211⟩,
⟨.mixed,310,1,(-1),false,7,211⟩,
⟨.mixed,311,0,(-1),false,11,221⟩,
⟨.mixed,312,0,(-1),false,517,298⟩
] := by rfl
end M7ContinueSep17.CatalogueGeneral

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def recs686 : List LowerHistoryRecord := [⟨.mixed,2,0,(-1),false,231,1084⟩,⟨.mixed,2,1,(-1),false,229,1084⟩]
theorem records686 : lowerHistoryRecordsFor (⟨.mixed,2,[1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true)],([1,2,3,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs686 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 2)) = recs686
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs687 : List LowerHistoryRecord := [⟨.mixed,3,0,(-1),false,235,1108⟩]
theorem records687 : lowerHistoryRecordsFor (⟨.mixed,3,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true)],([1,2,3,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs687 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 3)) = recs687
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs688 : List LowerHistoryRecord := [⟨.mixed,4,0,(-1),false,120,1078⟩]
theorem records688 : lowerHistoryRecordsFor (⟨.mixed,4,[1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true)],([1,2,2,3],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs688 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 4)) = recs688
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs689 : List LowerHistoryRecord := [⟨.mixed,5,0,(-1),false,132,1096⟩,⟨.mixed,5,1,(-1),false,129,1096⟩]
theorem records689 : lowerHistoryRecordsFor (⟨.mixed,5,[1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true)],([1,2,2,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs689 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 5)) = recs689
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs690 : List LowerHistoryRecord := [⟨.mixed,6,0,(-1),false,157,1120⟩]
theorem records690 : lowerHistoryRecordsFor (⟨.mixed,6,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true)],([1,2,2,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs690 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 6)) = recs690
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace M7SplitSep17

theorem premise_lookup_chunk3 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
    (hd : d.size = 200) (he : e.size = 200) (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[400+i]? = c[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e)
    (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d)
    (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c)
    (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b)
    (by simp only [Array.size_append, ha, hb]; omega)]
  simp only [Array.size_append, ha, hb]
  exact congrArg (fun j => c[j]?) (by omega)

theorem preSize1 : lowerHistoryPremises01.size = 200 := by rfl
theorem preSize2 : lowerHistoryPremises02.size = 200 := by rfl
theorem preSize3 : lowerHistoryPremises03.size = 200 := by rfl
theorem preSize4 : lowerHistoryPremises04.size = 200 := by rfl
theorem preSize5 : lowerHistoryPremises05.size = 200 := by rfl
theorem premise222 : lowerHistoryPremises[221]? = some ([3,7,21,177,260,371,392,399,425,440,627,650,718,751,814,843,856,984,1067,1107,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 221 = 200+21 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 21 (by decide)]
  rfl
theorem premise333 : lowerHistoryPremises[332]? = some ([3,19,21,44,127,156,170,260,371,372,378,422,425,440,518,527,547,599,618,665,735,751,807,820,843,856,942,1014,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 332 = 200+132 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 132 (by decide)]
  rfl
theorem premise334 : lowerHistoryPremises[333]? = some ([3,19,21,44,127,156,260,371,372,378,422,425,440,518,527,547,599,618,665,735,751,807,843,856,942,1007,1014,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 333 = 200+133 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 133 (by decide)]
  rfl
theorem premise335 : lowerHistoryPremises[334]? = some ([3,19,21,44,127,170,260,371,372,378,422,425,440,518,547,618,665,735,751,807,820,843,856,942,993,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 334 = 200+134 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 134 (by decide)]
  rfl
theorem premise336 : lowerHistoryPremises[335]? = some ([3,19,21,44,127,260,371,372,378,422,425,440,518,547,618,665,735,751,807,843,856,942,993,1007,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 335 = 200+135 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 135 (by decide)]
  rfl
theorem premise337 : lowerHistoryPremises[336]? = some ([3,19,21,44,133,168,189,260,371,374,422,425,440,552,582,636,662,665,685,735,751,807,843,856,965,1060,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 336 = 200+136 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 136 (by decide)]
  rfl
theorem premise338 : lowerHistoryPremises[337]? = some ([3,19,21,44,133,168,260,371,374,422,425,440,552,636,665,685,735,751,807,843,856,965,1035,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 337 = 200+137 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 137 (by decide)]
  rfl
theorem premise339 : lowerHistoryPremises[338]? = some ([3,19,21,44,135,260,371,375,380,422,425,440,509,521,583,665,735,751,807,843,856,929,971,1007,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 338 = 200+138 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 138 (by decide)]
  rfl
theorem premise421 : lowerHistoryPremises[420]? = some ([3,21,207,251,260,264,371,404,422,425,440,699,729,735,751,788,793,803,843,856,1065,1131,1143,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 420 = 400+20 by decide]
  rw [premise_lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 20 (by decide)]
  rfl
theorem premise422 : lowerHistoryPremises[421]? = some ([3,21,207,260,264,371,404,422,425,440,699,735,751,788,803,843,856,1065,1126,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 421 = 400+21 by decide]
  rw [premise_lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 21 (by decide)]
  rfl
end M7SplitSep17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
namespace M7ContinueSep17.Finish50.Six
theorem lookup_chunk1 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[0 + i]? = a[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b) (by simp only [Array.size_append, ha, hb]; omega)]
  rw [Array.getElem?_append_left (xs := a) (by simp only [Array.size_append, ha]; omega)]
  simp only [Nat.zero_add]
theorem lookup_chunk2 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[200 + i]? = b[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b) (by simp only [Array.size_append, ha, hb]; omega)]
  rw [Array.getElem?_append_right (xs := a) (by simp only [Array.size_append, ha]; omega)]
  simp only [Array.size_append, ha]
  exact congrArg (fun j => b[j]?) (by omega)
theorem lookup_chunk3 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[400 + i]? = c[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b) (by simp only [Array.size_append, ha, hb]; omega)]
  simp only [Array.size_append, ha, hb]
  exact congrArg (fun j => c[j]?) (by omega)
theorem lookup_chunk4 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[600 + i]? = d[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  simp only [Array.size_append, ha, hb, hc]
  exact congrArg (fun j => d[j]?) (by omega)
theorem lookup_chunk5 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[800 + i]? = e[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  simp only [Array.size_append, ha, hb, hc, hd]
  exact congrArg (fun j => e[j]?) (by omega)
theorem lookup_chunk6 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[1000 + i]? = f[i]? := by
  rw [Array.getElem?_append_right (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  simp only [Array.size_append, ha, hb, hc, hd, he]
  exact congrArg (fun j => f[j]?) (by omega)
end M7ContinueSep17.Finish50.Six

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
theorem premise120 : lowerHistoryPremises[119]? = some ([3,5,21,223,231,260,275,371,408,440,442,695,739,817,843,856,1125] : List Nat) := by
  have hg : lowerHistoryPremises[119]? = lowerHistoryPremises01[119]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 119 (by decide)
  exact hg.trans (by rfl)
theorem premise129 : lowerHistoryPremises[128]? = some ([3,5,21,228,243,250,260,275,371,411,440,442,734,775,817,843,856,868] : List Nat) := by
  have hg : lowerHistoryPremises[128]? = lowerHistoryPremises01[128]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 128 (by decide)
  exact hg.trans (by rfl)
theorem premise132 : lowerHistoryPremises[131]? = some ([3,5,21,228,243,260,275,371,411,440,442,734,775,817,843,856,1125] : List Nat) := by
  have hg : lowerHistoryPremises[131]? = lowerHistoryPremises01[131]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 131 (by decide)
  exact hg.trans (by rfl)
theorem premise157 : lowerHistoryPremises[156]? = some ([3,5,21,256,260,265,275,371,440,442,801,815,817,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[156]? = lowerHistoryPremises01[156]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 156 (by decide)
  exact hg.trans (by rfl)
theorem premise229 : lowerHistoryPremises[228]? = some ([3,7,21,211,230,239,260,275,371,406,440,442,697,740,814,843,850,856] : List Nat) := by
  have hg : lowerHistoryPremises[228]? = lowerHistoryPremises02[28]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 28 (by decide)
  exact hg.trans (by rfl)
theorem premise231 : lowerHistoryPremises[230]? = some ([3,7,21,211,230,260,275,371,406,440,442,697,740,814,843,856,1107] : List Nat) := by
  have hg : lowerHistoryPremises[230]? = lowerHistoryPremises02[30]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 30 (by decide)
  exact hg.trans (by rfl)
theorem premise235 : lowerHistoryPremises[234]? = some ([3,7,21,251,260,264,275,371,440,442,788,793,814,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[234]? = lowerHistoryPremises02[34]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 34 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Noninitial20260918.B685_690
theorem witness1078_projection : (lowerHistoryWitness 1078).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1078).upperBound = lowerHistoryBound 739 ∧ (lowerHistoryWitness 1078).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[77]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 739, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 739, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1077]? = lowerHistoryWitnesses06[77]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 77 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1084_projection : (lowerHistoryWitness 1084).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1084).upperBound = lowerHistoryBound 740 ∧ (lowerHistoryWitness 1084).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[83]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 740, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 740, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1083]? = lowerHistoryWitnesses06[83]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 83 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1096_projection : (lowerHistoryWitness 1096).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1096).upperBound = lowerHistoryBound 775 ∧ (lowerHistoryWitness 1096).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[95]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 775, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 775, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1095]? = lowerHistoryWitnesses06[95]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 95 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1108_projection : (lowerHistoryWitness 1108).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1108).upperBound = lowerHistoryBound 793 ∧ (lowerHistoryWitness 1108).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[107]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 793, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 793, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1107]? = lowerHistoryWitnesses06[107]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 107 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1120_projection : (lowerHistoryWitness 1120).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1120).upperBound = lowerHistoryBound 815 ∧ (lowerHistoryWitness 1120).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[119]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 815, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 815, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1119]? = lowerHistoryWitnesses06[119]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 119 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 1078 => (442,739)
  | 1084 => (442,740)
  | 1096 => (442,775)
  | 1108 => (442,793)
  | 1120 => (442,815)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 120 => [3,5,21,223,231,260,275,371,408,440,442,695,739,817,843,856,1125]
  | 129 => [3,5,21,228,243,250,260,275,371,411,440,442,734,775,817,843,856,868]
  | 132 => [3,5,21,228,243,260,275,371,411,440,442,734,775,817,843,856,1125]
  | 157 => [3,5,21,256,260,265,275,371,440,442,801,815,817,843,856]
  | 229 => [3,7,21,211,230,239,260,275,371,406,440,442,697,740,814,843,850,856]
  | 231 => [3,7,21,211,230,260,275,371,406,440,442,697,740,814,843,856,1107]
  | 235 => [3,7,21,251,260,264,275,371,440,442,788,793,814,843,856]
  | _ => []
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def src686 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,1107,406,697,230,740,211],[371,843,260,440,3,856,21,275,442,814,7,239,850,406,697,230,740,211]]
theorem sourceIDs686 : lowerHistorySourcePremises path686 = src686.map (List.map lowerHistoryBound) := by
  have hb : src686.map (List.map lowerHistoryBound) = expected686 := by
    simp only [src686, expected686, List.map_cons, List.map_nil, bound3, bound7, bound21, bound211, bound230, bound239, bound260, bound275, bound371, bound406, bound440, bound442, bound697, bound740, bound814, bound843, bound850, bound856, bound1107]
  exact source686.trans hb.symm
theorem length686 : path686.alternatives = (lowerHistorySourcePremises path686).length := by
  rw [sourceIDs686]
  rfl
theorem binding686 : lowerHistoryPathBinding path686 := by
  apply BindingIds19.pathBinding_from_ids path686 src686 [] recs686 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs686 rfl records686 rfl
  · intro r hr _
    simp only [recs686, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise231)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise229)
  · intro r hr _
    simp only [recs686, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path686] using witness1084_projection
    · simpa only [blockWids, path686] using witness1084_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path686 recs686 records686 length686 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def path687 : LowerHistoryPath := ⟨.mixed,3,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true)],([1,2,3,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
noncomputable def raw687 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv264,bv788,bv251,bv793,bv264]]
noncomputable def expected687 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv264,bv788,bv251,bv793]]
theorem structural687 (ops : RootOps19.SourceOps) (b3 b7 b21 b251 b260 b264 b275 b371 b440 b442 b788 b793 b814 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h148 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h149 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h44 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h45 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h46 : ops.normalization ([2,3],[3,1]) false false = b814)
    (h150 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (h163 : ops.normalization ([2,3,1],[3,1]) true false = b264)
    (h164 : ops.necessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [b788])
    (h165 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) true = b251)
    (h166 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) true = b793)
    (h167 : ops.pull (lowerHistoryHN) ([2,3,1],[3,1]) true = b264)
    : RootOps19.eval ops path687 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b251,b793,b264]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path687, h0, h148, h2, h149, h44, h45, h46, h150, h163, h164, h165, h166, h167, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource687 : lowerHistorySourcePremises path687 = raw687.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural687 RootOps19.actualOps bv3 bv7 bv21 bv251 bv260 bv264 bv275 bv371 bv440 bv442 bv788 bv793 bv814 bv843 bv856 op0 op148 op2 op149 op44 op45 op46 op150 op163 op164 op165 op166 op167
theorem dedup687 : raw687.map List.eraseDups = expected687 := by
  decide +kernel
theorem source687 : lowerHistorySourcePremises path687 = expected687 := (rawSource687).trans (dedup687)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def src687 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,264,788,251,793]]
theorem sourceIDs687 : lowerHistorySourcePremises path687 = src687.map (List.map lowerHistoryBound) := by
  have hb : src687.map (List.map lowerHistoryBound) = expected687 := by
    simp only [src687, expected687, List.map_cons, List.map_nil, bound3, bound7, bound21, bound251, bound260, bound264, bound275, bound371, bound440, bound442, bound788, bound793, bound814, bound843, bound856]
  exact source687.trans hb.symm
theorem length687 : path687.alternatives = (lowerHistorySourcePremises path687).length := by
  rw [sourceIDs687]
  rfl
theorem binding687 : lowerHistoryPathBinding path687 := by
  apply BindingIds19.pathBinding_from_ids path687 src687 [] recs687 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs687 rfl records687 rfl
  · intro r hr _
    simp only [recs687, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise235)
  · intro r hr _
    simp only [recs687, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path687] using witness1108_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path687 recs687 records687 length687 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
open BindingNumeric20
theorem op170 : lowerHistoryNormalization ([2,2,3],[3,1]) true true = bv408 := by
  norm_num [bv408, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op171 : lowerHistoryNecessary ⟨⟨([1,2,2,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,2,3],[3,1]) = some [bv695] := by
  decide +kernel
theorem op172 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,3],[3,1]) true = bv231 := by
  norm_num [bv231, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op173 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,3],[3,1]) true = bv739 := by
  norm_num [bv739, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op174 : lowerHistoryPull (lowerHistoryHN) ([2,2,3],[3,1]) true = bv223 := by
  norm_num [bv223, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op52 : lowerHistoryPull (lowerHistoryH7) ([2,2],[3,1]) false = bv250 := by
  norm_num [bv250, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op175 : lowerHistoryPull (lowerHistoryH9) ([2,2],[3,1]) false = bv868 := by
  norm_num [bv868, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op176 : lowerHistoryNormalization ([2,2,2],[3,1]) true true = bv411 := by
  norm_num [bv411, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op177 : lowerHistoryNecessary ⟨⟨([1,2,2,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,2],[3,1]) = some [bv734] := by
  decide +kernel
theorem op178 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,2],[3,1]) true = bv243 := by
  norm_num [bv243, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op179 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,2],[3,1]) true = bv775 := by
  norm_num [bv775, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op180 : lowerHistoryPull (lowerHistoryHN) ([2,2,2],[3,1]) true = bv228 := by
  norm_num [bv228, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def path688 : LowerHistoryPath := ⟨.mixed,4,[1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true)],([1,2,2,3],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
noncomputable def raw688 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv1125,bv408,bv695,bv231,bv739,bv223]]
noncomputable def expected688 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv1125,bv408,bv695,bv231,bv739,bv223]]
theorem structural688 (ops : RootOps19.SourceOps) (b3 b5 b21 b223 b231 b260 b275 b371 b408 b440 b442 b695 b739 b817 b843 b856 b1125 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h148 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h149 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h44 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h45 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h50 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h168 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (h169 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,2],[3,1]) false = b1125)
    (h170 : ops.normalization ([2,2,3],[3,1]) true true = b408)
    (h171 : ops.necessary ⟨⟨([1,2,2,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,2,3],[3,1]) = some [b695])
    (h172 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,3],[3,1]) true = b231)
    (h173 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,3],[3,1]) true = b739)
    (h174 : ops.pull (lowerHistoryHN) ([2,2,3],[3,1]) true = b223)
    : RootOps19.eval ops path688 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b408,b695,b231,b739,b223]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path688, h0, h148, h2, h149, h44, h45, h50, h168, h169, h170, h171, h172, h173, h174, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource688 : lowerHistorySourcePremises path688 = raw688.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural688 RootOps19.actualOps bv3 bv5 bv21 bv223 bv231 bv260 bv275 bv371 bv408 bv440 bv442 bv695 bv739 bv817 bv843 bv856 bv1125 op0 op148 op2 op149 op44 op45 op50 op168 op169 op170 op171 op172 op173 op174
theorem dedup688 : raw688.map List.eraseDups = expected688 := by
  decide +kernel
theorem source688 : lowerHistorySourcePremises path688 = expected688 := (rawSource688).trans (dedup688)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def src688 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,1125,408,695,231,739,223]]
theorem sourceIDs688 : lowerHistorySourcePremises path688 = src688.map (List.map lowerHistoryBound) := by
  have hb : src688.map (List.map lowerHistoryBound) = expected688 := by
    simp only [src688, expected688, List.map_cons, List.map_nil, bound3, bound5, bound21, bound223, bound231, bound260, bound275, bound371, bound408, bound440, bound442, bound695, bound739, bound817, bound843, bound856, bound1125]
  exact source688.trans hb.symm
theorem length688 : path688.alternatives = (lowerHistorySourcePremises path688).length := by
  rw [sourceIDs688]
  rfl
theorem binding688 : lowerHistoryPathBinding path688 := by
  apply BindingIds19.pathBinding_from_ids path688 src688 [] recs688 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs688 rfl records688 rfl
  · intro r hr _
    simp only [recs688, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise120)
  · intro r hr _
    simp only [recs688, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path688] using witness1078_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path688 recs688 records688 length688 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def path689 : LowerHistoryPath := ⟨.mixed,5,[1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true)],([1,2,2,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
noncomputable def raw689 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv1125,bv411,bv734,bv243,bv775,bv228],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv250,bv868,bv411,bv734,bv243,bv775,bv228]]
noncomputable def expected689 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv1125,bv411,bv734,bv243,bv775,bv228],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv250,bv868,bv411,bv734,bv243,bv775,bv228]]
theorem structural689 (ops : RootOps19.SourceOps) (b3 b5 b21 b228 b243 b250 b260 b275 b371 b411 b440 b442 b734 b775 b817 b843 b856 b868 b1125 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h148 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h149 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h44 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h45 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h50 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h168 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (h169 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,2],[3,1]) false = b1125)
    (h52 : ops.pull (lowerHistoryH7) ([2,2],[3,1]) false = b250)
    (h175 : ops.pull (lowerHistoryH9) ([2,2],[3,1]) false = b868)
    (h176 : ops.normalization ([2,2,2],[3,1]) true true = b411)
    (h177 : ops.necessary ⟨⟨([1,2,2,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,2],[3,1]) = some [b734])
    (h178 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,2],[3,1]) true = b243)
    (h179 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,2],[3,1]) true = b775)
    (h180 : ops.pull (lowerHistoryHN) ([2,2,2],[3,1]) true = b228)
    : RootOps19.eval ops path689 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b228],[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b228]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path689, h0, h148, h2, h149, h44, h45, h50, h168, h169, h52, h175, h176, h177, h178, h179, h180, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource689 : lowerHistorySourcePremises path689 = raw689.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural689 RootOps19.actualOps bv3 bv5 bv21 bv228 bv243 bv250 bv260 bv275 bv371 bv411 bv440 bv442 bv734 bv775 bv817 bv843 bv856 bv868 bv1125 op0 op148 op2 op149 op44 op45 op50 op168 op169 op52 op175 op176 op177 op178 op179 op180
theorem dedup689 : raw689.map List.eraseDups = expected689 := by
  decide +kernel
theorem source689 : lowerHistorySourcePremises path689 = expected689 := (rawSource689).trans (dedup689)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def src689 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,1125,411,734,243,775,228],[371,843,260,440,3,856,21,275,442,817,5,250,868,411,734,243,775,228]]
theorem sourceIDs689 : lowerHistorySourcePremises path689 = src689.map (List.map lowerHistoryBound) := by
  have hb : src689.map (List.map lowerHistoryBound) = expected689 := by
    simp only [src689, expected689, List.map_cons, List.map_nil, bound3, bound5, bound21, bound228, bound243, bound250, bound260, bound275, bound371, bound411, bound440, bound442, bound734, bound775, bound817, bound843, bound856, bound868, bound1125]
  exact source689.trans hb.symm
theorem length689 : path689.alternatives = (lowerHistorySourcePremises path689).length := by
  rw [sourceIDs689]
  rfl
theorem binding689 : lowerHistoryPathBinding path689 := by
  apply BindingIds19.pathBinding_from_ids path689 src689 [] recs689 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs689 rfl records689 rfl
  · intro r hr _
    simp only [recs689, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise132)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise129)
  · intro r hr _
    simp only [recs689, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path689] using witness1096_projection
    · simpa only [blockWids, path689] using witness1096_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path689 recs689 records689 length689 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
open BindingNumeric20
theorem op181 : lowerHistoryNormalization ([2,2,1],[3,1]) true false = bv256 := by
  norm_num [bv256, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op182 : lowerHistoryNecessary ⟨⟨([1,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [bv801] := by
  decide +kernel
theorem op183 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) true = bv265 := by
  norm_num [bv265, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op184 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) true = bv815 := by
  norm_num [bv815, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op185 : lowerHistoryPull (lowerHistoryHN) ([2,2,1],[3,1]) true = bv256 := by
  norm_num [bv256, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def path690 : LowerHistoryPath := ⟨.mixed,6,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true)],([1,2,2,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
noncomputable def raw690 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv256,bv801,bv265,bv815,bv256]]
noncomputable def expected690 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv256,bv801,bv265,bv815]]
theorem structural690 (ops : RootOps19.SourceOps) (b3 b5 b21 b256 b260 b265 b275 b371 b440 b442 b801 b815 b817 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h148 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h149 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h44 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h45 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h50 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h168 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (h181 : ops.normalization ([2,2,1],[3,1]) true false = b256)
    (h182 : ops.necessary ⟨⟨([1,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [b801])
    (h183 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) true = b265)
    (h184 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) true = b815)
    (h185 : ops.pull (lowerHistoryHN) ([2,2,1],[3,1]) true = b256)
    : RootOps19.eval ops path690 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b265,b815,b256]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path690, h0, h148, h2, h149, h44, h45, h50, h168, h181, h182, h183, h184, h185, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource690 : lowerHistorySourcePremises path690 = raw690.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural690 RootOps19.actualOps bv3 bv5 bv21 bv256 bv260 bv265 bv275 bv371 bv440 bv442 bv801 bv815 bv817 bv843 bv856 op0 op148 op2 op149 op44 op45 op50 op168 op181 op182 op183 op184 op185
theorem dedup690 : raw690.map List.eraseDups = expected690 := by
  decide +kernel
theorem source690 : lowerHistorySourcePremises path690 = expected690 := (rawSource690).trans (dedup690)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
noncomputable def src690 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,256,801,265,815]]
theorem sourceIDs690 : lowerHistorySourcePremises path690 = src690.map (List.map lowerHistoryBound) := by
  have hb : src690.map (List.map lowerHistoryBound) = expected690 := by
    simp only [src690, expected690, List.map_cons, List.map_nil, bound3, bound5, bound21, bound256, bound260, bound265, bound275, bound371, bound440, bound442, bound801, bound815, bound817, bound843, bound856]
  exact source690.trans hb.symm
theorem length690 : path690.alternatives = (lowerHistorySourcePremises path690).length := by
  rw [sourceIDs690]
  rfl
theorem binding690 : lowerHistoryPathBinding path690 := by
  apply BindingIds19.pathBinding_from_ids path690 src690 [] recs690 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs690 rfl records690 rfl
  · intro r hr _
    simp only [recs690, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise157)
  · intro r hr _
    simp only [recs690, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path690] using witness1120_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path690 recs690 records690 length690 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B685_690

set_option Elab.async false
set_option maxRecDepth 30000
open Freiman
namespace M7ContinueSep17.CatalogueGeneral
theorem pathSizeL : lowerHistoryPathsL.size = 594 := by rfl
theorem pathSizeR : lowerHistoryPathsR.size = 90 := by rfl
theorem pathSizeM : lowerHistoryPathsM.size = 312 := by rfl
theorem pathSizeX : lowerHistoryPathsX.size = 90 := by rfl
theorem pathSizeH : lowerHistoryPathsH.size = 406 := by rfl
theorem pathLookupL (i : Nat) (hi : i < 594) : lowerHistoryPaths[0+i]? = lowerHistoryPathsL[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Nat.zero_add]
theorem pathLookupR (i : Nat) (hi : i < 90) : lowerHistoryPaths[594+i]? = lowerHistoryPathsR[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsR[j]?) (by omega)
theorem pathLookupM (i : Nat) (hi : i < 312) : lowerHistoryPaths[684+i]? = lowerHistoryPathsM[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL ++ lowerHistoryPathsR) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsM[j]?) (by omega)
theorem pathLookupX (i : Nat) (hi : i < 90) : lowerHistoryPaths[996+i]? = lowerHistoryPathsX[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsX[j]?) (by omega)
theorem pathLookupH (i : Nat) (hi : i < 406) : lowerHistoryPaths[1086+i]? = lowerHistoryPathsH[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsH[j]?) (by omega)
end M7ContinueSep17.CatalogueGeneral

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B685_690
theorem _root_.solution : lowerHistoryBindingBatch 685 690 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[685]? = some M7ContinueSep17.Noninitial20260918.B685_690.path686 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 1 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding686
  · have hl : lowerHistoryPaths[686]? = some M7ContinueSep17.Noninitial20260918.B685_690.path687 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 2 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding687
  · have hl : lowerHistoryPaths[687]? = some M7ContinueSep17.Noninitial20260918.B685_690.path688 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 3 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding688
  · have hl : lowerHistoryPaths[688]? = some M7ContinueSep17.Noninitial20260918.B685_690.path689 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 4 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding689
  · have hl : lowerHistoryPaths[689]? = some M7ContinueSep17.Noninitial20260918.B685_690.path690 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 5 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding690
end M7ContinueSep17.Noninitial20260918.B685_690

#print axioms solution
