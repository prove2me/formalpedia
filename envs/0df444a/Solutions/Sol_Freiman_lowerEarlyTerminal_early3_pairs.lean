-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_early3_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T18:35:33.369317+00:00
-- url     : https://prove2.me/submissions/17bcae35-aac6-4da4-8212-b874dae58353

import Definitions.Def_Freiman_lowerEarlyTerminalDataEarly3
import Mathlib.Tactic

set_option Elab.async false
set_option linter.all false

open Freiman
namespace Blockers16Early3Data
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def coeffBool (z : CertField) (q : ℚ) : Bool :=
  decide (q < certFieldLower z)

private def coeffsBool (P : CertPoly22) (q : ℚ) : Bool :=
  coeffBool (P 0 0) q && coeffBool (P 0 1) q && coeffBool (P 0 2) q &&
  coeffBool (P 1 0) q && coeffBool (P 1 1) q && coeffBool (P 1 2) q &&
  coeffBool (P 2 0) q && coeffBool (P 2 1) q && coeffBool (P 2 2) q

private theorem coeffBool_sound (z : CertField) (q : ℚ) (hq : 0 < q)
    (h : coeffBool z q = true) : certCoefficientBoundValid z q := by
  simp only [coeffBool, decide_eq_true_eq] at h
  unfold certCoefficientBoundValid
  refine ⟨le_of_lt hq, ?_⟩
  simp [ne_of_gt hq, h]

private theorem coeffsBool_sound (P : CertPoly22) (q : ℚ) (hq : 0 < q)
    (h : coeffsBool P q = true) :
    ∀ i j : Fin 3, certCoefficientBoundValid (P i j) q := by
  simp only [coeffsBool, Bool.and_eq_true] at h
  intro i j
  fin_cases i <;> fin_cases j
  all_goals apply coeffBool_sound _ _ hq <;> simp_all

private def earlyRect : CertRectangle := ⟨(1/4),(1/3),(3/4),(4/5)⟩
private theorem bounds_length : lowerEarlyTerminalEarly3.bounds.length = 1238 := by decide +kernel

private def eb2 : CertBound := ⟨true,false,⟨⟨(1703/253),(-884/253),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/11),(-1/11),0,0⟩,⟨(3/13),(1/39),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb3 : CertBound := ⟨false,false,⟨⟨(183/250),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb6 : CertBound := ⟨false,true,⟨⟨(107615/518014),0,0,(130195/10878294)⟩,⟨(135/326),0,0,(1/6846)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb7 : CertBound := ⟨false,false,⟨⟨(-449175/2379971),(969439/2379971),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
private def eb8 : CertBound := ⟨false,false,⟨⟨(6611/16798),0,0,(-91/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb12 : CertBound := ⟨false,false,⟨⟨(-4068621/11250772),(6005837/11250772),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
private def eb13 : CertBound := ⟨true,true,⟨⟨(1770461/1683350),0,0,(171157/5050050)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
private def eb14 : CertBound := ⟨true,true,⟨⟨(6343/4454),0,0,(-511/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb15 : CertBound := ⟨false,false,⟨⟨(-89774/6105143),(2123203/6105143),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
private def eb23 : CertBound := ⟨false,false,⟨⟨(150661/370010),0,0,(26039/1110030)⟩,⟨(135/326),0,0,(1/6846)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb27 : CertBound := ⟨true,true,⟨⟨(1651/697),0,0,(-18/697)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb28 : CertBound := ⟨true,false,⟨⟨(110477/63986),(894529/191958),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
private def eb33 : CertBound := ⟨true,false,⟨⟨(3146175/336938),0,0,(-9775/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
private def eb35 : CertBound := ⟨true,true,⟨⟨(880929/48134),0,0,(-2737/48134)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
private def eb36 : CertBound := ⟨true,true,⟨⟨(17481/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩
private def eb39 : CertBound := ⟨true,false,⟨⟨(-69748/386377),(1965815/386377),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
private def eb43 : CertBound := ⟨true,true,⟨⟨(7723/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
private def eb45 : CertBound := ⟨true,false,⟨⟨(83966/39169),(461834/117507),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
private def eb50 : CertBound := ⟨false,true,⟨⟨(146275/471338),0,0,(-8775/471338)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb51 : CertBound := ⟨false,false,⟨⟨(-310869/2379971),(812695/2379971),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb52 : CertBound := ⟨false,false,⟨⟨(6757/22270),0,0,(-13/22270)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb53 : CertBound := ⟨false,false,⟨⟨(5869/16798),0,0,(-21/16798)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb60 : CertBound := ⟨false,false,⟨⟨(40957/67334),0,0,(-2457/67334)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb61 : CertBound := ⟨true,true,⟨⟨(2811/2227),0,0,(-224/2227)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb66 : CertBound := ⟨false,false,⟨⟨(-1372541/5625386),(2429307/5625386),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb69 : CertBound := ⟨true,true,⟨⟨(128177/185005),0,0,(51442/555015)⟩,⟨(135/326),0,0,(1/6846)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb70 : CertBound := ⟨true,true,⟨⟨(5665/8399),0,0,(1054/25197)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb71 : CertBound := ⟨false,false,⟨⟨(366559/7058447),(1948134/7058447),0,0⟩,⟨(1005/2426),(1/7278),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb75 : CertBound := ⟨true,true,⟨⟨(2931/1394),0,0,(-29/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb76 : CertBound := ⟨true,false,⟨⟨(48592/31993),(400249/95979),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
private def eb84 : CertBound := ⟨true,false,⟨⟨(165265/24067),0,0,(81040/168469)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
private def eb86 : CertBound := ⟨true,true,⟨⟨(1619597/120335),0,0,(113456/120335)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
private def eb87 : CertBound := ⟨true,true,⟨⟨(9665/697),0,0,(-64/697)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩
private def eb90 : CertBound := ⟨true,false,⟨⟨(-818671/772754),(11588245/2318262),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
private def eb96 : CertBound := ⟨true,false,⟨⟨(74292/39169),(413128/117507),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
private def eb100 : CertBound := ⟨true,true,⟨⟨(16627/1394),0,0,(-77/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
private def eb101 : CertBound := ⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private def eb102 : CertBound := ⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private def eb103 : CertBound := ⟨false,true,⟨⟨(-31948/28083),(28553/28083),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb105 : CertBound := ⟨true,false,⟨⟨(911075/336938),0,0,(87035/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
private def eb106 : CertBound := ⟨false,true,⟨⟨(-59864/48829),(626311/585948),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb107 : CertBound := ⟨true,true,⟨⟨(255101/48134),0,0,(121849/240670)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
private def eb109 : CertBound := ⟨false,true,⟨⟨(-468465/508343),(1375466/1525029),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb114 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private def eb116 : CertBound := ⟨false,true,⟨⟨(-166418/365079),(237950/365079),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb118 : CertBound := ⟨false,true,⟨⟨(-639385/1269554),(2592133/3808662),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb119 : CertBound := ⟨false,true,⟨⟨(-4753457/19825377),(10645601/19825377),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb120 : CertBound := ⟨true,true,⟨⟨(7126725/5220637),(1955485/5220637),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
private def eb121 : CertBound := ⟨false,true,⟨⟨(441215/341054),0,0,(-6665/48722)⟩,⟨(1209/2866),0,0,(1/2866)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb122 : CertBound := ⟨true,true,⟨⟨(51959375/37567058),(12944345/37567058),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
private def eb125 : CertBound := ⟨true,true,⟨⟨(409653009/294014566),(102638027/294014566),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
private def eb127 : CertBound := ⟨true,true,⟨⟨(8171/31993),(22664/31993),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb129 : CertBound := ⟨true,false,⟨⟨(460875/336938),0,0,(3875/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb131 : CertBound := ⟨true,true,⟨⟨(129045/48134),0,0,(1085/48134)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb134 : CertBound := ⟨true,true,⟨⟨(-23048/386377),(911665/1159131),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb137 : CertBound := ⟨true,true,⟨⟨(12536/39169),(23388/39169),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb140 : CertBound := ⟨true,true,⟨⟨(13461/33598),(13073/33598),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
private def eb141 : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
private def eb144 : CertBound := ⟨true,true,⟨⟨(360273/1694452),(736243/1694452),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
private def eb146 : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
private def eb147 : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private def eb150 : CertBound := ⟨true,false,⟨⟨(539885/341054),0,0,(-10055/341054)⟩,⟨(1209/2866),0,0,(1/2866)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb154 : CertBound := ⟨true,true,⟨⟨(755839/243610),0,0,(-14077/243610)⟩,⟨(1209/2866),0,0,(1/2866)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb159 : CertBound := ⟨true,false,⟨⟨(153/250),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(35/94),(1/94),0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(5/22),(1/22),0,0⟩⟩⟩
private def eb160 : CertBound := ⟨false,false,⟨⟨(1703/253),(-884/253),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/11),(-1/11),0,0⟩,⟨(3/13),(1/39),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb162 : CertBound := ⟨false,true,⟨⟨(193703/848225),0,0,(-4748/848225)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb163 : CertBound := ⟨false,false,⟨⟨(-24300/147323),(51497/147323),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
private def eb164 : CertBound := ⟨false,false,⟨⟨(13109/43885),0,0,(-176/43885)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb165 : CertBound := ⟨false,false,⟨⟨(3049/8282),0,0,(-391/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb171 : CertBound := ⟨false,false,⟨⟨(-601572/1915199),(3511661/7660796),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
private def eb172 : CertBound := ⟨true,true,⟨⟨(628621/804215),0,0,(62208/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
private def eb173 : CertBound := ⟨true,true,⟨⟨(3553/4141),0,0,(108/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
private def eb174 : CertBound := ⟨false,false,⟨⟨(187203/5421097),(1481141/5421097),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
private def eb183 : CertBound := ⟨false,false,⟨⟨(1355921/3029375),0,0,(-33236/3029375)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb186 : CertBound := ⟨true,true,⟨⟨(9833/12314),0,0,(-171/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb187 : CertBound := ⟨true,true,⟨⟨(187/94),0,0,(-31/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb188 : CertBound := ⟨true,false,⟨⟨(184867/101426),(1145809/304278),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
private def eb193 : CertBound := ⟨true,false,⟨⟨(-297343/612457),(2732382/612457),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(1493/5354),(-1/16062),0,0⟩⟩⟩
private def eb197 : CertBound := ⟨true,false,⟨⟨(2514041/1135849),(3575763/1135849),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
private def eb199 : CertBound := ⟨true,true,⟨⟨(991/94),0,0,(57/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩
private def eb203 : CertBound := ⟨true,false,⟨⟨(85625/9478),0,0,(565/9478)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
private def eb207 : CertBound := ⟨true,true,⟨⟨(23975/1354),0,0,(791/6770)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
private def eb208 : CertBound := ⟨true,true,⟨⟨(1207/94),0,0,(33/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(115/422),0,0,(1/1266)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
private def eb214 : CertBound := ⟨false,true,⟨⟨(225375/1125901),0,0,(20000/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb215 : CertBound := ⟨false,false,⟨⟨(-16887/147323),(43160/147323),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb216 : CertBound := ⟨false,false,⟨⟨(33/101),0,0,(-4/707)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb217 : CertBound := ⟨false,false,⟨⟨(8727/12314),0,0,(-143/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb223 : CertBound := ⟨false,false,⟨⟨(63105/160843),0,0,(800/160843)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb226 : CertBound := ⟨false,false,⟨⟨(-73993/348218),(64543/174109),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb229 : CertBound := ⟨true,true,⟨⟨(3962749/6058750),0,0,(275891/6058750)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb230 : CertBound := ⟨true,true,⟨⟨(8727/12314),0,0,(-143/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb231 : CertBound := ⟨false,false,⟨⟨(5976/2214839),(566539/2214839),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb235 : CertBound := ⟨true,true,⟨⟨(83/47),0,0,(-4/329)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb236 : CertBound := ⟨true,false,⟨⟨(81657/50713),(512554/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
private def eb241 : CertBound := ⟨true,false,⟨⟨(138122/612457),(6708677/1837371),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩⟩⟩
private def eb243 : CertBound := ⟨true,true,⟨⟨(319/94),0,0,(395/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb245 : CertBound := ⟨true,false,⟨⟨(202772/103259),(290686/103259),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
private def eb247 : CertBound := ⟨true,false,⟨⟨(53505/4739),0,0,(-81920/99519)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
private def eb251 : CertBound := ⟨true,true,⟨⟨(74907/3385),0,0,(-16384/10155)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
private def eb252 : CertBound := ⟨true,true,⟨⟨(471/47),0,0,(-16/987)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
private def eb257 : CertBound := ⟨false,false,⟨⟨(3165/8282),0,0,(2123/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
private def eb258 : CertBound := ⟨false,true,⟨⟨(328519/3030122),0,0,(-203377/21210854)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(19899/51358),0,0,(-1/51358)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb259 : CertBound := ⟨false,false,⟨⟨(-3830337/83577988),(13349929/125366982),0,0⟩,⟨(353/914),(1/2742),0,0⟩,⟨(1364/3517),(-1/3517),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb260 : CertBound := ⟨false,false,⟨⟨(10967/198830),0,0,(1189/198830)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(1311/3370),0,0,(-1/3370)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
private def eb261 : CertBound := ⟨false,false,⟨⟨(4089/64930),0,0,(3071/454510)⟩,⟨(579/1510),0,0,(1/1510)⟩,⟨(167/430),0,0,(-1/3010)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
private def eb268 : CertBound := ⟨false,false,⟨⟨(16097431/75753050),0,0,(-1423639/75753050)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(19899/51358),0,0,(-1/51358)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb272 : CertBound := ⟨true,false,⟨⟨(1693486/4216979),(4861851/4216979),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
private def eb280 : CertBound := ⟨true,false,⟨⟨(2137385/1125901),0,0,(945270/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
private def eb282 : CertBound := ⟨true,true,⟨⟨(2992339/804215),0,0,(189054/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
private def eb283 : CertBound := ⟨true,true,⟨⟨(16489/4141),0,0,(-324/4141)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩⟩⟩
private def eb286 : CertBound := ⟨true,false,⟨⟨(-14351173/50928131),(69686630/50928131),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(8222/27073),(1/27073),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
private def eb292 : CertBound := ⟨true,false,⟨⟨(4979012/9847487),(28731998/29542461),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
private def eb296 : CertBound := ⟨true,true,⟨⟨(29597/8282),0,0,(-3915/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
private def eb297 : CertBound := ⟨false,false,⟨⟨(365/677),0,0,(-232/4739)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
private def eb298 : CertBound := ⟨false,true,⟨⟨(1755447/29864266),0,0,(-983651/209049862)⟩,⟨(1311/3370),0,0,(1/3370)⟩,⟨(34601/88618),0,0,(-1/88618)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb299 : CertBound := ⟨false,false,⟨⟨(-6654327/256990708),(11698067/192743031),0,0⟩,⟨(1932/4957),(1/4957),0,0⟩,⟨(779/1994),(-1/5982),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb300 : CertBound := ⟨false,false,⟨⟨(58431/1843390),0,0,(6527/1843390)⟩,⟨(1311/3370),0,0,(1/3370)⟩,⟨(2141/5470),0,0,(-1/5470)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
private def eb301 : CertBound := ⟨false,false,⟨⟨(2513/71810),0,0,(1957/502670)⟩,⟨(167/430),0,0,(1/3010)⟩,⟨(653/1670),0,0,(-1/5010)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
private def eb308 : CertBound := ⟨false,false,⟨⟨(86016903/746606650),0,0,(-6885557/746606650)⟩,⟨(1311/3370),0,0,(1/3370)⟩,⟨(34601/88618),0,0,(-1/88618)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb312 : CertBound := ⟨true,false,⟨⟨(73300124/312797329),(183314232/312797329),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
private def eb318 : CertBound := ⟨true,false,⟨⟨(21209855/21903658),0,0,(781745/9387282)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
private def eb320 : CertBound := ⟨true,true,⟨⟨(29693797/15645470),0,0,(7661101/46936410)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
private def eb321 : CertBound := ⟨true,true,⟨⟨(11871/1354),0,0,(-5933/4062)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩⟩⟩
private def eb324 : CertBound := ⟨true,true,⟨⟨(10629/1354),0,0,(-37115/28434)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
private def eb325 : CertBound := ⟨false,true,⟨⟨(-92974/101343),(26405/33781),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb327 : CertBound := ⟨true,false,⟨⟨(1520885/1160054),0,0,(11855/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
private def eb328 : CertBound := ⟨false,true,⟨⟨(-347745/352418),(1739113/2114508),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb329 : CertBound := ⟨true,true,⟨⟨(2129239/828610),0,0,(16597/828610)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
private def eb331 : CertBound := ⟨false,true,⟨⟨(-413/481),(11923/15873),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb332 : CertBound := ⟨false,true,⟨⟨(1064163/878306),(-1103911/2634918),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
private def eb333 : CertBound := ⟨false,true,⟨⟨(31753823/27215617),(-32011552/81646851),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
private def eb334 : CertBound := ⟨false,true,⟨⟨(1043795/894179),(-348332/894179),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
private def eb335 : CertBound := ⟨false,true,⟨⟨(-310436/1317459),(182992/439153),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb336 : CertBound := ⟨false,true,⟨⟨(-605613/2290717),(2983688/6872151),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb337 : CertBound := ⟨false,true,⟨⟨(-2807/15873),(6130/15873),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private def eb338 : CertBound := ⟨true,true,⟨⟨(2316036/2293177),(762601/2293177),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
private def eb340 : CertBound := ⟨true,true,⟨⟨(16794977/16501418),(2579131/8250709),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
private def eb341 : CertBound := ⟨true,false,⟨⟨(14075/9478),0,0,(-4535/199038)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb342 : CertBound := ⟨true,true,⟨⟨(3941/1354),0,0,(-907/20310)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
private def eb345 : CertBound := ⟨true,true,⟨⟨(13766/50713),(29019/50713),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb346 : CertBound := ⟨false,true,⟨⟨(922125/1160054),0,0,(-75625/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
private def eb347 : CertBound := ⟨true,true,⟨⟨(-64511/1224914),(814289/1224914),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
private def eb350 : CertBound := ⟨true,true,⟨⟨(376986/1135849),(542948/1135849),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
private def eb358 : CertBound := ⟨true,true,⟨⟨(-29697/138697),(96839/138697),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb359 : CertBound := ⟨false,true,⟨⟨(1007355/2251802),0,0,(-21065/2251802)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb360 : CertBound := ⟨true,true,⟨⟨(-1608438/1675033),(1758380/1675033),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
private def eb363 : CertBound := ⟨true,true,⟨⟨(-1405947/10207366),(6145065/10207366),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb366 : CertBound := ⟨true,false,⟨⟨(20945/9478),0,0,(34225/199038)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb370 : CertBound := ⟨true,true,⟨⟨(29323/6770),0,0,(1369/4062)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
private def eb375 : CertBound := ⟨false,true,⟨⟨(341305/1564547),0,0,(11720/10951829)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb376 : CertBound := ⟨false,true,⟨⟨(-8563189/52684372),(17479377/52684372),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb380 : CertBound := ⟨false,false,⟨⟨(3344789/7822735),0,0,(16408/7822735)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
private def eb382 : CertBound := ⟨false,true,⟨⟨(5265060656/3004340799),(-1995772076/3004340799),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
private def eb383 : CertBound := ⟨false,true,⟨⟨(80427682014/55216958291),(-80769866134/165650874873),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
private def eb384 : CertBound := ⟨false,true,⟨⟨(46954158025/54382922579),(-16043976857/163148767737),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
private def eb385 : CertBound := ⟨true,true,⟨⟨(972627/1062082),(59571/151726),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb386 : CertBound := ⟨true,true,⟨⟨(54884910/59249003),(21043743/59249003),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
private def eb387 : CertBound := ⟨true,true,⟨⟨(1758829/1852277),(679351/1852277),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb388 : CertBound := ⟨true,true,⟨⟨(13125251/14262244),(4796555/14262244),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb389 : CertBound := ⟨true,true,⟨⟨(578159889/586345127),(158601532/586345127),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
private def eb390 : CertBound := ⟨true,true,⟨⟨(72484603/74620302),(22447511/74620302),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb391 : CertBound := ⟨true,true,⟨⟨(15100278/14953519),(4563022/14953519),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
private def eb392 : CertBound := ⟨true,true,⟨⟨(1769568852/1668385477),(409725352/1668385477),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
private def eb393 : CertBound := ⟨true,true,⟨⟨(108863233/104316086),(4162065/14902298),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
namespace LookupFast17
private theorem length01 : lowerEarlyTerminalBounds01.length = 150 := by rfl
private theorem length02 : lowerEarlyTerminalBounds02.length = 150 := by rfl
private theorem length03 : lowerEarlyTerminalBounds03.length = 150 := by rfl
private theorem length04 : lowerEarlyTerminalBounds04.length = 150 := by rfl
private theorem length05 : lowerEarlyTerminalBounds05.length = 150 := by rfl
private theorem length06 : lowerEarlyTerminalBounds06.length = 150 := by rfl
private theorem length07 : lowerEarlyTerminalBounds07.length = 150 := by rfl
private theorem length08 : lowerEarlyTerminalBounds08.length = 150 := by rfl
private theorem length09 : lowerEarlyTerminalBounds09.length = 38 := by rfl
private theorem of_local (id : Nat) (b : CertBound) (h : lowerEarlyTerminalBounds[id-1]? = some b) :
    lowerEarlyTerminalBound lowerEarlyTerminalEarly3 id = b := by
  change (lowerEarlyTerminalBounds[id-1]?).getD _ = b
  rw [h]
  rfl
private theorem chunk1 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[0+k]? = lowerEarlyTerminalBounds01[k]? := by
  unfold lowerEarlyTerminalBounds
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05) (by simp only [List.length_append, length01, length02, length03, length04, length05]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04) (by simp only [List.length_append, length01, length02, length03, length04]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03) (by simp only [List.length_append, length01, length02, length03]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02) (by simp only [List.length_append, length01, length02]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01) (by simp only [List.length_append, length01]; omega)]
  simp only [Nat.zero_add]
private theorem chunk2 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[150+k]? = lowerEarlyTerminalBounds02[k]? := by
  unfold lowerEarlyTerminalBounds
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05) (by simp only [List.length_append, length01, length02, length03, length04, length05]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04) (by simp only [List.length_append, length01, length02, length03, length04]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03) (by simp only [List.length_append, length01, length02, length03]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02) (by simp only [List.length_append, length01, length02]; omega)]
  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01) (by simp only [List.length_append, length01]; omega)]
  simp only [List.length_append, length01]
  exact congrArg (fun j => lowerEarlyTerminalBounds02[j]?) (by omega)
private theorem chunk3 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[300+k]? = lowerEarlyTerminalBounds03[k]? := by
  unfold lowerEarlyTerminalBounds
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05) (by simp only [List.length_append, length01, length02, length03, length04, length05]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04) (by simp only [List.length_append, length01, length02, length03, length04]; omega)]
  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03) (by simp only [List.length_append, length01, length02, length03]; omega)]
  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02) (by simp only [List.length_append, length01, length02]; omega)]
  simp only [List.length_append, length01, length02]
  exact congrArg (fun j => lowerEarlyTerminalBounds03[j]?) (by omega)
private theorem selected1 :
  (lowerEarlyTerminalBounds01[1]? = some eb2) ∧
  (lowerEarlyTerminalBounds01[2]? = some eb3) ∧
  (lowerEarlyTerminalBounds01[5]? = some eb6) ∧
  (lowerEarlyTerminalBounds01[6]? = some eb7) ∧
  (lowerEarlyTerminalBounds01[7]? = some eb8) ∧
  (lowerEarlyTerminalBounds01[11]? = some eb12) ∧
  (lowerEarlyTerminalBounds01[12]? = some eb13) ∧
  (lowerEarlyTerminalBounds01[13]? = some eb14) ∧
  (lowerEarlyTerminalBounds01[14]? = some eb15) ∧
  (lowerEarlyTerminalBounds01[22]? = some eb23) ∧
  (lowerEarlyTerminalBounds01[26]? = some eb27) ∧
  (lowerEarlyTerminalBounds01[27]? = some eb28) ∧
  (lowerEarlyTerminalBounds01[32]? = some eb33) ∧
  (lowerEarlyTerminalBounds01[34]? = some eb35) ∧
  (lowerEarlyTerminalBounds01[35]? = some eb36) ∧
  (lowerEarlyTerminalBounds01[38]? = some eb39) ∧
  (lowerEarlyTerminalBounds01[42]? = some eb43) ∧
  (lowerEarlyTerminalBounds01[44]? = some eb45) ∧
  (lowerEarlyTerminalBounds01[49]? = some eb50) ∧
  (lowerEarlyTerminalBounds01[50]? = some eb51) ∧
  (lowerEarlyTerminalBounds01[51]? = some eb52) ∧
  (lowerEarlyTerminalBounds01[52]? = some eb53) ∧
  (lowerEarlyTerminalBounds01[59]? = some eb60) ∧
  (lowerEarlyTerminalBounds01[60]? = some eb61) ∧
  (lowerEarlyTerminalBounds01[65]? = some eb66) ∧
  (lowerEarlyTerminalBounds01[68]? = some eb69) ∧
  (lowerEarlyTerminalBounds01[69]? = some eb70) ∧
  (lowerEarlyTerminalBounds01[70]? = some eb71) ∧
  (lowerEarlyTerminalBounds01[74]? = some eb75) ∧
  (lowerEarlyTerminalBounds01[75]? = some eb76) ∧
  (lowerEarlyTerminalBounds01[83]? = some eb84) ∧
  (lowerEarlyTerminalBounds01[85]? = some eb86) ∧
  (lowerEarlyTerminalBounds01[86]? = some eb87) ∧
  (lowerEarlyTerminalBounds01[89]? = some eb90) ∧
  (lowerEarlyTerminalBounds01[95]? = some eb96) ∧
  (lowerEarlyTerminalBounds01[99]? = some eb100) ∧
  (lowerEarlyTerminalBounds01[100]? = some eb101) ∧
  (lowerEarlyTerminalBounds01[101]? = some eb102) ∧
  (lowerEarlyTerminalBounds01[102]? = some eb103) ∧
  (lowerEarlyTerminalBounds01[104]? = some eb105) ∧
  (lowerEarlyTerminalBounds01[105]? = some eb106) ∧
  (lowerEarlyTerminalBounds01[106]? = some eb107) ∧
  (lowerEarlyTerminalBounds01[108]? = some eb109) ∧
  (lowerEarlyTerminalBounds01[113]? = some eb114) ∧
  (lowerEarlyTerminalBounds01[115]? = some eb116) ∧
  (lowerEarlyTerminalBounds01[117]? = some eb118) ∧
  (lowerEarlyTerminalBounds01[118]? = some eb119) ∧
  (lowerEarlyTerminalBounds01[119]? = some eb120) ∧
  (lowerEarlyTerminalBounds01[120]? = some eb121) ∧
  (lowerEarlyTerminalBounds01[121]? = some eb122) ∧
  (lowerEarlyTerminalBounds01[124]? = some eb125) ∧
  (lowerEarlyTerminalBounds01[126]? = some eb127) ∧
  (lowerEarlyTerminalBounds01[128]? = some eb129) ∧
  (lowerEarlyTerminalBounds01[130]? = some eb131) ∧
  (lowerEarlyTerminalBounds01[133]? = some eb134) ∧
  (lowerEarlyTerminalBounds01[136]? = some eb137) ∧
  (lowerEarlyTerminalBounds01[139]? = some eb140) ∧
  (lowerEarlyTerminalBounds01[140]? = some eb141) ∧
  (lowerEarlyTerminalBounds01[143]? = some eb144) ∧
  (lowerEarlyTerminalBounds01[145]? = some eb146) ∧
  (lowerEarlyTerminalBounds01[146]? = some eb147) ∧
  (lowerEarlyTerminalBounds01[149]? = some eb150) := by
  exact And.intro (Eq.refl (some eb2)) (And.intro (Eq.refl (some eb3)) (And.intro (Eq.refl (some eb6)) (And.intro (Eq.refl (some eb7)) (And.intro (Eq.refl (some eb8)) (And.intro (Eq.refl (some eb12)) (And.intro (Eq.refl (some eb13)) (And.intro (Eq.refl (some eb14)) (And.intro (Eq.refl (some eb15)) (And.intro (Eq.refl (some eb23)) (And.intro (Eq.refl (some eb27)) (And.intro (Eq.refl (some eb28)) (And.intro (Eq.refl (some eb33)) (And.intro (Eq.refl (some eb35)) (And.intro (Eq.refl (some eb36)) (And.intro (Eq.refl (some eb39)) (And.intro (Eq.refl (some eb43)) (And.intro (Eq.refl (some eb45)) (And.intro (Eq.refl (some eb50)) (And.intro (Eq.refl (some eb51)) (And.intro (Eq.refl (some eb52)) (And.intro (Eq.refl (some eb53)) (And.intro (Eq.refl (some eb60)) (And.intro (Eq.refl (some eb61)) (And.intro (Eq.refl (some eb66)) (And.intro (Eq.refl (some eb69)) (And.intro (Eq.refl (some eb70)) (And.intro (Eq.refl (some eb71)) (And.intro (Eq.refl (some eb75)) (And.intro (Eq.refl (some eb76)) (And.intro (Eq.refl (some eb84)) (And.intro (Eq.refl (some eb86)) (And.intro (Eq.refl (some eb87)) (And.intro (Eq.refl (some eb90)) (And.intro (Eq.refl (some eb96)) (And.intro (Eq.refl (some eb100)) (And.intro (Eq.refl (some eb101)) (And.intro (Eq.refl (some eb102)) (And.intro (Eq.refl (some eb103)) (And.intro (Eq.refl (some eb105)) (And.intro (Eq.refl (some eb106)) (And.intro (Eq.refl (some eb107)) (And.intro (Eq.refl (some eb109)) (And.intro (Eq.refl (some eb114)) (And.intro (Eq.refl (some eb116)) (And.intro (Eq.refl (some eb118)) (And.intro (Eq.refl (some eb119)) (And.intro (Eq.refl (some eb120)) (And.intro (Eq.refl (some eb121)) (And.intro (Eq.refl (some eb122)) (And.intro (Eq.refl (some eb125)) (And.intro (Eq.refl (some eb127)) (And.intro (Eq.refl (some eb129)) (And.intro (Eq.refl (some eb131)) (And.intro (Eq.refl (some eb134)) (And.intro (Eq.refl (some eb137)) (And.intro (Eq.refl (some eb140)) (And.intro (Eq.refl (some eb141)) (And.intro (Eq.refl (some eb144)) (And.intro (Eq.refl (some eb146)) (And.intro (Eq.refl (some eb147)) (Eq.refl (some eb150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem selected2 :
  (lowerEarlyTerminalBounds02[3]? = some eb154) ∧
  (lowerEarlyTerminalBounds02[8]? = some eb159) ∧
  (lowerEarlyTerminalBounds02[9]? = some eb160) ∧
  (lowerEarlyTerminalBounds02[11]? = some eb162) ∧
  (lowerEarlyTerminalBounds02[12]? = some eb163) ∧
  (lowerEarlyTerminalBounds02[13]? = some eb164) ∧
  (lowerEarlyTerminalBounds02[14]? = some eb165) ∧
  (lowerEarlyTerminalBounds02[20]? = some eb171) ∧
  (lowerEarlyTerminalBounds02[21]? = some eb172) ∧
  (lowerEarlyTerminalBounds02[22]? = some eb173) ∧
  (lowerEarlyTerminalBounds02[23]? = some eb174) ∧
  (lowerEarlyTerminalBounds02[32]? = some eb183) ∧
  (lowerEarlyTerminalBounds02[35]? = some eb186) ∧
  (lowerEarlyTerminalBounds02[36]? = some eb187) ∧
  (lowerEarlyTerminalBounds02[37]? = some eb188) ∧
  (lowerEarlyTerminalBounds02[42]? = some eb193) ∧
  (lowerEarlyTerminalBounds02[46]? = some eb197) ∧
  (lowerEarlyTerminalBounds02[48]? = some eb199) ∧
  (lowerEarlyTerminalBounds02[52]? = some eb203) ∧
  (lowerEarlyTerminalBounds02[56]? = some eb207) ∧
  (lowerEarlyTerminalBounds02[57]? = some eb208) ∧
  (lowerEarlyTerminalBounds02[63]? = some eb214) ∧
  (lowerEarlyTerminalBounds02[64]? = some eb215) ∧
  (lowerEarlyTerminalBounds02[65]? = some eb216) ∧
  (lowerEarlyTerminalBounds02[66]? = some eb217) ∧
  (lowerEarlyTerminalBounds02[72]? = some eb223) ∧
  (lowerEarlyTerminalBounds02[75]? = some eb226) ∧
  (lowerEarlyTerminalBounds02[78]? = some eb229) ∧
  (lowerEarlyTerminalBounds02[79]? = some eb230) ∧
  (lowerEarlyTerminalBounds02[80]? = some eb231) ∧
  (lowerEarlyTerminalBounds02[84]? = some eb235) ∧
  (lowerEarlyTerminalBounds02[85]? = some eb236) ∧
  (lowerEarlyTerminalBounds02[90]? = some eb241) ∧
  (lowerEarlyTerminalBounds02[92]? = some eb243) ∧
  (lowerEarlyTerminalBounds02[94]? = some eb245) ∧
  (lowerEarlyTerminalBounds02[96]? = some eb247) ∧
  (lowerEarlyTerminalBounds02[100]? = some eb251) ∧
  (lowerEarlyTerminalBounds02[101]? = some eb252) ∧
  (lowerEarlyTerminalBounds02[106]? = some eb257) ∧
  (lowerEarlyTerminalBounds02[107]? = some eb258) ∧
  (lowerEarlyTerminalBounds02[108]? = some eb259) ∧
  (lowerEarlyTerminalBounds02[109]? = some eb260) ∧
  (lowerEarlyTerminalBounds02[110]? = some eb261) ∧
  (lowerEarlyTerminalBounds02[117]? = some eb268) ∧
  (lowerEarlyTerminalBounds02[121]? = some eb272) ∧
  (lowerEarlyTerminalBounds02[129]? = some eb280) ∧
  (lowerEarlyTerminalBounds02[131]? = some eb282) ∧
  (lowerEarlyTerminalBounds02[132]? = some eb283) ∧
  (lowerEarlyTerminalBounds02[135]? = some eb286) ∧
  (lowerEarlyTerminalBounds02[141]? = some eb292) ∧
  (lowerEarlyTerminalBounds02[145]? = some eb296) ∧
  (lowerEarlyTerminalBounds02[146]? = some eb297) ∧
  (lowerEarlyTerminalBounds02[147]? = some eb298) ∧
  (lowerEarlyTerminalBounds02[148]? = some eb299) ∧
  (lowerEarlyTerminalBounds02[149]? = some eb300) := by
  exact And.intro (Eq.refl (some eb154)) (And.intro (Eq.refl (some eb159)) (And.intro (Eq.refl (some eb160)) (And.intro (Eq.refl (some eb162)) (And.intro (Eq.refl (some eb163)) (And.intro (Eq.refl (some eb164)) (And.intro (Eq.refl (some eb165)) (And.intro (Eq.refl (some eb171)) (And.intro (Eq.refl (some eb172)) (And.intro (Eq.refl (some eb173)) (And.intro (Eq.refl (some eb174)) (And.intro (Eq.refl (some eb183)) (And.intro (Eq.refl (some eb186)) (And.intro (Eq.refl (some eb187)) (And.intro (Eq.refl (some eb188)) (And.intro (Eq.refl (some eb193)) (And.intro (Eq.refl (some eb197)) (And.intro (Eq.refl (some eb199)) (And.intro (Eq.refl (some eb203)) (And.intro (Eq.refl (some eb207)) (And.intro (Eq.refl (some eb208)) (And.intro (Eq.refl (some eb214)) (And.intro (Eq.refl (some eb215)) (And.intro (Eq.refl (some eb216)) (And.intro (Eq.refl (some eb217)) (And.intro (Eq.refl (some eb223)) (And.intro (Eq.refl (some eb226)) (And.intro (Eq.refl (some eb229)) (And.intro (Eq.refl (some eb230)) (And.intro (Eq.refl (some eb231)) (And.intro (Eq.refl (some eb235)) (And.intro (Eq.refl (some eb236)) (And.intro (Eq.refl (some eb241)) (And.intro (Eq.refl (some eb243)) (And.intro (Eq.refl (some eb245)) (And.intro (Eq.refl (some eb247)) (And.intro (Eq.refl (some eb251)) (And.intro (Eq.refl (some eb252)) (And.intro (Eq.refl (some eb257)) (And.intro (Eq.refl (some eb258)) (And.intro (Eq.refl (some eb259)) (And.intro (Eq.refl (some eb260)) (And.intro (Eq.refl (some eb261)) (And.intro (Eq.refl (some eb268)) (And.intro (Eq.refl (some eb272)) (And.intro (Eq.refl (some eb280)) (And.intro (Eq.refl (some eb282)) (And.intro (Eq.refl (some eb283)) (And.intro (Eq.refl (some eb286)) (And.intro (Eq.refl (some eb292)) (And.intro (Eq.refl (some eb296)) (And.intro (Eq.refl (some eb297)) (And.intro (Eq.refl (some eb298)) (And.intro (Eq.refl (some eb299)) (Eq.refl (some eb300)))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem selected3 :
  (lowerEarlyTerminalBounds03[0]? = some eb301) ∧
  (lowerEarlyTerminalBounds03[7]? = some eb308) ∧
  (lowerEarlyTerminalBounds03[11]? = some eb312) ∧
  (lowerEarlyTerminalBounds03[17]? = some eb318) ∧
  (lowerEarlyTerminalBounds03[19]? = some eb320) ∧
  (lowerEarlyTerminalBounds03[20]? = some eb321) ∧
  (lowerEarlyTerminalBounds03[23]? = some eb324) ∧
  (lowerEarlyTerminalBounds03[24]? = some eb325) ∧
  (lowerEarlyTerminalBounds03[26]? = some eb327) ∧
  (lowerEarlyTerminalBounds03[27]? = some eb328) ∧
  (lowerEarlyTerminalBounds03[28]? = some eb329) ∧
  (lowerEarlyTerminalBounds03[30]? = some eb331) ∧
  (lowerEarlyTerminalBounds03[31]? = some eb332) ∧
  (lowerEarlyTerminalBounds03[32]? = some eb333) ∧
  (lowerEarlyTerminalBounds03[33]? = some eb334) ∧
  (lowerEarlyTerminalBounds03[34]? = some eb335) ∧
  (lowerEarlyTerminalBounds03[35]? = some eb336) ∧
  (lowerEarlyTerminalBounds03[36]? = some eb337) ∧
  (lowerEarlyTerminalBounds03[37]? = some eb338) ∧
  (lowerEarlyTerminalBounds03[39]? = some eb340) ∧
  (lowerEarlyTerminalBounds03[40]? = some eb341) ∧
  (lowerEarlyTerminalBounds03[41]? = some eb342) ∧
  (lowerEarlyTerminalBounds03[44]? = some eb345) ∧
  (lowerEarlyTerminalBounds03[45]? = some eb346) ∧
  (lowerEarlyTerminalBounds03[46]? = some eb347) ∧
  (lowerEarlyTerminalBounds03[49]? = some eb350) ∧
  (lowerEarlyTerminalBounds03[57]? = some eb358) ∧
  (lowerEarlyTerminalBounds03[58]? = some eb359) ∧
  (lowerEarlyTerminalBounds03[59]? = some eb360) ∧
  (lowerEarlyTerminalBounds03[62]? = some eb363) ∧
  (lowerEarlyTerminalBounds03[65]? = some eb366) ∧
  (lowerEarlyTerminalBounds03[69]? = some eb370) ∧
  (lowerEarlyTerminalBounds03[74]? = some eb375) ∧
  (lowerEarlyTerminalBounds03[75]? = some eb376) ∧
  (lowerEarlyTerminalBounds03[79]? = some eb380) ∧
  (lowerEarlyTerminalBounds03[81]? = some eb382) ∧
  (lowerEarlyTerminalBounds03[82]? = some eb383) ∧
  (lowerEarlyTerminalBounds03[83]? = some eb384) ∧
  (lowerEarlyTerminalBounds03[84]? = some eb385) ∧
  (lowerEarlyTerminalBounds03[85]? = some eb386) ∧
  (lowerEarlyTerminalBounds03[86]? = some eb387) ∧
  (lowerEarlyTerminalBounds03[87]? = some eb388) ∧
  (lowerEarlyTerminalBounds03[88]? = some eb389) ∧
  (lowerEarlyTerminalBounds03[89]? = some eb390) ∧
  (lowerEarlyTerminalBounds03[90]? = some eb391) ∧
  (lowerEarlyTerminalBounds03[91]? = some eb392) ∧
  (lowerEarlyTerminalBounds03[92]? = some eb393) := by
  exact And.intro (Eq.refl (some eb301)) (And.intro (Eq.refl (some eb308)) (And.intro (Eq.refl (some eb312)) (And.intro (Eq.refl (some eb318)) (And.intro (Eq.refl (some eb320)) (And.intro (Eq.refl (some eb321)) (And.intro (Eq.refl (some eb324)) (And.intro (Eq.refl (some eb325)) (And.intro (Eq.refl (some eb327)) (And.intro (Eq.refl (some eb328)) (And.intro (Eq.refl (some eb329)) (And.intro (Eq.refl (some eb331)) (And.intro (Eq.refl (some eb332)) (And.intro (Eq.refl (some eb333)) (And.intro (Eq.refl (some eb334)) (And.intro (Eq.refl (some eb335)) (And.intro (Eq.refl (some eb336)) (And.intro (Eq.refl (some eb337)) (And.intro (Eq.refl (some eb338)) (And.intro (Eq.refl (some eb340)) (And.intro (Eq.refl (some eb341)) (And.intro (Eq.refl (some eb342)) (And.intro (Eq.refl (some eb345)) (And.intro (Eq.refl (some eb346)) (And.intro (Eq.refl (some eb347)) (And.intro (Eq.refl (some eb350)) (And.intro (Eq.refl (some eb358)) (And.intro (Eq.refl (some eb359)) (And.intro (Eq.refl (some eb360)) (And.intro (Eq.refl (some eb363)) (And.intro (Eq.refl (some eb366)) (And.intro (Eq.refl (some eb370)) (And.intro (Eq.refl (some eb375)) (And.intro (Eq.refl (some eb376)) (And.intro (Eq.refl (some eb380)) (And.intro (Eq.refl (some eb382)) (And.intro (Eq.refl (some eb383)) (And.intro (Eq.refl (some eb384)) (And.intro (Eq.refl (some eb385)) (And.intro (Eq.refl (some eb386)) (And.intro (Eq.refl (some eb387)) (And.intro (Eq.refl (some eb388)) (And.intro (Eq.refl (some eb389)) (And.intro (Eq.refl (some eb390)) (And.intro (Eq.refl (some eb391)) (And.intro (Eq.refl (some eb392)) (Eq.refl (some eb393)))))))))))))))))))))))))))))))))))))))))))))))
end LookupFast17
private theorem lookup2 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 2 = eb2 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 1 (by omega)).trans LookupFast17.selected1.1
private theorem lookup3 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 3 = eb3 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 2 (by omega)).trans LookupFast17.selected1.2.1
private theorem lookup6 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 6 = eb6 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 5 (by omega)).trans LookupFast17.selected1.2.2.1
private theorem lookup7 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 7 = eb7 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 6 (by omega)).trans LookupFast17.selected1.2.2.2.1
private theorem lookup8 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 8 = eb8 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 7 (by omega)).trans LookupFast17.selected1.2.2.2.2.1
private theorem lookup12 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 12 = eb12 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 11 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.1
private theorem lookup13 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 13 = eb13 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 12 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.1
private theorem lookup14 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 14 = eb14 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 13 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.1
private theorem lookup15 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 15 = eb15 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 14 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.1
private theorem lookup23 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 23 = eb23 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 22 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.1
private theorem lookup27 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 27 = eb27 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 26 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup28 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 28 = eb28 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 27 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup33 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 33 = eb33 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 32 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup35 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 35 = eb35 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 34 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup36 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 36 = eb36 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 35 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup39 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 39 = eb39 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 38 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup43 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 43 = eb43 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 42 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup45 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 45 = eb45 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 44 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup50 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 50 = eb50 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 49 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup51 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 51 = eb51 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 50 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup52 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 52 = eb52 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 51 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup53 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 53 = eb53 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 52 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup60 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 60 = eb60 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 59 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup61 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 61 = eb61 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 60 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup66 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 66 = eb66 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 65 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup69 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 69 = eb69 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 68 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup70 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 70 = eb70 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 69 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup71 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 71 = eb71 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 70 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup75 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 75 = eb75 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 74 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup76 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 76 = eb76 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 75 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup84 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 84 = eb84 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 83 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup86 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 86 = eb86 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 85 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup87 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 87 = eb87 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 86 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup90 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 90 = eb90 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 89 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup96 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 96 = eb96 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 95 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup100 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 100 = eb100 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 99 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup101 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 101 = eb101 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 100 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup102 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 102 = eb102 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 101 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup103 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 103 = eb103 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 102 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup105 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 105 = eb105 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 104 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup106 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 106 = eb106 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 105 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup107 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 107 = eb107 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 106 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup109 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 109 = eb109 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 108 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup114 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 114 = eb114 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 113 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup116 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 116 = eb116 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 115 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup118 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 118 = eb118 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 117 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup119 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 119 = eb119 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 118 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup120 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 120 = eb120 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 119 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup121 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 121 = eb121 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 120 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup122 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 122 = eb122 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 121 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup125 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 125 = eb125 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 124 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup127 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 127 = eb127 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 126 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup129 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 129 = eb129 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 128 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup131 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 131 = eb131 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 130 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup134 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 134 = eb134 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 133 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup137 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 137 = eb137 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 136 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup140 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 140 = eb140 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 139 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup141 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 141 = eb141 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 140 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup144 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 144 = eb144 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 143 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup146 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 146 = eb146 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 145 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup147 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 147 = eb147 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 146 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup150 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 150 = eb150 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 149 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
private theorem lookup154 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 154 = eb154 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 3 (by omega)).trans LookupFast17.selected2.1
private theorem lookup159 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 159 = eb159 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 8 (by omega)).trans LookupFast17.selected2.2.1
private theorem lookup160 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 160 = eb160 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 9 (by omega)).trans LookupFast17.selected2.2.2.1
private theorem lookup162 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 162 = eb162 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 11 (by omega)).trans LookupFast17.selected2.2.2.2.1
private theorem lookup163 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 163 = eb163 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 12 (by omega)).trans LookupFast17.selected2.2.2.2.2.1
private theorem lookup164 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 164 = eb164 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 13 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.1
private theorem lookup165 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 165 = eb165 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 14 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.1
private theorem lookup171 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 171 = eb171 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 20 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.1
private theorem lookup172 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 172 = eb172 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 21 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.1
private theorem lookup173 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 173 = eb173 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 22 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.1
private theorem lookup174 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 174 = eb174 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 23 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup183 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 183 = eb183 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 32 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup186 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 186 = eb186 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 35 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup187 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 187 = eb187 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 36 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup188 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 188 = eb188 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 37 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup193 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 193 = eb193 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 42 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup197 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 197 = eb197 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 46 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup199 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 199 = eb199 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 48 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup203 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 203 = eb203 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 52 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup207 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 207 = eb207 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 56 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup208 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 208 = eb208 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 57 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup214 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 214 = eb214 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 63 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup215 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 215 = eb215 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 64 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup216 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 216 = eb216 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 65 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup217 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 217 = eb217 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 66 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup223 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 223 = eb223 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 72 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup226 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 226 = eb226 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 75 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup229 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 229 = eb229 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 78 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup230 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 230 = eb230 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 79 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup231 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 231 = eb231 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 80 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup235 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 235 = eb235 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 84 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup236 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 236 = eb236 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 85 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup241 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 241 = eb241 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 90 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup243 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 243 = eb243 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 92 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup245 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 245 = eb245 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 94 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup247 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 247 = eb247 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 96 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup251 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 251 = eb251 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 100 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup252 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 252 = eb252 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 101 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup257 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 257 = eb257 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 106 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup258 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 258 = eb258 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 107 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup259 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 259 = eb259 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 108 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup260 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 260 = eb260 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 109 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup261 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 261 = eb261 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 110 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup268 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 268 = eb268 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 117 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup272 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 272 = eb272 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 121 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup280 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 280 = eb280 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 129 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup282 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 282 = eb282 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 131 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup283 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 283 = eb283 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 132 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup286 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 286 = eb286 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 135 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup292 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 292 = eb292 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 141 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup296 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 296 = eb296 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 145 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup297 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 297 = eb297 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 146 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup298 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 298 = eb298 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 147 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup299 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 299 = eb299 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 148 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup300 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 300 = eb300 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 149 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
private theorem lookup301 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 301 = eb301 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 0 (by omega)).trans LookupFast17.selected3.1
private theorem lookup308 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 308 = eb308 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 7 (by omega)).trans LookupFast17.selected3.2.1
private theorem lookup312 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 312 = eb312 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 11 (by omega)).trans LookupFast17.selected3.2.2.1
private theorem lookup318 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 318 = eb318 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 17 (by omega)).trans LookupFast17.selected3.2.2.2.1
private theorem lookup320 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 320 = eb320 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 19 (by omega)).trans LookupFast17.selected3.2.2.2.2.1
private theorem lookup321 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 321 = eb321 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 20 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.1
private theorem lookup324 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 324 = eb324 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 23 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.1
private theorem lookup325 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 325 = eb325 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 24 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.1
private theorem lookup327 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 327 = eb327 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 26 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.1
private theorem lookup328 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 328 = eb328 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 27 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.1
private theorem lookup329 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 329 = eb329 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 28 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup331 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 331 = eb331 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 30 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup332 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 332 = eb332 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 31 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup333 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 333 = eb333 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 32 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup334 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 334 = eb334 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 33 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup335 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 335 = eb335 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 34 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup336 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 336 = eb336 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 35 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup337 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 337 = eb337 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 36 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup338 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 338 = eb338 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 37 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup340 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 340 = eb340 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 39 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup341 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 341 = eb341 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 40 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup342 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 342 = eb342 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 41 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup345 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 345 = eb345 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 44 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup346 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 346 = eb346 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 45 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup347 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 347 = eb347 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 46 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup350 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 350 = eb350 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 49 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup358 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 358 = eb358 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 57 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup359 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 359 = eb359 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 58 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup360 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 360 = eb360 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 59 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup363 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 363 = eb363 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 62 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup366 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 366 = eb366 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 65 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup370 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 370 = eb370 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 69 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup375 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 375 = eb375 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 74 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup376 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 376 = eb376 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 75 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup380 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 380 = eb380 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 79 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup382 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 382 = eb382 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 81 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup383 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 383 = eb383 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 82 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup384 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 384 = eb384 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 83 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup385 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 385 = eb385 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 84 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup386 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 386 = eb386 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 85 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup387 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 387 = eb387 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 86 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup388 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 388 = eb388 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 87 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup389 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 389 = eb389 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 88 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup390 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 390 = eb390 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 89 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup391 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 391 = eb391 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 90 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup392 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 392 = eb392 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 91 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
private theorem lookup393 : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 393 = eb393 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 92 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
private theorem endpointNonneg1 : 0 ≤ certFieldLower (⟨(10/23),(-1/69),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg2 : 0 ≤ certFieldLower (⟨(5/11),(-1/11),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg3 : 0 ≤ certFieldLower (⟨(5/22),(1/22),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg4 : 0 ≤ certFieldLower (⟨(15/37),(-1/37),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg5 : 0 ≤ certFieldLower (⟨(135/326),0,0,(1/6846)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg6 : 0 ≤ certFieldLower (⟨(193/454),0,0,(-1/454)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg7 : 0 ≤ certFieldLower (⟨(168/409),(1/409),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg8 : 0 ≤ certFieldLower (⟨(223/529),(-1/529),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg9 : 0 ≤ certFieldLower (⟨(29/74),0,0,(1/222)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg10 : 0 ≤ certFieldLower (⟨(105/262),0,0,(1/262)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg11 : 0 ≤ certFieldLower (⟨(1077/2570),0,0,(-1/7710)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg12 : 0 ≤ certFieldLower (⟨(19/34),0,0,(-1/34)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg13 : 0 ≤ certFieldLower (⟨(1137/2714),(-1/8142),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg14 : 0 ≤ certFieldLower (⟨(29/82),0,0,(1/82)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg15 : 0 ≤ certFieldLower (⟨(89/214),(1/214),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg16 : 0 ≤ certFieldLower (⟨(487/1174),0,0,(-1/1174)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg17 : 0 ≤ certFieldLower (⟨(1272/3013),(1/3013),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg18 : 0 ≤ certFieldLower (⟨(73/170),0,0,(-1/510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg19 : 0 ≤ certFieldLower (⟨(1005/2426),(1/7278),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg20 : 0 ≤ certFieldLower (⟨(39/134),0,0,(1/402)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg21 : 0 ≤ certFieldLower (⟨(15/34),0,0,(-1/34)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg22 : 0 ≤ certFieldLower (⟨(-1/2),0,0,(1/6)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg23 : 0 ≤ certFieldLower (⟨(517/1249),(-1/1249),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg24 : 0 ≤ certFieldLower (⟨(42/143),(1/429),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg25 : 0 ≤ certFieldLower (⟨(271/1006),(-1/1006),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg26 : 0 ≤ certFieldLower (⟨(1209/2866),0,0,(1/2866)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg27 : 0 ≤ certFieldLower (⟨(-1/10),0,0,(1/10)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg28 : 0 ≤ certFieldLower (⟨(63/170),0,0,(-1/510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg29 : 0 ≤ certFieldLower (⟨(9/10),0,0,(-1/10)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg30 : 0 ≤ certFieldLower (⟨(35/94),(1/94),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg31 : 0 ≤ certFieldLower (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg32 : 0 ≤ certFieldLower (⟨(105/262),0,0,(-1/262)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg33 : 0 ≤ certFieldLower (⟨(247/649),(1/649),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg34 : 0 ≤ certFieldLower (⟨(177/454),(-1/454),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg35 : 0 ≤ certFieldLower (⟨(251/670),0,0,(1/670)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg36 : 0 ≤ certFieldLower (⟨(31/82),0,0,(1/574)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg37 : 0 ≤ certFieldLower (⟨(83/202),0,0,(-1/202)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg38 : 0 ≤ certFieldLower (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg39 : 0 ≤ certFieldLower (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg40 : 0 ≤ certFieldLower (⟨(31/94),0,0,(1/94)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg41 : 0 ≤ certFieldLower (⟨(1/2),0,0,(-1/42)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg42 : 0 ≤ certFieldLower (⟨(32/83),(-1/249),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg43 : 0 ≤ certFieldLower (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg44 : 0 ≤ certFieldLower (⟨(523/1354),0,0,(1/1354)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg45 : 0 ≤ certFieldLower (⟨(3734/9757),(1/9757),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg46 : 0 ≤ certFieldLower (⟨(227/590),0,0,(1/1770)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg47 : 0 ≤ certFieldLower (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg48 : 0 ≤ certFieldLower (⟨(353/914),(1/2742),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg49 : 0 ≤ certFieldLower (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg50 : 0 ≤ certFieldLower (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg51 : 0 ≤ certFieldLower (⟨(579/1510),0,0,(1/1510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg52 : 0 ≤ certFieldLower (⟨(167/430),0,0,(-1/3010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg53 : 0 ≤ certFieldLower (⟨(553/1429),(1/1429),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg54 : 0 ≤ certFieldLower (⟨(2589/6674),(1/20022),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg55 : 0 ≤ certFieldLower (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg56 : 0 ≤ certFieldLower (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg57 : 0 ≤ certFieldLower (⟨(1932/4957),(1/4957),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg58 : 0 ≤ certFieldLower (⟨(779/1994),(-1/5982),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg59 : 0 ≤ certFieldLower (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg60 : 0 ≤ certFieldLower (⟨(167/430),0,0,(1/3010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg61 : 0 ≤ certFieldLower (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg62 : 0 ≤ certFieldLower (⟨(13260/33937),(1/33937),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg63 : 0 ≤ certFieldLower (⟨(278/709),(-1/709),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg64 : 0 ≤ certFieldLower (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg65 : 0 ≤ certFieldLower (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg66 : 0 ≤ certFieldLower (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem threshold2 : certThresholdDataValid eb2.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg2⟩

private theorem threshold3 : certThresholdDataValid eb3.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg4⟩

private theorem threshold6 : certThresholdDataValid eb6.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg6⟩

private theorem threshold7 : certThresholdDataValid eb7.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem threshold8 : certThresholdDataValid eb8.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg6⟩

private theorem threshold12 : certThresholdDataValid eb12.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem threshold13 : certThresholdDataValid eb13.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg11⟩

private theorem threshold14 : certThresholdDataValid eb14.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg12⟩

private theorem threshold15 : certThresholdDataValid eb15.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg13⟩

private theorem threshold23 : certThresholdDataValid eb23.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg6⟩

private theorem threshold27 : certThresholdDataValid eb27.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem threshold28 : certThresholdDataValid eb28.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg1⟩

private theorem threshold33 : certThresholdDataValid eb33.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold35 : certThresholdDataValid eb35.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold36 : certThresholdDataValid eb36.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem threshold39 : certThresholdDataValid eb39.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg1⟩

private theorem threshold43 : certThresholdDataValid eb43.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem threshold45 : certThresholdDataValid eb45.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg1⟩

private theorem threshold50 : certThresholdDataValid eb50.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg11⟩

private theorem threshold51 : certThresholdDataValid eb51.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem threshold52 : certThresholdDataValid eb52.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg18⟩

private theorem threshold53 : certThresholdDataValid eb53.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg6⟩

private theorem threshold60 : certThresholdDataValid eb60.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg11⟩

private theorem threshold61 : certThresholdDataValid eb61.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg12⟩

private theorem threshold66 : certThresholdDataValid eb66.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem threshold69 : certThresholdDataValid eb69.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg6⟩

private theorem threshold70 : certThresholdDataValid eb70.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg6⟩

private theorem threshold71 : certThresholdDataValid eb71.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg8⟩

private theorem threshold75 : certThresholdDataValid eb75.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem threshold76 : certThresholdDataValid eb76.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg1⟩

private theorem threshold84 : certThresholdDataValid eb84.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold86 : certThresholdDataValid eb86.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold87 : certThresholdDataValid eb87.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem threshold90 : certThresholdDataValid eb90.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg1⟩

private theorem threshold96 : certThresholdDataValid eb96.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg1⟩

private theorem threshold100 : certThresholdDataValid eb100.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem threshold101 : certThresholdDataValid eb101.threshold := by
  exact ⟨endpointNonneg20, endpointNonneg21⟩

private theorem threshold102 : certThresholdDataValid eb102.threshold := by
  exact ⟨endpointNonneg22, endpointNonneg21⟩

private theorem threshold103 : certThresholdDataValid eb103.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg1⟩

private theorem threshold105 : certThresholdDataValid eb105.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold106 : certThresholdDataValid eb106.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg1⟩

private theorem threshold107 : certThresholdDataValid eb107.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold109 : certThresholdDataValid eb109.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg23⟩

private theorem threshold114 : certThresholdDataValid eb114.threshold := by
  exact ⟨endpointNonneg20, endpointNonneg21⟩

private theorem threshold116 : certThresholdDataValid eb116.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg1⟩

private theorem threshold118 : certThresholdDataValid eb118.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg1⟩

private theorem threshold119 : certThresholdDataValid eb119.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg23⟩

private theorem threshold120 : certThresholdDataValid eb120.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg15⟩

private theorem threshold121 : certThresholdDataValid eb121.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg12⟩

private theorem threshold122 : certThresholdDataValid eb122.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg15⟩

private theorem threshold125 : certThresholdDataValid eb125.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg17⟩

private theorem threshold127 : certThresholdDataValid eb127.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg1⟩

private theorem threshold129 : certThresholdDataValid eb129.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold131 : certThresholdDataValid eb131.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem threshold134 : certThresholdDataValid eb134.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg1⟩

private theorem threshold137 : certThresholdDataValid eb137.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg1⟩

private theorem threshold140 : certThresholdDataValid eb140.threshold := by
  exact ⟨endpointNonneg4, endpointNonneg15⟩

private theorem threshold141 : certThresholdDataValid eb141.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem threshold144 : certThresholdDataValid eb144.threshold := by
  exact ⟨endpointNonneg4, endpointNonneg15⟩

private theorem threshold146 : certThresholdDataValid eb146.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem threshold147 : certThresholdDataValid eb147.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg29⟩

private theorem threshold150 : certThresholdDataValid eb150.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg12⟩

private theorem threshold154 : certThresholdDataValid eb154.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg12⟩

private theorem threshold159 : certThresholdDataValid eb159.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg30⟩

private theorem threshold160 : certThresholdDataValid eb160.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg2⟩

private theorem threshold162 : certThresholdDataValid eb162.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg32⟩

private theorem threshold163 : certThresholdDataValid eb163.threshold := by
  exact ⟨endpointNonneg33, endpointNonneg34⟩

private theorem threshold164 : certThresholdDataValid eb164.threshold := by
  exact ⟨endpointNonneg35, endpointNonneg32⟩

private theorem threshold165 : certThresholdDataValid eb165.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem threshold171 : certThresholdDataValid eb171.threshold := by
  exact ⟨endpointNonneg33, endpointNonneg34⟩

private theorem threshold172 : certThresholdDataValid eb172.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg38⟩

private theorem threshold173 : certThresholdDataValid eb173.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem threshold174 : certThresholdDataValid eb174.threshold := by
  exact ⟨endpointNonneg33, endpointNonneg39⟩

private theorem threshold183 : certThresholdDataValid eb183.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg32⟩

private theorem threshold186 : certThresholdDataValid eb186.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg32⟩

private theorem threshold187 : certThresholdDataValid eb187.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg41⟩

private theorem threshold188 : certThresholdDataValid eb188.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg42⟩

private theorem threshold193 : certThresholdDataValid eb193.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg42⟩

private theorem threshold197 : certThresholdDataValid eb197.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg43⟩

private theorem threshold199 : certThresholdDataValid eb199.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg41⟩

private theorem threshold203 : certThresholdDataValid eb203.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold207 : certThresholdDataValid eb207.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold208 : certThresholdDataValid eb208.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg41⟩

private theorem threshold214 : certThresholdDataValid eb214.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg38⟩

private theorem threshold215 : certThresholdDataValid eb215.threshold := by
  exact ⟨endpointNonneg33, endpointNonneg34⟩

private theorem threshold216 : certThresholdDataValid eb216.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem threshold217 : certThresholdDataValid eb217.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg32⟩

private theorem threshold223 : certThresholdDataValid eb223.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg38⟩

private theorem threshold226 : certThresholdDataValid eb226.threshold := by
  exact ⟨endpointNonneg33, endpointNonneg34⟩

private theorem threshold229 : certThresholdDataValid eb229.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg32⟩

private theorem threshold230 : certThresholdDataValid eb230.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg32⟩

private theorem threshold231 : certThresholdDataValid eb231.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg34⟩

private theorem threshold235 : certThresholdDataValid eb235.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg41⟩

private theorem threshold236 : certThresholdDataValid eb236.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg42⟩

private theorem threshold241 : certThresholdDataValid eb241.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg42⟩

private theorem threshold243 : certThresholdDataValid eb243.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg41⟩

private theorem threshold245 : certThresholdDataValid eb245.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg43⟩

private theorem threshold247 : certThresholdDataValid eb247.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold251 : certThresholdDataValid eb251.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold252 : certThresholdDataValid eb252.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg41⟩

private theorem threshold257 : certThresholdDataValid eb257.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem threshold258 : certThresholdDataValid eb258.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg47⟩

private theorem threshold259 : certThresholdDataValid eb259.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg49⟩

private theorem threshold260 : certThresholdDataValid eb260.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg50⟩

private theorem threshold261 : certThresholdDataValid eb261.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg52⟩

private theorem threshold268 : certThresholdDataValid eb268.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg47⟩

private theorem threshold272 : certThresholdDataValid eb272.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg34⟩

private theorem threshold280 : certThresholdDataValid eb280.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg38⟩

private theorem threshold282 : certThresholdDataValid eb282.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg38⟩

private theorem threshold283 : certThresholdDataValid eb283.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem threshold286 : certThresholdDataValid eb286.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg34⟩

private theorem threshold292 : certThresholdDataValid eb292.threshold := by
  exact ⟨endpointNonneg54, endpointNonneg34⟩

private theorem threshold296 : certThresholdDataValid eb296.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem threshold297 : certThresholdDataValid eb297.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold298 : certThresholdDataValid eb298.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg56⟩

private theorem threshold299 : certThresholdDataValid eb299.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg58⟩

private theorem threshold300 : certThresholdDataValid eb300.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg59⟩

private theorem threshold301 : certThresholdDataValid eb301.threshold := by
  exact ⟨endpointNonneg60, endpointNonneg61⟩

private theorem threshold308 : certThresholdDataValid eb308.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg56⟩

private theorem threshold312 : certThresholdDataValid eb312.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg63⟩

private theorem threshold318 : certThresholdDataValid eb318.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg64⟩

private theorem threshold320 : certThresholdDataValid eb320.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg64⟩

private theorem threshold321 : certThresholdDataValid eb321.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold324 : certThresholdDataValid eb324.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold325 : certThresholdDataValid eb325.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg42⟩

private theorem threshold327 : certThresholdDataValid eb327.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg65⟩

private theorem threshold328 : certThresholdDataValid eb328.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg42⟩

private theorem threshold329 : certThresholdDataValid eb329.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg65⟩

private theorem threshold331 : certThresholdDataValid eb331.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg43⟩

private theorem threshold332 : certThresholdDataValid eb332.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg42⟩

private theorem threshold333 : certThresholdDataValid eb333.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg42⟩

private theorem threshold334 : certThresholdDataValid eb334.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg43⟩

private theorem threshold335 : certThresholdDataValid eb335.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg42⟩

private theorem threshold336 : certThresholdDataValid eb336.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg42⟩

private theorem threshold337 : certThresholdDataValid eb337.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg43⟩

private theorem threshold338 : certThresholdDataValid eb338.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg30⟩

private theorem threshold340 : certThresholdDataValid eb340.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg30⟩

private theorem threshold341 : certThresholdDataValid eb341.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold342 : certThresholdDataValid eb342.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold345 : certThresholdDataValid eb345.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg42⟩

private theorem threshold346 : certThresholdDataValid eb346.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg65⟩

private theorem threshold347 : certThresholdDataValid eb347.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg42⟩

private theorem threshold350 : certThresholdDataValid eb350.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg43⟩

private theorem threshold358 : certThresholdDataValid eb358.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg34⟩

private theorem threshold359 : certThresholdDataValid eb359.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg38⟩

private theorem threshold360 : certThresholdDataValid eb360.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg34⟩

private theorem threshold363 : certThresholdDataValid eb363.threshold := by
  exact ⟨endpointNonneg30, endpointNonneg39⟩

private theorem threshold366 : certThresholdDataValid eb366.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold370 : certThresholdDataValid eb370.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg41⟩

private theorem threshold375 : certThresholdDataValid eb375.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg64⟩

private theorem threshold376 : certThresholdDataValid eb376.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg63⟩

private theorem threshold380 : certThresholdDataValid eb380.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg64⟩

private theorem threshold382 : certThresholdDataValid eb382.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg1⟩

private theorem threshold383 : certThresholdDataValid eb383.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg1⟩

private theorem threshold384 : certThresholdDataValid eb384.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg23⟩

private theorem threshold385 : certThresholdDataValid eb385.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg15⟩

private theorem threshold386 : certThresholdDataValid eb386.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg15⟩

private theorem threshold387 : certThresholdDataValid eb387.threshold := by
  exact ⟨endpointNonneg66, endpointNonneg15⟩

private theorem threshold388 : certThresholdDataValid eb388.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg15⟩

private theorem threshold389 : certThresholdDataValid eb389.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg15⟩

private theorem threshold390 : certThresholdDataValid eb390.threshold := by
  exact ⟨endpointNonneg66, endpointNonneg15⟩

private theorem threshold391 : certThresholdDataValid eb391.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg17⟩

private theorem threshold392 : certThresholdDataValid eb392.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg17⟩

private theorem threshold393 : certThresholdDataValid eb393.threshold := by
  exact ⟨endpointNonneg66, endpointNonneg17⟩

private theorem indexOk2 : 0 < 2 ∧ 2 ≤ 1238 := by norm_num
private theorem indexOk3 : 0 < 3 ∧ 3 ≤ 1238 := by norm_num
private theorem indexOk6 : 0 < 6 ∧ 6 ≤ 1238 := by norm_num
private theorem indexOk7 : 0 < 7 ∧ 7 ≤ 1238 := by norm_num
private theorem indexOk8 : 0 < 8 ∧ 8 ≤ 1238 := by norm_num
private theorem indexOk12 : 0 < 12 ∧ 12 ≤ 1238 := by norm_num
private theorem indexOk13 : 0 < 13 ∧ 13 ≤ 1238 := by norm_num
private theorem indexOk14 : 0 < 14 ∧ 14 ≤ 1238 := by norm_num
private theorem indexOk15 : 0 < 15 ∧ 15 ≤ 1238 := by norm_num
private theorem indexOk23 : 0 < 23 ∧ 23 ≤ 1238 := by norm_num
private theorem indexOk27 : 0 < 27 ∧ 27 ≤ 1238 := by norm_num
private theorem indexOk28 : 0 < 28 ∧ 28 ≤ 1238 := by norm_num
private theorem indexOk33 : 0 < 33 ∧ 33 ≤ 1238 := by norm_num
private theorem indexOk35 : 0 < 35 ∧ 35 ≤ 1238 := by norm_num
private theorem indexOk36 : 0 < 36 ∧ 36 ≤ 1238 := by norm_num
private theorem indexOk39 : 0 < 39 ∧ 39 ≤ 1238 := by norm_num
private theorem indexOk43 : 0 < 43 ∧ 43 ≤ 1238 := by norm_num
private theorem indexOk45 : 0 < 45 ∧ 45 ≤ 1238 := by norm_num
private theorem indexOk50 : 0 < 50 ∧ 50 ≤ 1238 := by norm_num
private theorem indexOk51 : 0 < 51 ∧ 51 ≤ 1238 := by norm_num
private theorem indexOk52 : 0 < 52 ∧ 52 ≤ 1238 := by norm_num
private theorem indexOk53 : 0 < 53 ∧ 53 ≤ 1238 := by norm_num
private theorem indexOk60 : 0 < 60 ∧ 60 ≤ 1238 := by norm_num
private theorem indexOk61 : 0 < 61 ∧ 61 ≤ 1238 := by norm_num
private theorem indexOk66 : 0 < 66 ∧ 66 ≤ 1238 := by norm_num
private theorem indexOk69 : 0 < 69 ∧ 69 ≤ 1238 := by norm_num
private theorem indexOk70 : 0 < 70 ∧ 70 ≤ 1238 := by norm_num
private theorem indexOk71 : 0 < 71 ∧ 71 ≤ 1238 := by norm_num
private theorem indexOk75 : 0 < 75 ∧ 75 ≤ 1238 := by norm_num
private theorem indexOk76 : 0 < 76 ∧ 76 ≤ 1238 := by norm_num
private theorem indexOk84 : 0 < 84 ∧ 84 ≤ 1238 := by norm_num
private theorem indexOk86 : 0 < 86 ∧ 86 ≤ 1238 := by norm_num
private theorem indexOk87 : 0 < 87 ∧ 87 ≤ 1238 := by norm_num
private theorem indexOk90 : 0 < 90 ∧ 90 ≤ 1238 := by norm_num
private theorem indexOk96 : 0 < 96 ∧ 96 ≤ 1238 := by norm_num
private theorem indexOk100 : 0 < 100 ∧ 100 ≤ 1238 := by norm_num
private theorem indexOk101 : 0 < 101 ∧ 101 ≤ 1238 := by norm_num
private theorem indexOk102 : 0 < 102 ∧ 102 ≤ 1238 := by norm_num
private theorem indexOk103 : 0 < 103 ∧ 103 ≤ 1238 := by norm_num
private theorem indexOk105 : 0 < 105 ∧ 105 ≤ 1238 := by norm_num
private theorem indexOk106 : 0 < 106 ∧ 106 ≤ 1238 := by norm_num
private theorem indexOk107 : 0 < 107 ∧ 107 ≤ 1238 := by norm_num
private theorem indexOk109 : 0 < 109 ∧ 109 ≤ 1238 := by norm_num
private theorem indexOk114 : 0 < 114 ∧ 114 ≤ 1238 := by norm_num
private theorem indexOk116 : 0 < 116 ∧ 116 ≤ 1238 := by norm_num
private theorem indexOk118 : 0 < 118 ∧ 118 ≤ 1238 := by norm_num
private theorem indexOk119 : 0 < 119 ∧ 119 ≤ 1238 := by norm_num
private theorem indexOk120 : 0 < 120 ∧ 120 ≤ 1238 := by norm_num
private theorem indexOk121 : 0 < 121 ∧ 121 ≤ 1238 := by norm_num
private theorem indexOk122 : 0 < 122 ∧ 122 ≤ 1238 := by norm_num
private theorem indexOk125 : 0 < 125 ∧ 125 ≤ 1238 := by norm_num
private theorem indexOk127 : 0 < 127 ∧ 127 ≤ 1238 := by norm_num
private theorem indexOk129 : 0 < 129 ∧ 129 ≤ 1238 := by norm_num
private theorem indexOk131 : 0 < 131 ∧ 131 ≤ 1238 := by norm_num
private theorem indexOk134 : 0 < 134 ∧ 134 ≤ 1238 := by norm_num
private theorem indexOk137 : 0 < 137 ∧ 137 ≤ 1238 := by norm_num
private theorem indexOk140 : 0 < 140 ∧ 140 ≤ 1238 := by norm_num
private theorem indexOk141 : 0 < 141 ∧ 141 ≤ 1238 := by norm_num
private theorem indexOk144 : 0 < 144 ∧ 144 ≤ 1238 := by norm_num
private theorem indexOk146 : 0 < 146 ∧ 146 ≤ 1238 := by norm_num
private theorem indexOk147 : 0 < 147 ∧ 147 ≤ 1238 := by norm_num
private theorem indexOk150 : 0 < 150 ∧ 150 ≤ 1238 := by norm_num
private theorem indexOk154 : 0 < 154 ∧ 154 ≤ 1238 := by norm_num
private theorem indexOk159 : 0 < 159 ∧ 159 ≤ 1238 := by norm_num
private theorem indexOk160 : 0 < 160 ∧ 160 ≤ 1238 := by norm_num
private theorem indexOk162 : 0 < 162 ∧ 162 ≤ 1238 := by norm_num
private theorem indexOk163 : 0 < 163 ∧ 163 ≤ 1238 := by norm_num
private theorem indexOk164 : 0 < 164 ∧ 164 ≤ 1238 := by norm_num
private theorem indexOk165 : 0 < 165 ∧ 165 ≤ 1238 := by norm_num
private theorem indexOk171 : 0 < 171 ∧ 171 ≤ 1238 := by norm_num
private theorem indexOk172 : 0 < 172 ∧ 172 ≤ 1238 := by norm_num
private theorem indexOk173 : 0 < 173 ∧ 173 ≤ 1238 := by norm_num
private theorem indexOk174 : 0 < 174 ∧ 174 ≤ 1238 := by norm_num
private theorem indexOk183 : 0 < 183 ∧ 183 ≤ 1238 := by norm_num
private theorem indexOk186 : 0 < 186 ∧ 186 ≤ 1238 := by norm_num
private theorem indexOk187 : 0 < 187 ∧ 187 ≤ 1238 := by norm_num
private theorem indexOk188 : 0 < 188 ∧ 188 ≤ 1238 := by norm_num
private theorem indexOk193 : 0 < 193 ∧ 193 ≤ 1238 := by norm_num
private theorem indexOk197 : 0 < 197 ∧ 197 ≤ 1238 := by norm_num
private theorem indexOk199 : 0 < 199 ∧ 199 ≤ 1238 := by norm_num
private theorem indexOk203 : 0 < 203 ∧ 203 ≤ 1238 := by norm_num
private theorem indexOk207 : 0 < 207 ∧ 207 ≤ 1238 := by norm_num
private theorem indexOk208 : 0 < 208 ∧ 208 ≤ 1238 := by norm_num
private theorem indexOk214 : 0 < 214 ∧ 214 ≤ 1238 := by norm_num
private theorem indexOk215 : 0 < 215 ∧ 215 ≤ 1238 := by norm_num
private theorem indexOk216 : 0 < 216 ∧ 216 ≤ 1238 := by norm_num
private theorem indexOk217 : 0 < 217 ∧ 217 ≤ 1238 := by norm_num
private theorem indexOk223 : 0 < 223 ∧ 223 ≤ 1238 := by norm_num
private theorem indexOk226 : 0 < 226 ∧ 226 ≤ 1238 := by norm_num
private theorem indexOk229 : 0 < 229 ∧ 229 ≤ 1238 := by norm_num
private theorem indexOk230 : 0 < 230 ∧ 230 ≤ 1238 := by norm_num
private theorem indexOk231 : 0 < 231 ∧ 231 ≤ 1238 := by norm_num
private theorem indexOk235 : 0 < 235 ∧ 235 ≤ 1238 := by norm_num
private theorem indexOk236 : 0 < 236 ∧ 236 ≤ 1238 := by norm_num
private theorem indexOk241 : 0 < 241 ∧ 241 ≤ 1238 := by norm_num
private theorem indexOk243 : 0 < 243 ∧ 243 ≤ 1238 := by norm_num
private theorem indexOk245 : 0 < 245 ∧ 245 ≤ 1238 := by norm_num
private theorem indexOk247 : 0 < 247 ∧ 247 ≤ 1238 := by norm_num
private theorem indexOk251 : 0 < 251 ∧ 251 ≤ 1238 := by norm_num
private theorem indexOk252 : 0 < 252 ∧ 252 ≤ 1238 := by norm_num
private theorem indexOk257 : 0 < 257 ∧ 257 ≤ 1238 := by norm_num
private theorem indexOk258 : 0 < 258 ∧ 258 ≤ 1238 := by norm_num
private theorem indexOk259 : 0 < 259 ∧ 259 ≤ 1238 := by norm_num
private theorem indexOk260 : 0 < 260 ∧ 260 ≤ 1238 := by norm_num
private theorem indexOk261 : 0 < 261 ∧ 261 ≤ 1238 := by norm_num
private theorem indexOk268 : 0 < 268 ∧ 268 ≤ 1238 := by norm_num
private theorem indexOk272 : 0 < 272 ∧ 272 ≤ 1238 := by norm_num
private theorem indexOk280 : 0 < 280 ∧ 280 ≤ 1238 := by norm_num
private theorem indexOk282 : 0 < 282 ∧ 282 ≤ 1238 := by norm_num
private theorem indexOk283 : 0 < 283 ∧ 283 ≤ 1238 := by norm_num
private theorem indexOk286 : 0 < 286 ∧ 286 ≤ 1238 := by norm_num
private theorem indexOk292 : 0 < 292 ∧ 292 ≤ 1238 := by norm_num
private theorem indexOk296 : 0 < 296 ∧ 296 ≤ 1238 := by norm_num
private theorem indexOk297 : 0 < 297 ∧ 297 ≤ 1238 := by norm_num
private theorem indexOk298 : 0 < 298 ∧ 298 ≤ 1238 := by norm_num
private theorem indexOk299 : 0 < 299 ∧ 299 ≤ 1238 := by norm_num
private theorem indexOk300 : 0 < 300 ∧ 300 ≤ 1238 := by norm_num
private theorem indexOk301 : 0 < 301 ∧ 301 ≤ 1238 := by norm_num
private theorem indexOk308 : 0 < 308 ∧ 308 ≤ 1238 := by norm_num
private theorem indexOk312 : 0 < 312 ∧ 312 ≤ 1238 := by norm_num
private theorem indexOk318 : 0 < 318 ∧ 318 ≤ 1238 := by norm_num
private theorem indexOk320 : 0 < 320 ∧ 320 ≤ 1238 := by norm_num
private theorem indexOk321 : 0 < 321 ∧ 321 ≤ 1238 := by norm_num
private theorem indexOk324 : 0 < 324 ∧ 324 ≤ 1238 := by norm_num
private theorem indexOk325 : 0 < 325 ∧ 325 ≤ 1238 := by norm_num
private theorem indexOk327 : 0 < 327 ∧ 327 ≤ 1238 := by norm_num
private theorem indexOk328 : 0 < 328 ∧ 328 ≤ 1238 := by norm_num
private theorem indexOk329 : 0 < 329 ∧ 329 ≤ 1238 := by norm_num
private theorem indexOk331 : 0 < 331 ∧ 331 ≤ 1238 := by norm_num
private theorem indexOk332 : 0 < 332 ∧ 332 ≤ 1238 := by norm_num
private theorem indexOk333 : 0 < 333 ∧ 333 ≤ 1238 := by norm_num
private theorem indexOk334 : 0 < 334 ∧ 334 ≤ 1238 := by norm_num
private theorem indexOk335 : 0 < 335 ∧ 335 ≤ 1238 := by norm_num
private theorem indexOk336 : 0 < 336 ∧ 336 ≤ 1238 := by norm_num
private theorem indexOk337 : 0 < 337 ∧ 337 ≤ 1238 := by norm_num
private theorem indexOk338 : 0 < 338 ∧ 338 ≤ 1238 := by norm_num
private theorem indexOk340 : 0 < 340 ∧ 340 ≤ 1238 := by norm_num
private theorem indexOk341 : 0 < 341 ∧ 341 ≤ 1238 := by norm_num
private theorem indexOk342 : 0 < 342 ∧ 342 ≤ 1238 := by norm_num
private theorem indexOk345 : 0 < 345 ∧ 345 ≤ 1238 := by norm_num
private theorem indexOk346 : 0 < 346 ∧ 346 ≤ 1238 := by norm_num
private theorem indexOk347 : 0 < 347 ∧ 347 ≤ 1238 := by norm_num
private theorem indexOk350 : 0 < 350 ∧ 350 ≤ 1238 := by norm_num
private theorem indexOk358 : 0 < 358 ∧ 358 ≤ 1238 := by norm_num
private theorem indexOk359 : 0 < 359 ∧ 359 ≤ 1238 := by norm_num
private theorem indexOk360 : 0 < 360 ∧ 360 ≤ 1238 := by norm_num
private theorem indexOk363 : 0 < 363 ∧ 363 ≤ 1238 := by norm_num
private theorem indexOk366 : 0 < 366 ∧ 366 ≤ 1238 := by norm_num
private theorem indexOk370 : 0 < 370 ∧ 370 ≤ 1238 := by norm_num
private theorem indexOk375 : 0 < 375 ∧ 375 ≤ 1238 := by norm_num
private theorem indexOk376 : 0 < 376 ∧ 376 ≤ 1238 := by norm_num
private theorem indexOk380 : 0 < 380 ∧ 380 ≤ 1238 := by norm_num
private theorem indexOk382 : 0 < 382 ∧ 382 ≤ 1238 := by norm_num
private theorem indexOk383 : 0 < 383 ∧ 383 ≤ 1238 := by norm_num
private theorem indexOk384 : 0 < 384 ∧ 384 ≤ 1238 := by norm_num
private theorem indexOk385 : 0 < 385 ∧ 385 ≤ 1238 := by norm_num
private theorem indexOk386 : 0 < 386 ∧ 386 ≤ 1238 := by norm_num
private theorem indexOk387 : 0 < 387 ∧ 387 ≤ 1238 := by norm_num
private theorem indexOk388 : 0 < 388 ∧ 388 ≤ 1238 := by norm_num
private theorem indexOk389 : 0 < 389 ∧ 389 ≤ 1238 := by norm_num
private theorem indexOk390 : 0 < 390 ∧ 390 ≤ 1238 := by norm_num
private theorem indexOk391 : 0 < 391 ∧ 391 ≤ 1238 := by norm_num
private theorem indexOk392 : 0 < 392 ∧ 392 ≤ 1238 := by norm_num
private theorem indexOk393 : 0 < 393 ∧ 393 ≤ 1238 := by norm_num

private theorem explicit_pair_valid (lid uid : ℕ) (q : ℚ) (l u : CertBound)
    (hlid : 0 < lid) (hlength : lid ≤ 1238)
    (huid : 0 < uid) (hulength : uid ≤ 1238)
    (hl : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 lid = l)
    (hu : lowerEarlyTerminalBound lowerEarlyTerminalEarly3 uid = u)
    (hll : l.lower = true) (hul : u.lower = false)
    (hlt : certThresholdDataValid l.threshold)
    (hut : certThresholdDataValid u.threshold)
    (hc : ∀ i j : Fin 3, certCoefficientBoundValid
      ((certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) earlyRect) i j) q)
    (hq : 0 < q) :
    lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ⟨lid,uid,q⟩ := by
  unfold lowerEarlyTerminalPairValid
  refine ⟨hlid, ?_, huid, ?_, ?_⟩
  · rw [bounds_length]
    exact hlength
  · rw [bounds_length]
    exact hulength
  · unfold lowerEarlyTerminalWitness
    rw [hl, hu]
    change certWitnessValid
      ⟨l,u,earlyRect,
        certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) earlyRect,
        fun _ _ => q⟩
    refine ⟨hll,hul,?_,?_,hlt,hut,rfl,hc,?_⟩
    · change certRectangleValid earlyRect
      norm_num [earlyRect, certRectangleValid]
    · change 0 ≤ earlyRect.r0
      norm_num [earlyRect]
    exact Or.inl (fun _ _ => hq)

end Blockers16Early3Data
open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs01
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep001 : LowerEarlyTerminalPair := ⟨2,6,(2928212403258624942694992846548610581797/6710146150400000000000000000000000000000)⟩
private theorem coeff001 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb6.threshold) earlyRect) i j)
      ep001.coefficientLower) ∧ 0 < ep001.coefficientLower := by
  have hq : 0 < ep001.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid001 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep001 := by
  apply explicit_pair_valid 2 6 ep001.coefficientLower eb2 eb6
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk6.1
  · exact indexOk6.2
  · exact lookup2
  · exact lookup6
  · rfl
  · rfl
  · exact threshold2
  · exact threshold6
  · exact coeff001.1
  · exact coeff001.2

private def ep002 : LowerEarlyTerminalPair := ⟨13,6,(436692971348431206908120374871147108475119/523199320140000000000000000000000000000000)⟩
private theorem coeff002 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb13.threshold eb6.threshold) earlyRect) i j)
      ep002.coefficientLower) ∧ 0 < ep002.coefficientLower := by
  have hq : 0 < ep002.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid002 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep002 := by
  apply explicit_pair_valid 13 6 ep002.coefficientLower eb13 eb6
  · exact indexOk13.1
  · exact indexOk13.2
  · exact indexOk6.1
  · exact indexOk6.2
  · exact lookup13
  · exact lookup6
  · rfl
  · rfl
  · exact threshold13
  · exact threshold6
  · exact coeff002.1
  · exact coeff002.2

private def ep003 : LowerEarlyTerminalPair := ⟨14,6,(33308652346594597778546715392745177608691/59065199513600000000000000000000000000000)⟩
private theorem coeff003 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb14.threshold eb6.threshold) earlyRect) i j)
      ep003.coefficientLower) ∧ 0 < ep003.coefficientLower := by
  have hq : 0 < ep003.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid003 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep003 := by
  apply explicit_pair_valid 14 6 ep003.coefficientLower eb14 eb6
  · exact indexOk14.1
  · exact indexOk14.2
  · exact indexOk6.1
  · exact indexOk6.2
  · exact lookup14
  · exact lookup6
  · rfl
  · rfl
  · exact threshold14
  · exact threshold6
  · exact coeff003.1
  · exact coeff003.2

private def ep004 : LowerEarlyTerminalPair := ⟨2,8,(215930956543442798296266740876569951627/652783718400000000000000000000000000000)⟩
private theorem coeff004 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb8.threshold) earlyRect) i j)
      ep004.coefficientLower) ∧ 0 < ep004.coefficientLower := by
  have hq : 0 < ep004.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid004 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep004 := by
  apply explicit_pair_valid 2 8 ep004.coefficientLower eb2 eb8
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk8.1
  · exact indexOk8.2
  · exact lookup2
  · exact lookup8
  · rfl
  · rfl
  · exact threshold2
  · exact threshold8
  · exact coeff004.1
  · exact coeff004.2

private def ep005 : LowerEarlyTerminalPair := ⟨13,8,(6155894580858887234483439363750734408813/8483073990000000000000000000000000000000)⟩
private theorem coeff005 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb13.threshold eb8.threshold) earlyRect) i j)
      ep005.coefficientLower) ∧ 0 < ep005.coefficientLower := by
  have hq : 0 < ep005.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid005 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep005 := by
  apply explicit_pair_valid 13 8 ep005.coefficientLower eb13 eb8
  · exact indexOk13.1
  · exact indexOk13.2
  · exact indexOk8.1
  · exact indexOk8.2
  · exact lookup13
  · exact lookup8
  · rfl
  · rfl
  · exact threshold13
  · exact threshold8
  · exact coeff005.1
  · exact coeff005.2

private def ep006 : LowerEarlyTerminalPair := ⟨14,8,(3267632754905348990392880867145768993151/7182556032000000000000000000000000000000)⟩
private theorem coeff006 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb14.threshold eb8.threshold) earlyRect) i j)
      ep006.coefficientLower) ∧ 0 < ep006.coefficientLower := by
  have hq : 0 < ep006.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid006 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep006 := by
  apply explicit_pair_valid 14 8 ep006.coefficientLower eb14 eb8
  · exact indexOk14.1
  · exact indexOk14.2
  · exact indexOk8.1
  · exact indexOk8.2
  · exact lookup14
  · exact lookup8
  · rfl
  · rfl
  · exact threshold14
  · exact threshold8
  · exact coeff006.1
  · exact coeff006.2

private def ep007 : LowerEarlyTerminalPair := ⟨2,7,(1460730671240061402614327879300130630393/6701998336000000000000000000000000000000)⟩
private theorem coeff007 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb7.threshold) earlyRect) i j)
      ep007.coefficientLower) ∧ 0 < ep007.coefficientLower := by
  have hq : 0 < ep007.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid007 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep007 := by
  apply explicit_pair_valid 2 7 ep007.coefficientLower eb2 eb7
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk7.1
  · exact indexOk7.2
  · exact lookup2
  · exact lookup7
  · rfl
  · rfl
  · exact threshold2
  · exact threshold7
  · exact coeff007.1
  · exact coeff007.2

private def ep008 : LowerEarlyTerminalPair := ⟨2,12,(1408850175438915414383676574385105874921/7920543488000000000000000000000000000000)⟩
private theorem coeff008 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb12.threshold) earlyRect) i j)
      ep008.coefficientLower) ∧ 0 < ep008.coefficientLower := by
  have hq : 0 < ep008.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid008 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep008 := by
  apply explicit_pair_valid 2 12 ep008.coefficientLower eb2 eb12
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk12.1
  · exact indexOk12.2
  · exact lookup2
  · exact lookup12
  · rfl
  · rfl
  · exact threshold2
  · exact threshold12
  · exact coeff008.1
  · exact coeff008.2

private def ep009 : LowerEarlyTerminalPair := ⟨13,7,(1876647347216724461744473929299481050070630401/3076856972428800000000000000000000000000000000)⟩
private theorem coeff009 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb13.threshold eb7.threshold) earlyRect) i j)
      ep009.coefficientLower) ∧ 0 < ep009.coefficientLower := by
  have hq : 0 < ep009.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid009 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep009 := by
  apply explicit_pair_valid 13 7 ep009.coefficientLower eb13 eb7
  · exact indexOk13.1
  · exact indexOk13.2
  · exact indexOk7.1
  · exact indexOk7.2
  · exact lookup13
  · exact lookup7
  · rfl
  · rfl
  · exact threshold13
  · exact threshold7
  · exact coeff009.1
  · exact coeff009.2

private def ep010 : LowerEarlyTerminalPair := ⟨14,15,(56421873395429461667100172900863088976699/204742075648000000000000000000000000000000)⟩
private theorem coeff010 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb14.threshold eb15.threshold) earlyRect) i j)
      ep010.coefficientLower) ∧ 0 < ep010.coefficientLower := by
  have hq : 0 < ep010.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid010 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep010 := by
  apply explicit_pair_valid 14 15 ep010.coefficientLower eb14 eb15
  · exact indexOk14.1
  · exact indexOk14.2
  · exact indexOk15.1
  · exact indexOk15.2
  · exact lookup14
  · exact lookup15
  · rfl
  · rfl
  · exact threshold14
  · exact threshold15
  · exact coeff010.1
  · exact coeff010.2

private def ep011 : LowerEarlyTerminalPair := ⟨2,23,(5215722255226578416462035656653147228363/23964807680000000000000000000000000000000)⟩
private theorem coeff011 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb23.threshold) earlyRect) i j)
      ep011.coefficientLower) ∧ 0 < ep011.coefficientLower := by
  have hq : 0 < ep011.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid011 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep011 := by
  apply explicit_pair_valid 2 23 ep011.coefficientLower eb2 eb23
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk23.1
  · exact indexOk23.2
  · exact lookup2
  · exact lookup23
  · rfl
  · rfl
  · exact threshold2
  · exact threshold23
  · exact coeff011.1
  · exact coeff011.2

private def ep012 : LowerEarlyTerminalPair := ⟨13,23,(45540578493512767603784052906741058072973/74742760020000000000000000000000000000000)⟩
private theorem coeff012 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb13.threshold eb23.threshold) earlyRect) i j)
      ep012.coefficientLower) ∧ 0 < ep012.coefficientLower := by
  have hq : 0 < ep012.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid012 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep012 := by
  apply explicit_pair_valid 13 23 ep012.coefficientLower eb13 eb23
  · exact indexOk13.1
  · exact indexOk13.2
  · exact indexOk23.1
  · exact indexOk23.2
  · exact lookup13
  · exact lookup23
  · rfl
  · rfl
  · exact threshold13
  · exact threshold23
  · exact coeff012.1
  · exact coeff012.2

end EarlyCompact16Pairs01

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs02
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep013 : LowerEarlyTerminalPair := ⟨14,23,(71360203306827825114020361984601463738713/210947141120000000000000000000000000000000)⟩
private theorem coeff013 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb14.threshold eb23.threshold) earlyRect) i j)
      ep013.coefficientLower) ∧ 0 < ep013.coefficientLower := by
  have hq : 0 < ep013.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid013 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep013 := by
  apply explicit_pair_valid 14 23 ep013.coefficientLower eb14 eb23
  · exact indexOk14.1
  · exact indexOk14.2
  · exact indexOk23.1
  · exact indexOk23.2
  · exact lookup14
  · exact lookup23
  · rfl
  · rfl
  · exact threshold14
  · exact threshold23
  · exact coeff013.1
  · exact coeff013.2

private def ep014 : LowerEarlyTerminalPair := ⟨28,3,(195741069668543769267249795431486435948539/25641651200000000000000000000000000000000)⟩
private theorem coeff014 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb28.threshold eb3.threshold) earlyRect) i j)
      ep014.coefficientLower) ∧ 0 < ep014.coefficientLower := by
  have hq : 0 < ep014.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid014 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep014 := by
  apply explicit_pair_valid 28 3 ep014.coefficientLower eb28 eb3
  · exact indexOk28.1
  · exact indexOk28.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup28
  · exact lookup3
  · rfl
  · rfl
  · exact threshold28
  · exact threshold3
  · exact coeff014.1
  · exact coeff014.2

private def ep015 : LowerEarlyTerminalPair := ⟨33,3,(465208465286808344465813201080344505263164031/65197310464000000000000000000000000000000000)⟩
private theorem coeff015 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb33.threshold eb3.threshold) earlyRect) i j)
      ep015.coefficientLower) ∧ 0 < ep015.coefficientLower := by
  have hq : 0 < ep015.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid015 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep015 := by
  apply explicit_pair_valid 33 3 ep015.coefficientLower eb33 eb3
  · exact indexOk33.1
  · exact indexOk33.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup33
  · exact lookup3
  · rfl
  · rfl
  · exact threshold33
  · exact threshold3
  · exact coeff015.1
  · exact coeff015.2

private def ep016 : LowerEarlyTerminalPair := ⟨35,3,(959037679108933808557389908989628243863589631/65197310464000000000000000000000000000000000)⟩
private theorem coeff016 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb35.threshold eb3.threshold) earlyRect) i j)
      ep016.coefficientLower) ∧ 0 < ep016.coefficientLower := by
  have hq : 0 < ep016.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid016 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep016 := by
  apply explicit_pair_valid 35 3 ep016.coefficientLower eb35 eb3
  · exact indexOk35.1
  · exact indexOk35.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup35
  · exact lookup3
  · rfl
  · rfl
  · exact threshold35
  · exact threshold3
  · exact coeff016.1
  · exact coeff016.2

private def ep017 : LowerEarlyTerminalPair := ⟨36,3,(1489579635608063508091358829463236917548317/145243648000000000000000000000000000000000)⟩
private theorem coeff017 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb36.threshold eb3.threshold) earlyRect) i j)
      ep017.coefficientLower) ∧ 0 < ep017.coefficientLower := by
  have hq : 0 < ep017.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid017 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep017 := by
  apply explicit_pair_valid 36 3 ep017.coefficientLower eb36 eb3
  · exact indexOk36.1
  · exact indexOk36.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup36
  · exact lookup3
  · rfl
  · rfl
  · exact threshold36
  · exact threshold3
  · exact coeff017.1
  · exact coeff017.2

private def ep018 : LowerEarlyTerminalPair := ⟨39,3,(6676866649711639620508535284041636279982687/1006434809600000000000000000000000000000000)⟩
private theorem coeff018 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb39.threshold eb3.threshold) earlyRect) i j)
      ep018.coefficientLower) ∧ 0 < ep018.coefficientLower := by
  have hq : 0 < ep018.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid018 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep018 := by
  apply explicit_pair_valid 39 3 ep018.coefficientLower eb39 eb3
  · exact indexOk39.1
  · exact indexOk39.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup39
  · exact lookup3
  · rfl
  · rfl
  · exact threshold39
  · exact threshold3
  · exact coeff018.1
  · exact coeff018.2

private def ep019 : LowerEarlyTerminalPair := ⟨45,3,(433770549830828952171707174584030234806407/62786099200000000000000000000000000000000)⟩
private theorem coeff019 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb45.threshold eb3.threshold) earlyRect) i j)
      ep019.coefficientLower) ∧ 0 < ep019.coefficientLower := by
  have hq : 0 < ep019.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid019 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep019 := by
  apply explicit_pair_valid 45 3 ep019.coefficientLower eb45 eb3
  · exact indexOk45.1
  · exact indexOk45.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup45
  · exact lookup3
  · rfl
  · rfl
  · exact threshold45
  · exact threshold3
  · exact coeff019.1
  · exact coeff019.2

private def ep020 : LowerEarlyTerminalPair := ⟨2,50,(148577438259311005476402374988262695421/317775360000000000000000000000000000000)⟩
private theorem coeff020 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb50.threshold) earlyRect) i j)
      ep020.coefficientLower) ∧ 0 < ep020.coefficientLower := by
  have hq : 0 < ep020.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid020 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep020 := by
  apply explicit_pair_valid 2 50 ep020.coefficientLower eb2 eb50
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk50.1
  · exact indexOk50.2
  · exact lookup2
  · exact lookup50
  · rfl
  · rfl
  · exact threshold2
  · exact threshold50
  · exact coeff020.1
  · exact coeff020.2

private def ep021 : LowerEarlyTerminalPair := ⟨2,52,(346394384527457846031598837086547188329/865430016000000000000000000000000000000)⟩
private theorem coeff021 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb52.threshold) earlyRect) i j)
      ep021.coefficientLower) ∧ 0 < ep021.coefficientLower := by
  have hq : 0 < ep021.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid021 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep021 := by
  apply explicit_pair_valid 2 52 ep021.coefficientLower eb2 eb52
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk52.1
  · exact indexOk52.2
  · exact lookup2
  · exact lookup52
  · rfl
  · rfl
  · exact threshold2
  · exact threshold52
  · exact coeff021.1
  · exact coeff021.2

private def ep022 : LowerEarlyTerminalPair := ⟨2,53,(1177345535090819927954504817368888637511/3263918592000000000000000000000000000000)⟩
private theorem coeff022 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb53.threshold) earlyRect) i j)
      ep022.coefficientLower) ∧ 0 < ep022.coefficientLower := by
  have hq : 0 < ep022.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid022 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep022 := by
  apply explicit_pair_valid 2 53 ep022.coefficientLower eb2 eb53
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk53.1
  · exact indexOk53.2
  · exact lookup2
  · exact lookup53
  · rfl
  · rfl
  · exact threshold2
  · exact threshold53
  · exact coeff022.1
  · exact coeff022.2

private def ep023 : LowerEarlyTerminalPair := ⟨61,53,(991347048194472320209557238828388065933/2394185344000000000000000000000000000000)⟩
private theorem coeff023 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb61.threshold eb53.threshold) earlyRect) i j)
      ep023.coefficientLower) ∧ 0 < ep023.coefficientLower := by
  have hq : 0 < ep023.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid023 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep023 := by
  apply explicit_pair_valid 61 53 ep023.coefficientLower eb61 eb53
  · exact indexOk61.1
  · exact indexOk61.2
  · exact indexOk53.1
  · exact indexOk53.2
  · exact lookup61
  · exact lookup53
  · rfl
  · rfl
  · exact threshold61
  · exact threshold53
  · exact coeff023.1
  · exact coeff023.2

private def ep024 : LowerEarlyTerminalPair := ⟨2,51,(1730400367660396635352859604546772112841/6701998336000000000000000000000000000000)⟩
private theorem coeff024 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb51.threshold) earlyRect) i j)
      ep024.coefficientLower) ∧ 0 < ep024.coefficientLower := by
  have hq : 0 < ep024.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid024 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep024 := by
  apply explicit_pair_valid 2 51 ep024.coefficientLower eb2 eb51
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk51.1
  · exact indexOk51.2
  · exact lookup2
  · exact lookup51
  · rfl
  · rfl
  · exact threshold2
  · exact threshold51
  · exact coeff024.1
  · exact coeff024.2

end EarlyCompact16Pairs02

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs03
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep025 : LowerEarlyTerminalPair := ⟨2,60,(90840753033815376653444180628894257375639/327081638400000000000000000000000000000000)⟩
private theorem coeff025 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb60.threshold) earlyRect) i j)
      ep025.coefficientLower) ∧ 0 < ep025.coefficientLower := by
  have hq : 0 < ep025.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid025 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep025 := by
  apply explicit_pair_valid 2 60 ep025.coefficientLower eb2 eb60
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk60.1
  · exact indexOk60.2
  · exact lookup2
  · exact lookup60
  · rfl
  · rfl
  · exact threshold2
  · exact threshold60
  · exact coeff025.1
  · exact coeff025.2

private def ep026 : LowerEarlyTerminalPair := ⟨61,51,(334719655802161774404539156284334746788401/1085480021401600000000000000000000000000000)⟩
private theorem coeff026 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb61.threshold eb51.threshold) earlyRect) i j)
      ep026.coefficientLower) ∧ 0 < ep026.coefficientLower := by
  have hq : 0 < ep026.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid026 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep026 := by
  apply explicit_pair_valid 61 51 ep026.coefficientLower eb61 eb51
  · exact indexOk61.1
  · exact indexOk61.2
  · exact indexOk51.1
  · exact indexOk51.2
  · exact lookup61
  · exact lookup51
  · rfl
  · rfl
  · exact threshold61
  · exact threshold51
  · exact coeff026.1
  · exact coeff026.2

private def ep027 : LowerEarlyTerminalPair := ⟨2,66,(348944144061210691847304969011086415773/1584108697600000000000000000000000000000)⟩
private theorem coeff027 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb66.threshold) earlyRect) i j)
      ep027.coefficientLower) ∧ 0 < ep027.coefficientLower := by
  have hq : 0 < ep027.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid027 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep027 := by
  apply explicit_pair_valid 2 66 ep027.coefficientLower eb2 eb66
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk66.1
  · exact indexOk66.2
  · exact lookup2
  · exact lookup66
  · rfl
  · rfl
  · exact threshold2
  · exact threshold66
  · exact coeff027.1
  · exact coeff027.2

private def ep028 : LowerEarlyTerminalPair := ⟨61,66,(3454061073356242065932576940833141098776623/12828400252928000000000000000000000000000000)⟩
private theorem coeff028 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb61.threshold eb66.threshold) earlyRect) i j)
      ep028.coefficientLower) ∧ 0 < ep028.coefficientLower := by
  have hq : 0 < ep028.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid028 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep028 := by
  apply explicit_pair_valid 61 66 ep028.coefficientLower eb61 eb66
  · exact indexOk61.1
  · exact indexOk61.2
  · exact indexOk66.1
  · exact indexOk66.2
  · exact lookup61
  · exact lookup66
  · rfl
  · rfl
  · exact threshold61
  · exact threshold66
  · exact coeff028.1
  · exact coeff028.2

private def ep029 : LowerEarlyTerminalPair := ⟨69,50,(284877111728192585766484501683774484683717/348799546760000000000000000000000000000000)⟩
private theorem coeff029 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb69.threshold eb50.threshold) earlyRect) i j)
      ep029.coefficientLower) ∧ 0 < ep029.coefficientLower := by
  have hq : 0 < ep029.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid029 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep029 := by
  apply explicit_pair_valid 69 50 ep029.coefficientLower eb69 eb50
  · exact indexOk69.1
  · exact indexOk69.2
  · exact indexOk50.1
  · exact indexOk50.2
  · exact lookup69
  · exact lookup50
  · rfl
  · rfl
  · exact threshold69
  · exact threshold50
  · exact coeff029.1
  · exact coeff029.2

private def ep030 : LowerEarlyTerminalPair := ⟨69,52,(12321613067848710274416697360396831172639/16480245400000000000000000000000000000000)⟩
private theorem coeff030 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb69.threshold eb52.threshold) earlyRect) i j)
      ep030.coefficientLower) ∧ 0 < ep030.coefficientLower := by
  have hq : 0 < ep030.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid030 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep030 := by
  apply explicit_pair_valid 69 52 ep030.coefficientLower eb69 eb52
  · exact indexOk69.1
  · exact indexOk69.2
  · exact indexOk52.1
  · exact indexOk52.2
  · exact lookup69
  · exact lookup52
  · rfl
  · rfl
  · exact threshold69
  · exact threshold52
  · exact coeff030.1
  · exact coeff030.2

private def ep031 : LowerEarlyTerminalPair := ⟨69,51,(73916515998891110439820934214071771575557223/122965606824960000000000000000000000000000000)⟩
private theorem coeff031 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb69.threshold eb51.threshold) earlyRect) i j)
      ep031.coefficientLower) ∧ 0 < ep031.coefficientLower := by
  have hq : 0 < ep031.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid031 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep031 := by
  apply explicit_pair_valid 69 51 ep031.coefficientLower eb69 eb51
  · exact indexOk69.1
  · exact indexOk69.2
  · exact indexOk51.1
  · exact indexOk51.2
  · exact lookup69
  · exact lookup51
  · rfl
  · rfl
  · exact threshold69
  · exact threshold51
  · exact coeff031.1
  · exact coeff031.2

private def ep032 : LowerEarlyTerminalPair := ⟨69,60,(6193454113490775494956861363315246790671/9965701336000000000000000000000000000000)⟩
private theorem coeff032 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb69.threshold eb60.threshold) earlyRect) i j)
      ep032.coefficientLower) ∧ 0 < ep032.coefficientLower := by
  have hq : 0 < ep032.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid032 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep032 := by
  apply explicit_pair_valid 69 60 ep032.coefficientLower eb69 eb60
  · exact indexOk69.1
  · exact indexOk69.2
  · exact indexOk60.1
  · exact indexOk60.2
  · exact lookup69
  · exact lookup60
  · rfl
  · rfl
  · exact threshold69
  · exact threshold60
  · exact coeff032.1
  · exact coeff032.2

private def ep033 : LowerEarlyTerminalPair := ⟨70,50,(46406150143795884379959190859794520890703/79175357240000000000000000000000000000000)⟩
private theorem coeff033 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb70.threshold eb50.threshold) earlyRect) i j)
      ep033.coefficientLower) ∧ 0 < ep033.coefficientLower := by
  have hq : 0 < ep033.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid033 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep033 := by
  apply explicit_pair_valid 70 50 ep033.coefficientLower eb70 eb50
  · exact indexOk70.1
  · exact indexOk70.2
  · exact indexOk50.1
  · exact indexOk50.2
  · exact lookup70
  · exact lookup50
  · rfl
  · rfl
  · exact threshold70
  · exact threshold50
  · exact coeff033.1
  · exact coeff033.2

private def ep034 : LowerEarlyTerminalPair := ⟨70,52,(1160376888618846872363490886639580937899/2244548760000000000000000000000000000000)⟩
private theorem coeff034 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb70.threshold eb52.threshold) earlyRect) i j)
      ep034.coefficientLower) ∧ 0 < ep034.coefficientLower := by
  have hq : 0 < ep034.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid034 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep034 := by
  apply explicit_pair_valid 70 52 ep034.coefficientLower eb70 eb52
  · exact indexOk70.1
  · exact indexOk70.2
  · exact indexOk52.1
  · exact indexOk52.2
  · exact lookup70
  · exact lookup52
  · rfl
  · rfl
  · exact threshold70
  · exact threshold52
  · exact coeff034.1
  · exact coeff034.2

private def ep035 : LowerEarlyTerminalPair := ⟨70,71,(56088711009610592664189240443377308918966589/182120129596416000000000000000000000000000000)⟩
private theorem coeff035 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb70.threshold eb71.threshold) earlyRect) i j)
      ep035.coefficientLower) ∧ 0 < ep035.coefficientLower := by
  have hq : 0 < ep035.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid035 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep035 := by
  apply explicit_pair_valid 70 71 ep035.coefficientLower eb70 eb71
  · exact indexOk70.1
  · exact indexOk70.2
  · exact indexOk71.1
  · exact indexOk71.2
  · exact lookup70
  · exact lookup71
  · rfl
  · rfl
  · exact threshold70
  · exact threshold71
  · exact coeff035.1
  · exact coeff035.2

private def ep036 : LowerEarlyTerminalPair := ⟨70,60,(884409156871434353607786504570043994909/2262153064000000000000000000000000000000)⟩
private theorem coeff036 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb70.threshold eb60.threshold) earlyRect) i j)
      ep036.coefficientLower) ∧ 0 < ep036.coefficientLower := by
  have hq : 0 < ep036.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid036 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep036 := by
  apply explicit_pair_valid 70 60 ep036.coefficientLower eb70 eb60
  · exact indexOk70.1
  · exact indexOk70.2
  · exact indexOk60.1
  · exact indexOk60.2
  · exact lookup70
  · exact lookup60
  · rfl
  · rfl
  · exact threshold70
  · exact threshold60
  · exact coeff036.1
  · exact coeff036.2

end EarlyCompact16Pairs03

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs04
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep037 : LowerEarlyTerminalPair := ⟨76,3,(176453281172359688845023582896665520941539/25641651200000000000000000000000000000000)⟩
private theorem coeff037 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb76.threshold eb3.threshold) earlyRect) i j)
      ep037.coefficientLower) ∧ 0 < ep037.coefficientLower := by
  have hq : 0 < ep037.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid037 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep037 := by
  apply explicit_pair_valid 76 3 ep037.coefficientLower eb76 eb3
  · exact indexOk76.1
  · exact indexOk76.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup76
  · exact lookup3
  · rfl
  · rfl
  · exact threshold76
  · exact threshold3
  · exact coeff037.1
  · exact coeff037.2

private def ep038 : LowerEarlyTerminalPair := ⟨84,3,(93624053515654058857417155767980485322470927/13039462092800000000000000000000000000000000)⟩
private theorem coeff038 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb84.threshold eb3.threshold) earlyRect) i j)
      ep038.coefficientLower) ∧ 0 < ep038.coefficientLower := by
  have hq : 0 < ep038.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid038 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep038 := by
  apply explicit_pair_valid 84 3 ep038.coefficientLower eb84 eb3
  · exact indexOk84.1
  · exact indexOk84.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup84
  · exact lookup3
  · rfl
  · rfl
  · exact threshold84
  · exact threshold3
  · exact coeff038.1
  · exact coeff038.2

private def ep039 : LowerEarlyTerminalPair := ⟨86,3,(192948962320039846041416832279672320539067247/13039462092800000000000000000000000000000000)⟩
private theorem coeff039 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb86.threshold eb3.threshold) earlyRect) i j)
      ep039.coefficientLower) ∧ 0 < ep039.coefficientLower := by
  have hq : 0 < ep039.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid039 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep039 := by
  apply explicit_pair_valid 86 3 ep039.coefficientLower eb86 eb3
  · exact indexOk86.1
  · exact indexOk86.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup86
  · exact lookup3
  · rfl
  · rfl
  · exact threshold86
  · exact threshold3
  · exact coeff039.1
  · exact coeff039.2

private def ep040 : LowerEarlyTerminalPair := ⟨87,3,(5197754484616301233098494688238092149095557/472041856000000000000000000000000000000000)⟩
private theorem coeff040 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb87.threshold eb3.threshold) earlyRect) i j)
      ep040.coefficientLower) ∧ 0 < ep040.coefficientLower := by
  have hq : 0 < ep040.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid040 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep040 := by
  apply explicit_pair_valid 87 3 ep040.coefficientLower eb87 eb3
  · exact indexOk87.1
  · exact indexOk87.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup87
  · exact lookup3
  · rfl
  · rfl
  · exact threshold87
  · exact threshold3
  · exact coeff040.1
  · exact coeff040.2

private def ep041 : LowerEarlyTerminalPair := ⟨90,3,(23677672765505588797915008475528531124940373/4025739238400000000000000000000000000000000)⟩
private theorem coeff041 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb90.threshold eb3.threshold) earlyRect) i j)
      ep041.coefficientLower) ∧ 0 < ep041.coefficientLower := by
  have hq : 0 < ep041.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid041 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep041 := by
  apply explicit_pair_valid 90 3 ep041.coefficientLower eb90 eb3
  · exact indexOk90.1
  · exact indexOk90.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup90
  · exact lookup3
  · rfl
  · rfl
  · exact threshold90
  · exact threshold3
  · exact coeff041.1
  · exact coeff041.2

private def ep042 : LowerEarlyTerminalPair := ⟨96,3,(390624580229215859330275768171904696798407/62786099200000000000000000000000000000000)⟩
private theorem coeff042 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb96.threshold eb3.threshold) earlyRect) i j)
      ep042.coefficientLower) ∧ 0 < ep042.coefficientLower := by
  have hq : 0 < ep042.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid042 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep042 := by
  apply explicit_pair_valid 96 3 ep042.coefficientLower eb96 eb3
  · exact indexOk96.1
  · exact indexOk96.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup96
  · exact lookup3
  · rfl
  · rfl
  · exact threshold96
  · exact threshold3
  · exact coeff042.1
  · exact coeff042.2

private def ep043 : LowerEarlyTerminalPair := ⟨100,3,(1112379273954803725281698229768446219929983/118010464000000000000000000000000000000000)⟩
private theorem coeff043 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb100.threshold eb3.threshold) earlyRect) i j)
      ep043.coefficientLower) ∧ 0 < ep043.coefficientLower := by
  have hq : 0 < ep043.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid043 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep043 := by
  apply explicit_pair_valid 100 3 ep043.coefficientLower eb100 eb3
  · exact indexOk100.1
  · exact indexOk100.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup100
  · exact lookup3
  · rfl
  · rfl
  · exact threshold100
  · exact threshold3
  · exact coeff043.1
  · exact coeff043.2

private def ep044 : LowerEarlyTerminalPair := ⟨2,101,(279248421583568542945075429390713579291/1032790528000000000000000000000000000000)⟩
private theorem coeff044 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb101.threshold) earlyRect) i j)
      ep044.coefficientLower) ∧ 0 < ep044.coefficientLower := by
  have hq : 0 < ep044.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid044 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep044 := by
  apply explicit_pair_valid 2 101 ep044.coefficientLower eb2 eb101
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup2
  · exact lookup101
  · rfl
  · rfl
  · exact threshold2
  · exact threshold101
  · exact coeff044.1
  · exact coeff044.2

private def ep045 : LowerEarlyTerminalPair := ⟨27,101,(109805127984057033009518015396098446889/71729664000000000000000000000000000000)⟩
private theorem coeff045 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb101.threshold) earlyRect) i j)
      ep045.coefficientLower) ∧ 0 < ep045.coefficientLower := by
  have hq : 0 < ep045.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid045 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep045 := by
  apply explicit_pair_valid 27 101 ep045.coefficientLower eb27 eb101
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup27
  · exact lookup101
  · rfl
  · rfl
  · exact threshold27
  · exact threshold101
  · exact coeff045.1
  · exact coeff045.2

private def ep046 : LowerEarlyTerminalPair := ⟨105,101,(334291012281174131940427107502322423821/115131714600000000000000000000000000000)⟩
private theorem coeff046 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb105.threshold eb101.threshold) earlyRect) i j)
      ep046.coefficientLower) ∧ 0 < ep046.coefficientLower := by
  have hq : 0 < ep046.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid046 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep046 := by
  apply explicit_pair_valid 105 101 ep046.coefficientLower eb105 eb101
  · exact indexOk105.1
  · exact indexOk105.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup105
  · exact lookup101
  · rfl
  · rfl
  · exact threshold105
  · exact threshold101
  · exact coeff046.1
  · exact coeff046.2

private def ep047 : LowerEarlyTerminalPair := ⟨107,101,(1243160737349861966156083556786770985021/205592347500000000000000000000000000000)⟩
private theorem coeff047 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb107.threshold eb101.threshold) earlyRect) i j)
      ep047.coefficientLower) ∧ 0 < ep047.coefficientLower := by
  have hq : 0 < ep047.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid047 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep047 := by
  apply explicit_pair_valid 107 101 ep047.coefficientLower eb107 eb101
  · exact indexOk107.1
  · exact indexOk107.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup107
  · exact lookup101
  · rfl
  · rfl
  · exact threshold107
  · exact threshold101
  · exact coeff047.1
  · exact coeff047.2

private def ep048 : LowerEarlyTerminalPair := ⟨43,101,(255137058749732788156600531228444661/56038800000000000000000000000000000)⟩
private theorem coeff048 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb43.threshold eb101.threshold) earlyRect) i j)
      ep048.coefficientLower) ∧ 0 < ep048.coefficientLower := by
  have hq : 0 < ep048.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid048 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep048 := by
  apply explicit_pair_valid 43 101 ep048.coefficientLower eb43 eb101
  · exact indexOk43.1
  · exact indexOk43.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup43
  · exact lookup101
  · rfl
  · rfl
  · exact threshold43
  · exact threshold101
  · exact coeff048.1
  · exact coeff048.2

end EarlyCompact16Pairs04

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs05
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep049 : LowerEarlyTerminalPair := ⟨2,102,(1501495182178183128149205727377797/13056000000000000000000000000000000)⟩
private theorem coeff049 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb102.threshold) earlyRect) i j)
      ep049.coefficientLower) ∧ 0 < ep049.coefficientLower := by
  have hq : 0 < ep049.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid049 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep049 := by
  apply explicit_pair_valid 2 102 ep049.coefficientLower eb2 eb102
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk102.1
  · exact indexOk102.2
  · exact lookup2
  · exact lookup102
  · rfl
  · rfl
  · exact threshold2
  · exact threshold102
  · exact coeff049.1
  · exact coeff049.2

private def ep050 : LowerEarlyTerminalPair := ⟨27,102,(2842912627344939718423922149801651/2091000000000000000000000000000000)⟩
private theorem coeff050 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb102.threshold) earlyRect) i j)
      ep050.coefficientLower) ∧ 0 < ep050.coefficientLower := by
  have hq : 0 < ep050.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid050 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep050 := by
  apply explicit_pair_valid 27 102 ep050.coefficientLower eb27 eb102
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk102.1
  · exact indexOk102.2
  · exact lookup27
  · exact lookup102
  · rfl
  · rfl
  · exact threshold27
  · exact threshold102
  · exact coeff050.1
  · exact coeff050.2

private def ep051 : LowerEarlyTerminalPair := ⟨105,102,(93495682202114037947390499006111167063/34367676000000000000000000000000000000)⟩
private theorem coeff051 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb105.threshold eb102.threshold) earlyRect) i j)
      ep051.coefficientLower) ∧ 0 < ep051.coefficientLower := by
  have hq : 0 < ep051.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid051 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep051 := by
  apply explicit_pair_valid 105 102 ep051.coefficientLower eb105 eb102
  · exact indexOk105.1
  · exact indexOk105.2
  · exact indexOk102.1
  · exact indexOk102.2
  · exact lookup105
  · exact lookup102
  · rfl
  · rfl
  · exact threshold105
  · exact threshold102
  · exact coeff051.1
  · exact coeff051.2

private def ep052 : LowerEarlyTerminalPair := ⟨107,102,(28649723781984624932171397378521661773/4909668000000000000000000000000000000)⟩
private theorem coeff052 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb107.threshold eb102.threshold) earlyRect) i j)
      ep052.coefficientLower) ∧ 0 < ep052.coefficientLower := by
  have hq : 0 < ep052.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid052 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep052 := by
  apply explicit_pair_valid 107 102 ep052.coefficientLower eb107 eb102
  · exact indexOk107.1
  · exact indexOk107.2
  · exact indexOk102.1
  · exact indexOk102.2
  · exact lookup107
  · exact lookup102
  · rfl
  · rfl
  · exact threshold107
  · exact threshold102
  · exact coeff052.1
  · exact coeff052.2

private def ep053 : LowerEarlyTerminalPair := ⟨43,102,(36420788768097840120415609177710239/8364000000000000000000000000000000)⟩
private theorem coeff053 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb43.threshold eb102.threshold) earlyRect) i j)
      ep053.coefficientLower) ∧ 0 < ep053.coefficientLower := by
  have hq : 0 < ep053.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid053 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep053 := by
  apply explicit_pair_valid 43 102 ep053.coefficientLower eb43 eb102
  · exact indexOk43.1
  · exact indexOk43.2
  · exact indexOk102.1
  · exact indexOk102.2
  · exact lookup43
  · exact lookup102
  · rfl
  · rfl
  · exact threshold43
  · exact threshold102
  · exact coeff053.1
  · exact coeff053.2

private def ep054 : LowerEarlyTerminalPair := ⟨114,103,(1594860521156032749709003728322282273541/12282830208000000000000000000000000000000)⟩
private theorem coeff054 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb114.threshold eb103.threshold) earlyRect) i j)
      ep054.coefficientLower) ∧ 0 < ep054.coefficientLower := by
  have hq : 0 < ep054.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid054 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep054 := by
  apply explicit_pair_valid 114 103 ep054.coefficientLower eb114 eb103
  · exact indexOk114.1
  · exact indexOk114.2
  · exact indexOk103.1
  · exact indexOk103.2
  · exact lookup114
  · exact lookup103
  · rfl
  · rfl
  · exact threshold114
  · exact threshold103
  · exact coeff054.1
  · exact coeff054.2

private def ep055 : LowerEarlyTerminalPair := ⟨27,103,(13427836991809019627354285723223193843387/10021811712000000000000000000000000000000)⟩
private theorem coeff055 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb103.threshold) earlyRect) i j)
      ep055.coefficientLower) ∧ 0 < ep055.coefficientLower := by
  have hq : 0 < ep055.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid055 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep055 := by
  apply explicit_pair_valid 27 103 ep055.coefficientLower eb27 eb103
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk103.1
  · exact indexOk103.2
  · exact lookup27
  · exact lookup103
  · rfl
  · rfl
  · exact threshold27
  · exact threshold103
  · exact coeff055.1
  · exact coeff055.2

private def ep056 : LowerEarlyTerminalPair := ⟨105,106,(46249812134071011337430751027197022946877567/16847201896448000000000000000000000000000000)⟩
private theorem coeff056 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb105.threshold eb106.threshold) earlyRect) i j)
      ep056.coefficientLower) ∧ 0 < ep056.coefficientLower := by
  have hq : 0 < ep056.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid056 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep056 := by
  apply explicit_pair_valid 105 106 ep056.coefficientLower eb105 eb106
  · exact indexOk105.1
  · exact indexOk105.2
  · exact indexOk106.1
  · exact indexOk106.2
  · exact lookup105
  · exact lookup106
  · rfl
  · rfl
  · exact threshold105
  · exact threshold106
  · exact coeff056.1
  · exact coeff056.2

private def ep057 : LowerEarlyTerminalPair := ⟨107,103,(41308236543635841543012149879253792239526643/6920945264640000000000000000000000000000000)⟩
private theorem coeff057 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb107.threshold eb103.threshold) earlyRect) i j)
      ep057.coefficientLower) ∧ 0 < ep057.coefficientLower := by
  have hq : 0 < ep057.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid057 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep057 := by
  apply explicit_pair_valid 107 103 ep057.coefficientLower eb107 eb103
  · exact indexOk107.1
  · exact indexOk107.2
  · exact indexOk103.1
  · exact indexOk103.2
  · exact lookup107
  · exact lookup103
  · rfl
  · rfl
  · exact threshold107
  · exact threshold103
  · exact coeff057.1
  · exact coeff057.2

private def ep058 : LowerEarlyTerminalPair := ⟨43,109,(3209767730673507269002031041126056926956589/725637265408000000000000000000000000000000)⟩
private theorem coeff058 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb43.threshold eb109.threshold) earlyRect) i j)
      ep058.coefficientLower) ∧ 0 < ep058.coefficientLower := by
  have hq : 0 < ep058.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid058 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep058 := by
  apply explicit_pair_valid 43 109 ep058.coefficientLower eb43 eb109
  · exact indexOk43.1
  · exact indexOk43.2
  · exact indexOk109.1
  · exact indexOk109.2
  · exact lookup43
  · exact lookup109
  · rfl
  · rfl
  · exact threshold43
  · exact threshold109
  · exact coeff058.1
  · exact coeff058.2

private def ep059 : LowerEarlyTerminalPair := ⟨2,116,(13458013925609777267122600805971629947/2149585152000000000000000000000000000000)⟩
private theorem coeff059 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb2.threshold eb116.threshold) earlyRect) i j)
      ep059.coefficientLower) ∧ 0 < ep059.coefficientLower := by
  have hq : 0 < ep059.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid059 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep059 := by
  apply explicit_pair_valid 2 116 ep059.coefficientLower eb2 eb116
  · exact indexOk2.1
  · exact indexOk2.2
  · exact indexOk116.1
  · exact indexOk116.2
  · exact lookup2
  · exact lookup116
  · rfl
  · rfl
  · exact threshold2
  · exact threshold116
  · exact coeff059.1
  · exact coeff059.2

private def ep060 : LowerEarlyTerminalPair := ⟨27,116,(335490670484131655326726198366873787058839/260567104512000000000000000000000000000000)⟩
private theorem coeff060 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb116.threshold) earlyRect) i j)
      ep060.coefficientLower) ∧ 0 < ep060.coefficientLower := by
  have hq : 0 < ep060.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid060 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep060 := by
  apply explicit_pair_valid 27 116 ep060.coefficientLower eb27 eb116
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk116.1
  · exact indexOk116.2
  · exact lookup27
  · exact lookup116
  · rfl
  · rfl
  · exact threshold27
  · exact threshold116
  · exact coeff060.1
  · exact coeff060.2

end EarlyCompact16Pairs05

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs06
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep061 : LowerEarlyTerminalPair := ⟨105,118,(35351573288869796317245675815735227309276001/13140817479229440000000000000000000000000000)⟩
private theorem coeff061 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb105.threshold eb118.threshold) earlyRect) i j)
      ep061.coefficientLower) ∧ 0 < ep061.coefficientLower := by
  have hq : 0 < ep061.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid061 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep061 := by
  apply explicit_pair_valid 105 118 ep061.coefficientLower eb105 eb118
  · exact indexOk105.1
  · exact indexOk105.2
  · exact indexOk118.1
  · exact indexOk118.2
  · exact lookup105
  · exact lookup118
  · rfl
  · rfl
  · exact threshold105
  · exact threshold118
  · exact coeff061.1
  · exact coeff061.2

private def ep062 : LowerEarlyTerminalPair := ⟨107,116,(66439274241477174773706008351385957844291529/11246536055040000000000000000000000000000000)⟩
private theorem coeff062 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb107.threshold eb116.threshold) earlyRect) i j)
      ep062.coefficientLower) ∧ 0 < ep062.coefficientLower := by
  have hq : 0 < ep062.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid062 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep062 := by
  apply explicit_pair_valid 107 116 ep062.coefficientLower eb107 eb116
  · exact indexOk107.1
  · exact indexOk107.2
  · exact indexOk116.1
  · exact indexOk116.2
  · exact lookup107
  · exact lookup116
  · rfl
  · rfl
  · exact threshold107
  · exact threshold116
  · exact coeff062.1
  · exact coeff062.2

private def ep063 : LowerEarlyTerminalPair := ⟨43,119,(15441498819206307752081328446311854798187907/3537481668864000000000000000000000000000000)⟩
private theorem coeff063 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb43.threshold eb119.threshold) earlyRect) i j)
      ep063.coefficientLower) ∧ 0 < ep063.coefficientLower := by
  have hq : 0 < ep063.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid063 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep063 := by
  apply explicit_pair_valid 43 119 ep063.coefficientLower eb43 eb119
  · exact indexOk43.1
  · exact indexOk43.2
  · exact indexOk119.1
  · exact indexOk119.2
  · exact lookup43
  · exact lookup119
  · rfl
  · rfl
  · exact threshold43
  · exact threshold119
  · exact coeff063.1
  · exact coeff063.2

private def ep064 : LowerEarlyTerminalPair := ⟨120,121,(479744498658741533807232665980335441450782877/364650318110310400000000000000000000000000000)⟩
private theorem coeff064 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb120.threshold eb121.threshold) earlyRect) i j)
      ep064.coefficientLower) ∧ 0 < ep064.coefficientLower := by
  have hq : 0 < ep064.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid064 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep064 := by
  apply explicit_pair_valid 120 121 ep064.coefficientLower eb120 eb121
  · exact indexOk120.1
  · exact indexOk120.2
  · exact indexOk121.1
  · exact indexOk121.2
  · exact lookup120
  · exact lookup121
  · rfl
  · rfl
  · exact threshold120
  · exact threshold121
  · exact coeff064.1
  · exact coeff064.2

private def ep065 : LowerEarlyTerminalPair := ⟨122,3,(822065526896834465510229600797557829506485749/782837381427200000000000000000000000000000000)⟩
private theorem coeff065 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb122.threshold eb3.threshold) earlyRect) i j)
      ep065.coefficientLower) ∧ 0 < ep065.coefficientLower := by
  have hq : 0 < ep065.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid065 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep065 := by
  apply explicit_pair_valid 122 3 ep065.coefficientLower eb122 eb3
  · exact indexOk122.1
  · exact indexOk122.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup122
  · exact lookup3
  · rfl
  · rfl
  · exact threshold122
  · exact threshold3
  · exact coeff065.1
  · exact coeff065.2

private def ep066 : LowerEarlyTerminalPair := ⟨120,3,(235460811261475569151560232800985060719171297/217579444121600000000000000000000000000000000)⟩
private theorem coeff066 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb120.threshold eb3.threshold) earlyRect) i j)
      ep066.coefficientLower) ∧ 0 < ep066.coefficientLower := by
  have hq : 0 < ep066.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid066 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep066 := by
  apply explicit_pair_valid 120 3 ep066.coefficientLower eb120 eb3
  · exact indexOk120.1
  · exact indexOk120.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup120
  · exact lookup3
  · rfl
  · rfl
  · exact threshold120
  · exact threshold3
  · exact coeff066.1
  · exact coeff066.2

private def ep067 : LowerEarlyTerminalPair := ⟨125,3,(817956375661562499419783307975018101301497667/765849141516800000000000000000000000000000000)⟩
private theorem coeff067 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb125.threshold eb3.threshold) earlyRect) i j)
      ep067.coefficientLower) ∧ 0 < ep067.coefficientLower := by
  have hq : 0 < ep067.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid067 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep067 := by
  apply explicit_pair_valid 125 3 ep067.coefficientLower eb125 eb3
  · exact indexOk125.1
  · exact indexOk125.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup125
  · exact lookup3
  · rfl
  · rfl
  · exact threshold125
  · exact threshold3
  · exact coeff067.1
  · exact coeff067.2

private def ep068 : LowerEarlyTerminalPair := ⟨27,3,(552444862292635430201436930096873709362057/472041856000000000000000000000000000000000)⟩
private theorem coeff068 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb3.threshold) earlyRect) i j)
      ep068.coefficientLower) ∧ 0 < ep068.coefficientLower := by
  have hq : 0 < ep068.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid068 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep068 := by
  apply explicit_pair_valid 27 3 ep068.coefficientLower eb27 eb3
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup27
  · exact lookup3
  · rfl
  · rfl
  · exact threshold27
  · exact threshold3
  · exact coeff068.1
  · exact coeff068.2

private def ep069 : LowerEarlyTerminalPair := ⟨127,121,(2070208637570869347005595253612176889310199/2793303199232000000000000000000000000000000)⟩
private theorem coeff069 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb127.threshold eb121.threshold) earlyRect) i j)
      ep069.coefficientLower) ∧ 0 < ep069.coefficientLower := by
  have hq : 0 < ep069.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid069 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep069 := by
  apply explicit_pair_valid 127 121 ep069.coefficientLower eb127 eb121
  · exact indexOk127.1
  · exact indexOk127.2
  · exact indexOk121.1
  · exact indexOk121.2
  · exact lookup127
  · exact lookup121
  · rfl
  · rfl
  · exact threshold127
  · exact threshold121
  · exact coeff069.1
  · exact coeff069.2

private def ep070 : LowerEarlyTerminalPair := ⟨129,121,(22269206583809262904616027714547953157/32031791680000000000000000000000000000)⟩
private theorem coeff070 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb129.threshold eb121.threshold) earlyRect) i j)
      ep070.coefficientLower) ∧ 0 < ep070.coefficientLower := by
  have hq : 0 < ep070.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid070 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep070 := by
  apply explicit_pair_valid 129 121 ep070.coefficientLower eb129 eb121
  · exact indexOk129.1
  · exact indexOk129.2
  · exact indexOk121.1
  · exact indexOk121.2
  · exact lookup129
  · exact lookup121
  · rfl
  · rfl
  · exact threshold129
  · exact threshold121
  · exact coeff070.1
  · exact coeff070.2

private def ep071 : LowerEarlyTerminalPair := ⟨131,121,(45327566397142110855550231774701890491671/23451847480000000000000000000000000000000)⟩
private theorem coeff071 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb131.threshold eb121.threshold) earlyRect) i j)
      ep071.coefficientLower) ∧ 0 < ep071.coefficientLower := by
  have hq : 0 < ep071.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid071 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep071 := by
  apply explicit_pair_valid 131 121 ep071.coefficientLower eb131 eb121
  · exact indexOk131.1
  · exact indexOk131.2
  · exact indexOk121.1
  · exact indexOk121.2
  · exact lookup131
  · exact lookup121
  · rfl
  · rfl
  · exact threshold131
  · exact threshold121
  · exact coeff071.1
  · exact coeff071.2

private def ep072 : LowerEarlyTerminalPair := ⟨75,121,(167517027808243406720855614828518630263/135836936000000000000000000000000000000)⟩
private theorem coeff072 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb75.threshold eb121.threshold) earlyRect) i j)
      ep072.coefficientLower) ∧ 0 < ep072.coefficientLower := by
  have hq : 0 < ep072.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid072 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep072 := by
  apply explicit_pair_valid 75 121 ep072.coefficientLower eb75 eb121
  · exact indexOk75.1
  · exact indexOk75.2
  · exact indexOk121.1
  · exact indexOk121.2
  · exact lookup75
  · exact lookup121
  · rfl
  · rfl
  · exact threshold75
  · exact threshold121
  · exact coeff072.1
  · exact coeff072.2

end EarlyCompact16Pairs06

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs07
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep073 : LowerEarlyTerminalPair := ⟨134,3,(5868769807292149377061926127637092177791/15912012800000000000000000000000000000000)⟩
private theorem coeff073 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb134.threshold eb3.threshold) earlyRect) i j)
      ep073.coefficientLower) ∧ 0 < ep073.coefficientLower := by
  have hq : 0 < ep073.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid073 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep073 := by
  apply explicit_pair_valid 134 3 ep073.coefficientLower eb134 eb3
  · exact indexOk134.1
  · exact indexOk134.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup134
  · exact lookup3
  · rfl
  · rfl
  · exact threshold134
  · exact threshold3
  · exact coeff073.1
  · exact coeff073.2

private def ep074 : LowerEarlyTerminalPair := ⟨129,3,(9993919384103544391412397267078692129897607/20744598784000000000000000000000000000000000)⟩
private theorem coeff074 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb129.threshold eb3.threshold) earlyRect) i j)
      ep074.coefficientLower) ∧ 0 < ep074.coefficientLower := by
  have hq : 0 < ep074.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid074 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep074 := by
  apply explicit_pair_valid 129 3 ep074.coefficientLower eb129 eb3
  · exact indexOk129.1
  · exact indexOk129.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup129
  · exact lookup3
  · rfl
  · rfl
  · exact threshold129
  · exact threshold3
  · exact coeff074.1
  · exact coeff074.2

private def ep075 : LowerEarlyTerminalPair := ⟨131,3,(4945074116039422129795291001698077145397601/2963514112000000000000000000000000000000000)⟩
private theorem coeff075 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb131.threshold eb3.threshold) earlyRect) i j)
      ep075.coefficientLower) ∧ 0 < ep075.coefficientLower := by
  have hq : 0 < ep075.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid075 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep075 := by
  apply explicit_pair_valid 131 3 ep075.coefficientLower eb131 eb3
  · exact indexOk131.1
  · exact indexOk131.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup131
  · exact lookup3
  · rfl
  · rfl
  · exact threshold131
  · exact threshold3
  · exact coeff075.1
  · exact coeff075.2

private def ep076 : LowerEarlyTerminalPair := ⟨75,3,(470709693717210738516174728806636128129057/472041856000000000000000000000000000000000)⟩
private theorem coeff076 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb75.threshold eb3.threshold) earlyRect) i j)
      ep076.coefficientLower) ∧ 0 < ep076.coefficientLower := by
  have hq : 0 < ep076.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid076 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep076 := by
  apply explicit_pair_valid 75 3 ep076.coefficientLower eb75 eb3
  · exact indexOk75.1
  · exact indexOk75.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup75
  · exact lookup3
  · rfl
  · rfl
  · exact threshold75
  · exact threshold3
  · exact coeff076.1
  · exact coeff076.2

private def ep077 : LowerEarlyTerminalPair := ⟨127,3,(306089726751847692757028503857523787981/582764800000000000000000000000000000000)⟩
private theorem coeff077 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb127.threshold eb3.threshold) earlyRect) i j)
      ep077.coefficientLower) ∧ 0 < ep077.coefficientLower := by
  have hq : 0 < ep077.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid077 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep077 := by
  apply explicit_pair_valid 127 3 ep077.coefficientLower eb127 eb3
  · exact indexOk127.1
  · exact indexOk127.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup127
  · exact lookup3
  · rfl
  · rfl
  · exact threshold127
  · exact threshold3
  · exact coeff077.1
  · exact coeff077.2

private def ep078 : LowerEarlyTerminalPair := ⟨137,3,(2366660191234389753820245572812537189037/5707827200000000000000000000000000000000)⟩
private theorem coeff078 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb137.threshold eb3.threshold) earlyRect) i j)
      ep078.coefficientLower) ∧ 0 < ep078.coefficientLower := by
  have hq : 0 < ep078.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid078 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep078 := by
  apply explicit_pair_valid 137 3 ep078.coefficientLower eb137 eb3
  · exact indexOk137.1
  · exact indexOk137.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup137
  · exact lookup3
  · rfl
  · rfl
  · exact threshold137
  · exact threshold3
  · exact coeff078.1
  · exact coeff078.2

private def ep079 : LowerEarlyTerminalPair := ⟨140,141,(16054567491378763728167746074692169726711/54100843520000000000000000000000000000000)⟩
private theorem coeff079 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb140.threshold eb141.threshold) earlyRect) i j)
      ep079.coefficientLower) ∧ 0 < ep079.coefficientLower := by
  have hq : 0 < ep079.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid079 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep079 := by
  apply explicit_pair_valid 140 141 ep079.coefficientLower eb140 eb141
  · exact indexOk140.1
  · exact indexOk140.2
  · exact indexOk141.1
  · exact indexOk141.2
  · exact lookup140
  · exact lookup141
  · rfl
  · rfl
  · exact threshold140
  · exact threshold141
  · exact coeff079.1
  · exact coeff079.2

private def ep080 : LowerEarlyTerminalPair := ⟨144,3,(59257217178484729613195200658901802947783/441370856960000000000000000000000000000000)⟩
private theorem coeff080 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb144.threshold eb3.threshold) earlyRect) i j)
      ep080.coefficientLower) ∧ 0 < ep080.coefficientLower := by
  have hq : 0 < ep080.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid080 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep080 := by
  apply explicit_pair_valid 144 3 ep080.coefficientLower eb144 eb3
  · exact indexOk144.1
  · exact indexOk144.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup144
  · exact lookup3
  · rfl
  · rfl
  · exact threshold144
  · exact threshold3
  · exact coeff080.1
  · exact coeff080.2

private def ep081 : LowerEarlyTerminalPair := ⟨146,3,(67557071826703251926883477224889240850689/115132160000000000000000000000000000000000)⟩
private theorem coeff081 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb146.threshold eb3.threshold) earlyRect) i j)
      ep081.coefficientLower) ∧ 0 < ep081.coefficientLower := by
  have hq : 0 < ep081.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid081 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep081 := by
  apply explicit_pair_valid 146 3 ep081.coefficientLower eb146 eb3
  · exact indexOk146.1
  · exact indexOk146.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup146
  · exact lookup3
  · rfl
  · rfl
  · exact threshold146
  · exact threshold3
  · exact coeff081.1
  · exact coeff081.2

private def ep082 : LowerEarlyTerminalPair := ⟨147,3,(1622650420975242511056370923609027244293/6772480000000000000000000000000000000000)⟩
private theorem coeff082 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb147.threshold eb3.threshold) earlyRect) i j)
      ep082.coefficientLower) ∧ 0 < ep082.coefficientLower := by
  have hq : 0 < ep082.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid082 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep082 := by
  apply explicit_pair_valid 147 3 ep082.coefficientLower eb147 eb3
  · exact indexOk147.1
  · exact indexOk147.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup147
  · exact lookup3
  · rfl
  · rfl
  · exact threshold147
  · exact threshold3
  · exact coeff082.1
  · exact coeff082.2

private def ep083 : LowerEarlyTerminalPair := ⟨150,141,(108060942953553620833646306965214340569/185533376000000000000000000000000000000)⟩
private theorem coeff083 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb150.threshold eb141.threshold) earlyRect) i j)
      ep083.coefficientLower) ∧ 0 < ep083.coefficientLower := by
  have hq : 0 < ep083.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid083 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep083 := by
  apply explicit_pair_valid 150 141 ep083.coefficientLower eb150 eb141
  · exact indexOk150.1
  · exact indexOk150.2
  · exact indexOk141.1
  · exact indexOk141.2
  · exact lookup150
  · exact lookup141
  · rfl
  · rfl
  · exact threshold150
  · exact threshold141
  · exact coeff083.1
  · exact coeff083.2

private def ep084 : LowerEarlyTerminalPair := ⟨150,3,(59060732721600285979026068186280007635179697/115489069696000000000000000000000000000000000)⟩
private theorem coeff084 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb150.threshold eb3.threshold) earlyRect) i j)
      ep084.coefficientLower) ∧ 0 < ep084.coefficientLower := by
  have hq : 0 < ep084.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid084 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep084 := by
  apply explicit_pair_valid 150 3 ep084.coefficientLower eb150 eb3
  · exact indexOk150.1
  · exact indexOk150.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup150
  · exact lookup3
  · rfl
  · rfl
  · exact threshold150
  · exact threshold3
  · exact coeff084.1
  · exact coeff084.2

end EarlyCompact16Pairs07

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs08
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep085 : LowerEarlyTerminalPair := ⟨154,141,(337276978701425921336593729293366063227/185533376000000000000000000000000000000)⟩
private theorem coeff085 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb154.threshold eb141.threshold) earlyRect) i j)
      ep085.coefficientLower) ∧ 0 < ep085.coefficientLower := by
  have hq : 0 < ep085.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid085 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep085 := by
  apply explicit_pair_valid 154 141 ep085.coefficientLower eb154 eb141
  · exact indexOk154.1
  · exact indexOk154.2
  · exact indexOk141.1
  · exact indexOk141.2
  · exact lookup154
  · exact lookup141
  · rfl
  · rfl
  · exact threshold154
  · exact threshold141
  · exact coeff085.1
  · exact coeff085.2

private def ep086 : LowerEarlyTerminalPair := ⟨154,3,(28561853469902004300287421101542656248150271/16498438528000000000000000000000000000000000)⟩
private theorem coeff086 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb154.threshold eb3.threshold) earlyRect) i j)
      ep086.coefficientLower) ∧ 0 < ep086.coefficientLower := by
  have hq : 0 < ep086.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid086 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep086 := by
  apply explicit_pair_valid 154 3 ep086.coefficientLower eb154 eb3
  · exact indexOk154.1
  · exact indexOk154.2
  · exact indexOk3.1
  · exact indexOk3.2
  · exact lookup154
  · exact lookup3
  · rfl
  · rfl
  · exact threshold154
  · exact threshold3
  · exact coeff086.1
  · exact coeff086.2

private def ep087 : LowerEarlyTerminalPair := ⟨75,141,(16292806915501211730335943497206274533/15166720000000000000000000000000000000)⟩
private theorem coeff087 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb75.threshold eb141.threshold) earlyRect) i j)
      ep087.coefficientLower) ∧ 0 < ep087.coefficientLower := by
  have hq : 0 < ep087.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid087 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep087 := by
  apply explicit_pair_valid 75 141 ep087.coefficientLower eb75 eb141
  · exact indexOk75.1
  · exact indexOk75.2
  · exact indexOk141.1
  · exact indexOk141.2
  · exact lookup75
  · exact lookup141
  · rfl
  · rfl
  · exact threshold75
  · exact threshold141
  · exact coeff087.1
  · exact coeff087.2

private def ep088 : LowerEarlyTerminalPair := ⟨159,162,(222007429911159424348614467559636855775774101/561321376000000000000000000000000000000000000)⟩
private theorem coeff088 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb162.threshold) earlyRect) i j)
      ep088.coefficientLower) ∧ 0 < ep088.coefficientLower := by
  have hq : 0 < ep088.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid088 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep088 := by
  apply explicit_pair_valid 159 162 ep088.coefficientLower eb159 eb162
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk162.1
  · exact indexOk162.2
  · exact lookup159
  · exact lookup162
  · rfl
  · rfl
  · exact threshold159
  · exact threshold162
  · exact coeff088.1
  · exact coeff088.2

private def ep089 : LowerEarlyTerminalPair := ⟨172,162,(22199296912898178602166042520227233858347463/27286210735000000000000000000000000000000000)⟩
private theorem coeff089 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb172.threshold eb162.threshold) earlyRect) i j)
      ep089.coefficientLower) ∧ 0 < ep089.coefficientLower := by
  have hq : 0 < ep089.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid089 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep089 := by
  apply explicit_pair_valid 172 162 ep089.coefficientLower eb172 eb162
  · exact indexOk172.1
  · exact indexOk172.2
  · exact indexOk162.1
  · exact indexOk162.2
  · exact lookup172
  · exact lookup162
  · rfl
  · rfl
  · exact threshold172
  · exact threshold162
  · exact coeff089.1
  · exact coeff089.2

private def ep090 : LowerEarlyTerminalPair := ⟨173,162,(16482915052240381208380023561598388344251/28099997800000000000000000000000000000000)⟩
private theorem coeff090 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb173.threshold eb162.threshold) earlyRect) i j)
      ep090.coefficientLower) ∧ 0 < ep090.coefficientLower := by
  have hq : 0 < ep090.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid090 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep090 := by
  apply explicit_pair_valid 173 162 ep090.coefficientLower eb173 eb162
  · exact indexOk173.1
  · exact indexOk173.2
  · exact indexOk162.1
  · exact indexOk162.2
  · exact lookup173
  · exact lookup162
  · rfl
  · rfl
  · exact threshold173
  · exact threshold162
  · exact coeff090.1
  · exact coeff090.2

private def ep091 : LowerEarlyTerminalPair := ⟨159,164,(381205184455733424106231981278295339110219/1161653504000000000000000000000000000000000)⟩
private theorem coeff091 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb164.threshold) earlyRect) i j)
      ep091.coefficientLower) ∧ 0 < ep091.coefficientLower := by
  have hq : 0 < ep091.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid091 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep091 := by
  apply explicit_pair_valid 159 164 ep091.coefficientLower eb159 eb164
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk164.1
  · exact indexOk164.2
  · exact lookup159
  · exact lookup164
  · rfl
  · rfl
  · exact threshold159
  · exact threshold164
  · exact coeff091.1
  · exact coeff091.2

private def ep092 : LowerEarlyTerminalPair := ⟨172,164,(42109173548821473587589714796953833121771/56468760440000000000000000000000000000000)⟩
private theorem coeff092 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb172.threshold eb164.threshold) earlyRect) i j)
      ep092.coefficientLower) ∧ 0 < ep092.coefficientLower := by
  have hq : 0 < ep092.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid092 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep092 := by
  apply explicit_pair_valid 172 164 ep092.coefficientLower eb172 eb164
  · exact indexOk172.1
  · exact indexOk172.2
  · exact indexOk164.1
  · exact indexOk164.2
  · exact lookup172
  · exact lookup164
  · rfl
  · rfl
  · exact threshold172
  · exact threshold164
  · exact coeff092.1
  · exact coeff092.2

private def ep093 : LowerEarlyTerminalPair := ⟨173,164,(1055878813758829678641788113829467759189/2035351192000000000000000000000000000000)⟩
private theorem coeff093 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb173.threshold eb164.threshold) earlyRect) i j)
      ep093.coefficientLower) ∧ 0 < ep093.coefficientLower := by
  have hq : 0 < ep093.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid093 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep093 := by
  apply explicit_pair_valid 173 164 ep093.coefficientLower eb173 eb164
  · exact indexOk173.1
  · exact indexOk173.2
  · exact indexOk164.1
  · exact indexOk164.2
  · exact lookup173
  · exact lookup164
  · rfl
  · rfl
  · exact threshold173
  · exact threshold164
  · exact coeff093.1
  · exact coeff093.2

private def ep094 : LowerEarlyTerminalPair := ⟨159,165,(1073107309321132997407707463396450517780091/3836487424000000000000000000000000000000000)⟩
private theorem coeff094 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb165.threshold) earlyRect) i j)
      ep094.coefficientLower) ∧ 0 < ep094.coefficientLower := by
  have hq : 0 < ep094.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid094 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep094 := by
  apply explicit_pair_valid 159 165 ep094.coefficientLower eb159 eb165
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk165.1
  · exact indexOk165.2
  · exact lookup159
  · exact lookup165
  · rfl
  · rfl
  · exact threshold159
  · exact threshold165
  · exact coeff094.1
  · exact coeff094.2

private def ep095 : LowerEarlyTerminalPair := ⟨159,163,(18417822783139107621283278820695129691796757/97492468480000000000000000000000000000000000)⟩
private theorem coeff095 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb163.threshold) earlyRect) i j)
      ep095.coefficientLower) ∧ 0 < ep095.coefficientLower := by
  have hq : 0 < ep095.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid095 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep095 := by
  apply explicit_pair_valid 159 163 ep095.coefficientLower eb159 eb163
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk163.1
  · exact indexOk163.2
  · exact lookup159
  · exact lookup163
  · rfl
  · rfl
  · exact threshold159
  · exact threshold163
  · exact coeff095.1
  · exact coeff095.2

private def ep096 : LowerEarlyTerminalPair := ⟨159,171,(391406991937284232152603113452636190727058557/2534804180480000000000000000000000000000000000)⟩
private theorem coeff096 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb171.threshold) earlyRect) i j)
      ep096.coefficientLower) ∧ 0 < ep096.coefficientLower := by
  have hq : 0 < ep096.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid096 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep096 := by
  apply explicit_pair_valid 159 171 ep096.coefficientLower eb159 eb171
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk171.1
  · exact indexOk171.2
  · exact lookup159
  · exact lookup171
  · rfl
  · rfl
  · exact threshold159
  · exact threshold171
  · exact coeff096.1
  · exact coeff096.2

end EarlyCompact16Pairs08

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs09
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep097 : LowerEarlyTerminalPair := ⟨172,163,(73540590012086482381624272856660826160870287/121322871239680000000000000000000000000000000)⟩
private theorem coeff097 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb172.threshold eb163.threshold) earlyRect) i j)
      ep097.coefficientLower) ∧ 0 < ep097.coefficientLower := by
  have hq : 0 < ep097.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid097 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep097 := by
  apply explicit_pair_valid 172 163 ep097.coefficientLower eb172 eb163
  · exact indexOk172.1
  · exact indexOk172.2
  · exact indexOk163.1
  · exact indexOk163.2
  · exact lookup172
  · exact lookup163
  · rfl
  · rfl
  · exact threshold172
  · exact threshold163
  · exact coeff097.1
  · exact coeff097.2

private def ep098 : LowerEarlyTerminalPair := ⟨173,174,(51479900006511563799573496769936419197952089/160912730868736000000000000000000000000000000)⟩
private theorem coeff098 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb173.threshold eb174.threshold) earlyRect) i j)
      ep098.coefficientLower) ∧ 0 < ep098.coefficientLower := by
  have hq : 0 < ep098.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid098 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep098 := by
  apply explicit_pair_valid 173 174 ep098.coefficientLower eb173 eb174
  · exact indexOk173.1
  · exact indexOk173.2
  · exact indexOk174.1
  · exact indexOk174.2
  · exact lookup173
  · exact lookup174
  · rfl
  · rfl
  · exact threshold173
  · exact threshold174
  · exact coeff098.1
  · exact coeff098.2

private def ep099 : LowerEarlyTerminalPair := ⟨159,183,(18040522524432710727294312183905703814843443/80188768000000000000000000000000000000000000)⟩
private theorem coeff099 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb183.threshold) earlyRect) i j)
      ep099.coefficientLower) ∧ 0 < ep099.coefficientLower := by
  have hq : 0 < ep099.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid099 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep099 := by
  apply explicit_pair_valid 159 183 ep099.coefficientLower eb159 eb183
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk183.1
  · exact indexOk183.2
  · exact lookup159
  · exact lookup183
  · rfl
  · rfl
  · exact threshold159
  · exact threshold183
  · exact coeff099.1
  · exact coeff099.2

private def ep100 : LowerEarlyTerminalPair := ⟨172,183,(2503039415228675125627250515364356332417209/3898030105000000000000000000000000000000000)⟩
private theorem coeff100 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb172.threshold eb183.threshold) earlyRect) i j)
      ep100.coefficientLower) ∧ 0 < ep100.coefficientLower := by
  have hq : 0 < ep100.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid100 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep100 := by
  apply explicit_pair_valid 172 183 ep100.coefficientLower eb172 eb183
  · exact indexOk172.1
  · exact indexOk172.2
  · exact indexOk183.1
  · exact indexOk183.2
  · exact lookup172
  · exact lookup183
  · rfl
  · rfl
  · exact threshold172
  · exact threshold183
  · exact coeff100.1
  · exact coeff100.2

private def ep101 : LowerEarlyTerminalPair := ⟨173,183,(93305719118476933910342277505906720191/224799982400000000000000000000000000000)⟩
private theorem coeff101 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb173.threshold eb183.threshold) earlyRect) i j)
      ep101.coefficientLower) ∧ 0 < ep101.coefficientLower := by
  have hq : 0 < ep101.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid101 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep101 := by
  apply explicit_pair_valid 173 183 ep101.coefficientLower eb173 eb183
  · exact indexOk173.1
  · exact indexOk173.2
  · exact indexOk183.1
  · exact indexOk183.2
  · exact lookup173
  · exact lookup183
  · rfl
  · rfl
  · exact threshold173
  · exact threshold183
  · exact coeff101.1
  · exact coeff101.2

private def ep102 : LowerEarlyTerminalPair := ⟨186,165,(45696327611021794709823362214255089947/130540221440000000000000000000000000000)⟩
private theorem coeff102 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb186.threshold eb165.threshold) earlyRect) i j)
      ep102.coefficientLower) ∧ 0 < ep102.coefficientLower := by
  have hq : 0 < ep102.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid102 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep102 := by
  apply explicit_pair_valid 186 165 ep102.coefficientLower eb186 eb165
  · exact indexOk186.1
  · exact indexOk186.2
  · exact indexOk165.1
  · exact indexOk165.2
  · exact lookup186
  · exact lookup165
  · rfl
  · rfl
  · exact threshold186
  · exact threshold165
  · exact coeff102.1
  · exact coeff102.2

private def ep103 : LowerEarlyTerminalPair := ⟨186,163,(480979948174585877501803721655873712182781/1857674672128000000000000000000000000000000)⟩
private theorem coeff103 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb186.threshold eb163.threshold) earlyRect) i j)
      ep103.coefficientLower) ∧ 0 < ep103.coefficientLower := by
  have hq : 0 < ep103.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid103 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep103 := by
  apply explicit_pair_valid 186 163 ep103.coefficientLower eb186 eb163
  · exact indexOk186.1
  · exact indexOk186.2
  · exact indexOk163.1
  · exact indexOk163.2
  · exact lookup186
  · exact lookup163
  · rfl
  · rfl
  · exact threshold186
  · exact threshold163
  · exact coeff103.1
  · exact coeff103.2

private def ep104 : LowerEarlyTerminalPair := ⟨186,171,(2708534895607341338979347507394357470932871/12074885368832000000000000000000000000000000)⟩
private theorem coeff104 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb186.threshold eb171.threshold) earlyRect) i j)
      ep104.coefficientLower) ∧ 0 < ep104.coefficientLower := by
  have hq : 0 < ep104.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid104 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep104 := by
  apply explicit_pair_valid 186 171 ep104.coefficientLower eb186 eb171
  · exact indexOk186.1
  · exact indexOk186.2
  · exact indexOk171.1
  · exact indexOk171.2
  · exact lookup186
  · exact lookup171
  · rfl
  · rfl
  · exact threshold186
  · exact threshold171
  · exact coeff104.1
  · exact coeff104.2

private def ep105 : LowerEarlyTerminalPair := ⟨188,160,(1988909902709477549566479620892726451619/303191961600000000000000000000000000000)⟩
private theorem coeff105 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb188.threshold eb160.threshold) earlyRect) i j)
      ep105.coefficientLower) ∧ 0 < ep105.coefficientLower := by
  have hq : 0 < ep105.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid105 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep105 := by
  apply explicit_pair_valid 188 160 ep105.coefficientLower eb188 eb160
  · exact indexOk188.1
  · exact indexOk188.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup188
  · exact lookup160
  · rfl
  · rfl
  · exact threshold188
  · exact threshold160
  · exact coeff105.1
  · exact coeff105.2

private def ep106 : LowerEarlyTerminalPair := ⟨193,160,(266896044615164128902981527316654139469761/47601137971200000000000000000000000000000)⟩
private theorem coeff106 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb193.threshold eb160.threshold) earlyRect) i j)
      ep106.coefficientLower) ∧ 0 < ep106.coefficientLower := by
  have hq : 0 < ep106.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid106 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep106 := by
  apply explicit_pair_valid 193 160 ep106.coefficientLower eb193 eb160
  · exact indexOk193.1
  · exact indexOk193.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup193
  · exact lookup160
  · rfl
  · rfl
  · exact threshold193
  · exact threshold160
  · exact coeff106.1
  · exact coeff106.2

private def ep107 : LowerEarlyTerminalPair := ⟨197,160,(81118592304476565361765455995067439107701/13581538713600000000000000000000000000000)⟩
private theorem coeff107 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb197.threshold eb160.threshold) earlyRect) i j)
      ep107.coefficientLower) ∧ 0 < ep107.coefficientLower := by
  have hq : 0 < ep107.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid107 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep107 := by
  apply explicit_pair_valid 197 160 ep107.coefficientLower eb197 eb160
  · exact indexOk197.1
  · exact indexOk197.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup197
  · exact lookup160
  · rfl
  · rfl
  · exact threshold197
  · exact threshold160
  · exact coeff107.1
  · exact coeff107.2

private def ep108 : LowerEarlyTerminalPair := ⟨199,160,(375808028800176757057425765857413487573/42617344000000000000000000000000000000)⟩
private theorem coeff108 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb199.threshold eb160.threshold) earlyRect) i j)
      ep108.coefficientLower) ∧ 0 < ep108.coefficientLower := by
  have hq : 0 < ep108.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid108 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep108 := by
  apply explicit_pair_valid 199 160 ep108.coefficientLower eb199 eb160
  · exact indexOk199.1
  · exact indexOk199.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup199
  · exact lookup160
  · rfl
  · rfl
  · exact threshold199
  · exact threshold160
  · exact coeff108.1
  · exact coeff108.2

end EarlyCompact16Pairs09

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs10
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep109 : LowerEarlyTerminalPair := ⟨203,160,(7613623049790615399255830225051377623931/1031303454720000000000000000000000000000)⟩
private theorem coeff109 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb203.threshold eb160.threshold) earlyRect) i j)
      ep109.coefficientLower) ∧ 0 < ep109.coefficientLower := by
  have hq : 0 < ep109.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid109 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep109 := by
  apply explicit_pair_valid 203 160 ep109.coefficientLower eb203 eb160
  · exact indexOk203.1
  · exact indexOk203.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup203
  · exact lookup160
  · rfl
  · rfl
  · exact threshold203
  · exact threshold160
  · exact coeff109.1
  · exact coeff109.2

private def ep110 : LowerEarlyTerminalPair := ⟨207,160,(2418170956020081847589550682918642239539/160140288000000000000000000000000000000)⟩
private theorem coeff110 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb207.threshold eb160.threshold) earlyRect) i j)
      ep110.coefficientLower) ∧ 0 < ep110.coefficientLower := by
  have hq : 0 < ep110.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid110 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep110 := by
  apply explicit_pair_valid 207 160 ep110.coefficientLower eb207 eb160
  · exact indexOk207.1
  · exact indexOk207.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup207
  · exact lookup160
  · rfl
  · rfl
  · exact threshold207
  · exact threshold160
  · exact coeff110.1
  · exact coeff110.2

private def ep111 : LowerEarlyTerminalPair := ⟨208,160,(19275034935801152546893425559263170967/1813504000000000000000000000000000000)⟩
private theorem coeff111 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb208.threshold eb160.threshold) earlyRect) i j)
      ep111.coefficientLower) ∧ 0 < ep111.coefficientLower := by
  have hq : 0 < ep111.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid111 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep111 := by
  apply explicit_pair_valid 208 160 ep111.coefficientLower eb208 eb160
  · exact indexOk208.1
  · exact indexOk208.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup208
  · exact lookup160
  · rfl
  · rfl
  · exact threshold208
  · exact threshold160
  · exact coeff111.1
  · exact coeff111.2

private def ep112 : LowerEarlyTerminalPair := ⟨159,214,(80520785579819585924587073354965488320247861/208621348812800000000000000000000000000000000)⟩
private theorem coeff112 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb214.threshold) earlyRect) i j)
      ep112.coefficientLower) ∧ 0 < ep112.coefficientLower := by
  have hq : 0 < ep112.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid112 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep112 := by
  apply explicit_pair_valid 159 214 ep112.coefficientLower eb159 eb214
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk214.1
  · exact indexOk214.2
  · exact lookup159
  · exact lookup214
  · rfl
  · rfl
  · exact threshold159
  · exact threshold214
  · exact coeff112.1
  · exact coeff112.2

private def ep113 : LowerEarlyTerminalPair := ⟨159,216,(1174610521840933898038211023532743662758091/3836487424000000000000000000000000000000000)⟩
private theorem coeff113 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb216.threshold) earlyRect) i j)
      ep113.coefficientLower) ∧ 0 < ep113.coefficientLower := by
  have hq : 0 < ep113.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid113 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep113 := by
  apply explicit_pair_valid 159 216 ep113.coefficientLower eb159 eb216
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk216.1
  · exact indexOk216.2
  · exact lookup159
  · exact lookup216
  · rfl
  · rfl
  · exact threshold159
  · exact threshold216
  · exact coeff113.1
  · exact coeff113.2

private def ep114 : LowerEarlyTerminalPair := ⟨159,215,(21794591047503342368414272050813312677576757/97492468480000000000000000000000000000000000)⟩
private theorem coeff114 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb215.threshold) earlyRect) i j)
      ep114.coefficientLower) ∧ 0 < ep114.coefficientLower := by
  have hq : 0 < ep114.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid114 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep114 := by
  apply explicit_pair_valid 159 215 ep114.coefficientLower eb159 eb215
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk215.1
  · exact indexOk215.2
  · exact lookup159
  · exact lookup215
  · rfl
  · rfl
  · exact threshold159
  · exact threshold215
  · exact coeff114.1
  · exact coeff114.2

private def ep115 : LowerEarlyTerminalPair := ⟨159,223,(875063490684436262919077203039769120189109/4257578547200000000000000000000000000000000)⟩
private theorem coeff115 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb223.threshold) earlyRect) i j)
      ep115.coefficientLower) ∧ 0 < ep115.coefficientLower := by
  have hq : 0 < ep115.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid115 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep115 := by
  apply explicit_pair_valid 159 223 ep115.coefficientLower eb159 eb223
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk223.1
  · exact indexOk223.2
  · exact lookup159
  · exact lookup223
  · rfl
  · rfl
  · exact threshold159
  · exact threshold223
  · exact coeff115.1
  · exact coeff115.2

private def ep116 : LowerEarlyTerminalPair := ⟨159,226,(483932975619313271263592288030372894967457557/2534804180480000000000000000000000000000000000)⟩
private theorem coeff116 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb226.threshold) earlyRect) i j)
      ep116.coefficientLower) ∧ 0 < ep116.coefficientLower := by
  have hq : 0 < ep116.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid116 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep116 := by
  apply explicit_pair_valid 159 226 ep116.coefficientLower eb159 eb226
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk226.1
  · exact indexOk226.2
  · exact lookup159
  · exact lookup226
  · rfl
  · rfl
  · exact threshold159
  · exact threshold226
  · exact coeff116.1
  · exact coeff116.2

private def ep117 : LowerEarlyTerminalPair := ⟨229,214,(60641849195284495441989819445506367866073/103245121700000000000000000000000000000000)⟩
private theorem coeff117 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb229.threshold eb214.threshold) earlyRect) i j)
      ep117.coefficientLower) ∧ 0 < ep117.coefficientLower := by
  have hq : 0 < ep117.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid117 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep117 := by
  apply explicit_pair_valid 229 214 ep117.coefficientLower eb229 eb214
  · exact indexOk229.1
  · exact indexOk229.2
  · exact indexOk214.1
  · exact indexOk214.2
  · exact lookup229
  · exact lookup214
  · rfl
  · rfl
  · exact threshold229
  · exact threshold214
  · exact coeff117.1
  · exact coeff117.2

private def ep118 : LowerEarlyTerminalPair := ⟨229,216,(17820035339807039449559956708237298013781/35124997250000000000000000000000000000000)⟩
private theorem coeff118 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb229.threshold eb216.threshold) earlyRect) i j)
      ep118.coefficientLower) ∧ 0 < ep118.coefficientLower := by
  have hq : 0 < ep118.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid118 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep118 := by
  apply explicit_pair_valid 229 216 ep118.coefficientLower eb229 eb216
  · exact indexOk229.1
  · exact indexOk229.2
  · exact indexOk216.1
  · exact indexOk216.2
  · exact lookup229
  · exact lookup216
  · rfl
  · rfl
  · exact threshold229
  · exact threshold216
  · exact coeff118.1
  · exact coeff118.2

private def ep119 : LowerEarlyTerminalPair := ⟨229,215,(77538079855121451872200409846704079682418617/182803092736000000000000000000000000000000000)⟩
private theorem coeff119 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb229.threshold eb215.threshold) earlyRect) i j)
      ep119.coefficientLower) ∧ 0 < ep119.coefficientLower := by
  have hq : 0 < ep119.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid119 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep119 := by
  apply explicit_pair_valid 229 215 ep119.coefficientLower eb229 eb215
  · exact indexOk229.1
  · exact indexOk229.2
  · exact indexOk215.1
  · exact indexOk215.2
  · exact lookup229
  · exact lookup215
  · rfl
  · rfl
  · exact threshold229
  · exact threshold215
  · exact coeff119.1
  · exact coeff119.2

private def ep120 : LowerEarlyTerminalPair := ⟨229,223,(791698191220744020003166808113651484009641/1949015052500000000000000000000000000000000)⟩
private theorem coeff120 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb229.threshold eb223.threshold) earlyRect) i j)
      ep120.coefficientLower) ∧ 0 < ep120.coefficientLower := by
  have hq : 0 < ep120.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid120 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep120 := by
  apply explicit_pair_valid 229 223 ep120.coefficientLower eb229 eb223
  · exact indexOk229.1
  · exact indexOk229.2
  · exact indexOk223.1
  · exact indexOk223.2
  · exact lookup229
  · exact lookup223
  · rfl
  · rfl
  · exact threshold229
  · exact threshold223
  · exact coeff120.1
  · exact coeff120.2

end EarlyCompact16Pairs10

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs11
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep121 : LowerEarlyTerminalPair := ⟨230,214,(1414849593430612623578855775218427589762483/3549272297984000000000000000000000000000000)⟩
private theorem coeff121 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb230.threshold eb214.threshold) earlyRect) i j)
      ep121.coefficientLower) ∧ 0 < ep121.coefficientLower := by
  have hq : 0 < ep121.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid121 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep121 := by
  apply explicit_pair_valid 230 214 ep121.coefficientLower eb230 eb214
  · exact indexOk230.1
  · exact indexOk230.2
  · exact indexOk214.1
  · exact indexOk214.2
  · exact lookup230
  · exact lookup214
  · rfl
  · rfl
  · exact threshold230
  · exact threshold214
  · exact coeff121.1
  · exact coeff121.2

private def ep122 : LowerEarlyTerminalPair := ⟨230,216,(1039764629818985340605512635768619922987/3263505536000000000000000000000000000000)⟩
private theorem coeff122 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb230.threshold eb216.threshold) earlyRect) i j)
      ep122.coefficientLower) ∧ 0 < ep122.coefficientLower := by
  have hq : 0 < ep122.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid122 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep122 := by
  apply explicit_pair_valid 230 216 ep122.coefficientLower eb230 eb216
  · exact indexOk230.1
  · exact indexOk230.2
  · exact indexOk216.1
  · exact indexOk216.2
  · exact lookup230
  · exact lookup216
  · rfl
  · rfl
  · exact threshold230
  · exact threshold216
  · exact coeff122.1
  · exact coeff122.2

private def ep123 : LowerEarlyTerminalPair := ⟨230,231,(5260780330360391628865409429802585253918899/27928092104704000000000000000000000000000000)⟩
private theorem coeff123 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb230.threshold eb231.threshold) earlyRect) i j)
      ep123.coefficientLower) ∧ 0 < ep123.coefficientLower := by
  have hq : 0 < ep123.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid123 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep123 := by
  apply explicit_pair_valid 230 231 ep123.coefficientLower eb230 eb231
  · exact indexOk230.1
  · exact indexOk230.2
  · exact indexOk231.1
  · exact indexOk231.2
  · exact lookup230
  · exact lookup231
  · rfl
  · rfl
  · exact threshold230
  · exact threshold231
  · exact coeff123.1
  · exact coeff123.2

private def ep124 : LowerEarlyTerminalPair := ⟨230,223,(551823784204304765408817672332783783288141/2535194498560000000000000000000000000000000)⟩
private theorem coeff124 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb230.threshold eb223.threshold) earlyRect) i j)
      ep124.coefficientLower) ∧ 0 < ep124.coefficientLower := by
  have hq : 0 < ep124.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid124 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep124 := by
  apply explicit_pair_valid 230 223 ep124.coefficientLower eb230 eb223
  · exact indexOk230.1
  · exact indexOk230.2
  · exact indexOk223.1
  · exact indexOk223.2
  · exact lookup230
  · exact lookup223
  · rfl
  · rfl
  · exact threshold230
  · exact threshold223
  · exact coeff124.1
  · exact coeff124.2

private def ep125 : LowerEarlyTerminalPair := ⟨236,160,(1792797711108998517080764091980909625987/303191961600000000000000000000000000000)⟩
private theorem coeff125 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb236.threshold eb160.threshold) earlyRect) i j)
      ep125.coefficientLower) ∧ 0 < ep125.coefficientLower := by
  have hq : 0 < ep125.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid125 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep125 := by
  apply explicit_pair_valid 236 160 ep125.coefficientLower eb236 eb160
  · exact indexOk236.1
  · exact indexOk236.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup236
  · exact lookup160
  · rfl
  · rfl
  · exact threshold236
  · exact threshold160
  · exact coeff125.1
  · exact coeff125.2

private def ep126 : LowerEarlyTerminalPair := ⟨241,160,(243890359946015975222583840209068403891399/47601137971200000000000000000000000000000)⟩
private theorem coeff126 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb241.threshold eb160.threshold) earlyRect) i j)
      ep126.coefficientLower) ∧ 0 < ep126.coefficientLower := by
  have hq : 0 < ep126.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid126 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep126 := by
  apply explicit_pair_valid 241 160 ep126.coefficientLower eb241 eb160
  · exact indexOk241.1
  · exact indexOk241.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup241
  · exact lookup160
  · rfl
  · rfl
  · exact threshold241
  · exact threshold160
  · exact coeff126.1
  · exact coeff126.2

private def ep127 : LowerEarlyTerminalPair := ⟨245,160,(73048480337752732982859638087722016062933/13581538713600000000000000000000000000000)⟩
private theorem coeff127 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb245.threshold eb160.threshold) earlyRect) i j)
      ep127.coefficientLower) ∧ 0 < ep127.coefficientLower := by
  have hq : 0 < ep127.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid127 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep127 := by
  apply explicit_pair_valid 245 160 ep127.coefficientLower eb245 eb160
  · exact indexOk245.1
  · exact indexOk245.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup245
  · exact lookup160
  · rfl
  · rfl
  · exact threshold245
  · exact threshold160
  · exact coeff127.1
  · exact coeff127.2

private def ep128 : LowerEarlyTerminalPair := ⟨247,160,(366390216987531772410250381000404902491/61387110400000000000000000000000000000)⟩
private theorem coeff128 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb247.threshold eb160.threshold) earlyRect) i j)
      ep128.coefficientLower) ∧ 0 < ep128.coefficientLower := by
  have hq : 0 < ep128.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid128 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep128 := by
  apply explicit_pair_valid 247 160 ep128.coefficientLower eb247 eb160
  · exact indexOk247.1
  · exact indexOk247.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup247
  · exact lookup160
  · rfl
  · rfl
  · exact threshold247
  · exact threshold160
  · exact coeff128.1
  · exact coeff128.2

private def ep129 : LowerEarlyTerminalPair := ⟨251,160,(18920858399025546306339291223923540698709/1534677760000000000000000000000000000000)⟩
private theorem coeff129 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb251.threshold eb160.threshold) earlyRect) i j)
      ep129.coefficientLower) ∧ 0 < ep129.coefficientLower := by
  have hq : 0 < ep129.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid129 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep129 := by
  apply explicit_pair_valid 251 160 ep129.coefficientLower eb251 eb160
  · exact indexOk251.1
  · exact indexOk251.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup251
  · exact lookup160
  · rfl
  · rfl
  · exact threshold251
  · exact threshold160
  · exact coeff129.1
  · exact coeff129.2

private def ep130 : LowerEarlyTerminalPair := ⟨252,160,(207235976233720188221604116035030847407/25570406400000000000000000000000000000)⟩
private theorem coeff130 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb252.threshold eb160.threshold) earlyRect) i j)
      ep130.coefficientLower) ∧ 0 < ep130.coefficientLower := by
  have hq : 0 < ep130.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid130 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep130 := by
  apply explicit_pair_valid 252 160 ep130.coefficientLower eb252 eb160
  · exact indexOk252.1
  · exact indexOk252.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup252
  · exact lookup160
  · rfl
  · rfl
  · exact threshold252
  · exact threshold160
  · exact coeff130.1
  · exact coeff130.2

private def ep131 : LowerEarlyTerminalPair := ⟨159,258,(144910076767355224339182702890782009971723879/280729894860800000000000000000000000000000000)⟩
private theorem coeff131 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb258.threshold) earlyRect) i j)
      ep131.coefficientLower) ∧ 0 < ep131.coefficientLower := by
  have hq : 0 < ep131.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid131 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep131 := by
  apply explicit_pair_valid 159 258 ep131.coefficientLower eb159 eb258
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk258.1
  · exact indexOk258.2
  · exact lookup159
  · exact lookup258
  · rfl
  · rfl
  · exact threshold159
  · exact threshold258
  · exact coeff131.1
  · exact coeff131.2

private def ep132 : LowerEarlyTerminalPair := ⟨159,260,(1315215095372424842098392035897538896755767/2631554816000000000000000000000000000000000)⟩
private theorem coeff132 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb260.threshold) earlyRect) i j)
      ep132.coefficientLower) ∧ 0 < ep132.coefficientLower := by
  have hq : 0 < ep132.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid132 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep132 := by
  apply explicit_pair_valid 159 260 ep132.coefficientLower eb159 eb260
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk260.1
  · exact indexOk260.2
  · exact lookup159
  · exact lookup260
  · rfl
  · rfl
  · exact threshold159
  · exact threshold260
  · exact coeff132.1
  · exact coeff132.2

end EarlyCompact16Pairs11

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs12
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep133 : LowerEarlyTerminalPair := ⟨159,261,(14717086088108112963401659100045215407390813/30077653760000000000000000000000000000000000)⟩
private theorem coeff133 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb261.threshold) earlyRect) i j)
      ep133.coefficientLower) ∧ 0 < ep133.coefficientLower := by
  have hq : 0 < ep133.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid133 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep133 := by
  apply explicit_pair_valid 159 261 ep133.coefficientLower eb159 eb261
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk261.1
  · exact indexOk261.2
  · exact lookup159
  · exact lookup261
  · rfl
  · rfl
  · exact threshold159
  · exact threshold261
  · exact coeff133.1
  · exact coeff133.2

private def ep134 : LowerEarlyTerminalPair := ⟨159,259,(3105126896353816126530429970526284462362061871/6913571167360000000000000000000000000000000000)⟩
private theorem coeff134 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb259.threshold) earlyRect) i j)
      ep134.coefficientLower) ∧ 0 < ep134.coefficientLower := by
  have hq : 0 < ep134.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid134 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep134 := by
  apply explicit_pair_valid 159 259 ep134.coefficientLower eb159 eb259
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk259.1
  · exact indexOk259.2
  · exact lookup159
  · exact lookup259
  · rfl
  · rfl
  · exact threshold159
  · exact threshold259
  · exact coeff134.1
  · exact coeff134.2

private def ep135 : LowerEarlyTerminalPair := ⟨159,268,(18466598646004023969337202573388947917233777/40104270694400000000000000000000000000000000)⟩
private theorem coeff135 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb268.threshold) earlyRect) i j)
      ep135.coefficientLower) ∧ 0 < ep135.coefficientLower := by
  have hq : 0 < ep135.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid135 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep135 := by
  apply explicit_pair_valid 159 268 ep135.coefficientLower eb159 eb268
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk268.1
  · exact indexOk268.2
  · exact lookup159
  · exact lookup268
  · rfl
  · rfl
  · exact threshold159
  · exact threshold268
  · exact coeff135.1
  · exact coeff135.2

private def ep136 : LowerEarlyTerminalPair := ⟨272,160,(9370697278963996573441502333231335583423/6302891443200000000000000000000000000000)⟩
private theorem coeff136 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb272.threshold eb160.threshold) earlyRect) i j)
      ep136.coefficientLower) ∧ 0 < ep136.coefficientLower := by
  have hq : 0 < ep136.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid136 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep136 := by
  apply explicit_pair_valid 272 160 ep136.coefficientLower eb272 eb160
  · exact indexOk272.1
  · exact indexOk272.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup272
  · exact lookup160
  · rfl
  · rfl
  · exact threshold272
  · exact threshold160
  · exact coeff136.1
  · exact coeff136.2

private def ep137 : LowerEarlyTerminalPair := ⟨280,160,(33526016650478599307394175560795831116479/21876706790400000000000000000000000000000)⟩
private theorem coeff137 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb280.threshold eb160.threshold) earlyRect) i j)
      ep137.coefficientLower) ∧ 0 < ep137.coefficientLower := by
  have hq : 0 < ep137.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid137 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep137 := by
  apply explicit_pair_valid 280 160 ep137.coefficientLower eb280 eb160
  · exact indexOk280.1
  · exact indexOk280.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup280
  · exact lookup160
  · rfl
  · rfl
  · exact threshold280
  · exact threshold160
  · exact coeff137.1
  · exact coeff137.2

private def ep138 : LowerEarlyTerminalPair := ⟨282,160,(12902604897421433617088800666125848493343/3551413440000000000000000000000000000000)⟩
private theorem coeff138 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb282.threshold eb160.threshold) earlyRect) i j)
      ep138.coefficientLower) ∧ 0 < ep138.coefficientLower := by
  have hq : 0 < ep138.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid138 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep138 := by
  apply explicit_pair_valid 282 160 ep138.coefficientLower eb282 eb160
  · exact indexOk282.1
  · exact indexOk282.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup282
  · exact lookup160
  · rfl
  · rfl
  · exact threshold282
  · exact threshold160
  · exact coeff138.1
  · exact coeff138.2

private def ep139 : LowerEarlyTerminalPair := ⟨283,160,(1164230330737625475755472344193392979991/450583203840000000000000000000000000000)⟩
private theorem coeff139 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb283.threshold eb160.threshold) earlyRect) i j)
      ep139.coefficientLower) ∧ 0 < ep139.coefficientLower := by
  have hq : 0 < ep139.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid139 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep139 := by
  apply explicit_pair_valid 283 160 ep139.coefficientLower eb283 eb160
  · exact indexOk283.1
  · exact indexOk283.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup283
  · exact lookup160
  · rfl
  · rfl
  · exact threshold283
  · exact threshold160
  · exact coeff139.1
  · exact coeff139.2

private def ep140 : LowerEarlyTerminalPair := ⟨286,160,(4787062552105955660900617708792138283186683/3958215826329600000000000000000000000000000)⟩
private theorem coeff140 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb286.threshold eb160.threshold) earlyRect) i j)
      ep140.coefficientLower) ∧ 0 < ep140.coefficientLower := by
  have hq : 0 < ep140.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid140 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep140 := by
  apply explicit_pair_valid 286 160 ep140.coefficientLower eb286 eb160
  · exact indexOk286.1
  · exact indexOk286.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup286
  · exact lookup160
  · rfl
  · rfl
  · exact threshold286
  · exact threshold160
  · exact coeff140.1
  · exact coeff140.2

private def ep141 : LowerEarlyTerminalPair := ⟨292,160,(10209725084181144370409470240098836001233/7849871237120000000000000000000000000000)⟩
private theorem coeff141 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb292.threshold eb160.threshold) earlyRect) i j)
      ep141.coefficientLower) ∧ 0 < ep141.coefficientLower := by
  have hq : 0 < ep141.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid141 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep141 := by
  apply explicit_pair_valid 292 160 ep141.coefficientLower eb292 eb160
  · exact indexOk292.1
  · exact indexOk292.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup292
  · exact lookup160
  · rfl
  · rfl
  · exact threshold292
  · exact threshold160
  · exact coeff141.1
  · exact coeff141.2

private def ep142 : LowerEarlyTerminalPair := ⟨296,160,(2542769016197777414243547156386400580237/1126458009600000000000000000000000000000)⟩
private theorem coeff142 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb296.threshold eb160.threshold) earlyRect) i j)
      ep142.coefficientLower) ∧ 0 < ep142.coefficientLower := by
  have hq : 0 < ep142.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid142 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep142 := by
  apply explicit_pair_valid 296 160 ep142.coefficientLower eb296 eb160
  · exact indexOk296.1
  · exact indexOk296.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup296
  · exact lookup160
  · rfl
  · rfl
  · exact threshold296
  · exact threshold160
  · exact coeff142.1
  · exact coeff142.2

private def ep143 : LowerEarlyTerminalPair := ⟨159,298,(7491537166424322332588253213712064386487111517/13834083667712000000000000000000000000000000000)⟩
private theorem coeff143 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb298.threshold) earlyRect) i j)
      ep143.coefficientLower) ∧ 0 < ep143.coefficientLower := by
  have hq : 0 < ep143.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid143 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep143 := by
  apply explicit_pair_valid 159 298 ep143.coefficientLower eb159 eb298
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk298.1
  · exact indexOk298.2
  · exact lookup159
  · exact lookup298
  · rfl
  · rfl
  · exact threshold159
  · exact threshold298
  · exact coeff143.1
  · exact coeff143.2

private def ep144 : LowerEarlyTerminalPair := ⟨159,300,(64875482735095941433755230448588011675341173/121988176640000000000000000000000000000000000)⟩
private theorem coeff144 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb300.threshold) earlyRect) i j)
      ep144.coefficientLower) ∧ 0 < ep144.coefficientLower := by
  have hq : 0 < ep144.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid144 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep144 := by
  apply explicit_pair_valid 159 300 ep144.coefficientLower eb159 eb300
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk300.1
  · exact indexOk300.2
  · exact lookup159
  · exact lookup300
  · rfl
  · rfl
  · exact threshold159
  · exact threshold300
  · exact coeff144.1
  · exact coeff144.2

end EarlyCompact16Pairs12

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs13
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep145 : LowerEarlyTerminalPair := ⟨159,301,(17539160476808899816123843013640469373460963/33264689920000000000000000000000000000000000)⟩
private theorem coeff145 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb301.threshold) earlyRect) i j)
      ep145.coefficientLower) ∧ 0 < ep145.coefficientLower := by
  have hq : 0 < ep145.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid145 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep145 := by
  apply explicit_pair_valid 159 301 ep145.coefficientLower eb159 eb301
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk301.1
  · exact indexOk301.2
  · exact lookup159
  · exact lookup301
  · rfl
  · rfl
  · exact threshold159
  · exact threshold301
  · exact coeff145.1
  · exact coeff145.2

private def ep146 : LowerEarlyTerminalPair := ⟨159,299,(5352041485716137301723520465392158519119935661/10629135682880000000000000000000000000000000000)⟩
private theorem coeff146 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb299.threshold) earlyRect) i j)
      ep146.coefficientLower) ∧ 0 < ep146.coefficientLower := by
  have hq : 0 < ep146.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid146 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep146 := by
  apply explicit_pair_valid 159 299 ep146.coefficientLower eb159 eb299
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk299.1
  · exact indexOk299.2
  · exact lookup159
  · exact lookup299
  · rfl
  · rfl
  · exact threshold159
  · exact threshold299
  · exact coeff146.1
  · exact coeff146.2

private def ep147 : LowerEarlyTerminalPair := ⟨159,308,(1006649908496073454928449263673316164827703131/1976297666816000000000000000000000000000000000)⟩
private theorem coeff147 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb308.threshold) earlyRect) i j)
      ep147.coefficientLower) ∧ 0 < ep147.coefficientLower := by
  have hq : 0 < ep147.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid147 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep147 := by
  apply explicit_pair_valid 159 308 ep147.coefficientLower eb159 eb308
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk308.1
  · exact indexOk308.2
  · exact lookup159
  · exact lookup308
  · rfl
  · rfl
  · exact threshold159
  · exact threshold308
  · exact coeff147.1
  · exact coeff147.2

private def ep148 : LowerEarlyTerminalPair := ⟨312,160,(858895511879486348298563552231560007615059/1870085298892800000000000000000000000000000)⟩
private theorem coeff148 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb312.threshold eb160.threshold) earlyRect) i j)
      ep148.coefficientLower) ∧ 0 < ep148.coefficientLower := by
  have hq : 0 < ep148.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid148 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep148 := by
  apply explicit_pair_valid 312 160 ep148.coefficientLower eb312 eb160
  · exact indexOk312.1
  · exact indexOk312.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup312
  · exact lookup160
  · rfl
  · rfl
  · exact threshold312
  · exact threshold160
  · exact coeff148.1
  · exact coeff148.2

private def ep149 : LowerEarlyTerminalPair := ⟨318,160,(29257031721084747428835914384789022459821/53199604550400000000000000000000000000000)⟩
private theorem coeff149 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb318.threshold eb160.threshold) earlyRect) i j)
      ep149.coefficientLower) ∧ 0 < ep149.coefficientLower := by
  have hq : 0 < ep149.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid149 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep149 := by
  apply explicit_pair_valid 318 160 ep149.coefficientLower eb318 eb160
  · exact indexOk318.1
  · exact indexOk318.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup318
  · exact lookup160
  · rfl
  · rfl
  · exact threshold318
  · exact threshold160
  · exact coeff149.1
  · exact coeff149.2

private def ep150 : LowerEarlyTerminalPair := ⟨320,160,(1298311049112558017159502204544596907611029/759994350720000000000000000000000000000000)⟩
private theorem coeff150 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb320.threshold eb160.threshold) earlyRect) i j)
      ep150.coefficientLower) ∧ 0 < ep150.coefficientLower := by
  have hq : 0 < ep150.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid150 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep150 := by
  apply explicit_pair_valid 320 160 ep150.coefficientLower eb320 eb160
  · exact indexOk320.1
  · exact indexOk320.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup320
  · exact lookup160
  · rfl
  · rfl
  · exact threshold320
  · exact threshold160
  · exact coeff150.1
  · exact coeff150.2

private def ep151 : LowerEarlyTerminalPair := ⟨321,160,(110273268730722847386635897309419952651/92080665600000000000000000000000000000)⟩
private theorem coeff151 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb321.threshold eb160.threshold) earlyRect) i j)
      ep151.coefficientLower) ∧ 0 < ep151.coefficientLower := by
  have hq : 0 < ep151.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid151 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep151 := by
  apply explicit_pair_valid 321 160 ep151.coefficientLower eb321 eb160
  · exact indexOk321.1
  · exact indexOk321.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup321
  · exact lookup160
  · rfl
  · rfl
  · exact threshold321
  · exact threshold160
  · exact coeff151.1
  · exact coeff151.2

private def ep152 : LowerEarlyTerminalPair := ⟨324,160,(53179199419531187355840681849385667861/52617523200000000000000000000000000000)⟩
private theorem coeff152 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb324.threshold eb160.threshold) earlyRect) i j)
      ep152.coefficientLower) ∧ 0 < ep152.coefficientLower := by
  have hq : 0 < ep152.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid152 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep152 := by
  apply explicit_pair_valid 324 160 ep152.coefficientLower eb324 eb160
  · exact indexOk324.1
  · exact indexOk324.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup324
  · exact lookup160
  · rfl
  · rfl
  · exact threshold324
  · exact threshold160
  · exact coeff152.1
  · exact coeff152.2

private def ep153 : LowerEarlyTerminalPair := ⟨159,6,(2408930480760071150765525171951070513072911/6856018892800000000000000000000000000000000)⟩
private theorem coeff153 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb6.threshold) earlyRect) i j)
      ep153.coefficientLower) ∧ 0 < ep153.coefficientLower := by
  have hq : 0 < ep153.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid153 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep153 := by
  apply explicit_pair_valid 159 6 ep153.coefficientLower eb159 eb6
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk6.1
  · exact indexOk6.2
  · exact lookup159
  · exact lookup6
  · rfl
  · rfl
  · exact threshold159
  · exact threshold6
  · exact coeff153.1
  · exact coeff153.2

private def ep154 : LowerEarlyTerminalPair := ⟨159,8,(54416363364573002836281354698143533861433/222324889600000000000000000000000000000000)⟩
private theorem coeff154 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb8.threshold) earlyRect) i j)
      ep154.coefficientLower) ∧ 0 < ep154.coefficientLower := by
  have hq : 0 < ep154.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid154 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep154 := by
  apply explicit_pair_valid 159 8 ep154.coefficientLower eb159 eb8
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk8.1
  · exact indexOk8.2
  · exact lookup159
  · exact lookup8
  · rfl
  · rfl
  · exact threshold159
  · exact threshold8
  · exact coeff154.1
  · exact coeff154.2

private def ep155 : LowerEarlyTerminalPair := ⟨159,7,(850608136643133634126788539725259878983621/6508138880000000000000000000000000000000000)⟩
private theorem coeff155 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb7.threshold) earlyRect) i j)
      ep155.coefficientLower) ∧ 0 < ep155.coefficientLower := by
  have hq : 0 < ep155.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid155 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep155 := by
  apply explicit_pair_valid 159 7 ep155.coefficientLower eb159 eb7
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk7.1
  · exact indexOk7.2
  · exact lookup159
  · exact lookup7
  · rfl
  · rfl
  · exact threshold159
  · exact threshold7
  · exact coeff155.1
  · exact coeff155.2

private def ep156 : LowerEarlyTerminalPair := ⟨159,12,(167931481672561848172439374935873444895984731/1861327719680000000000000000000000000000000000)⟩
private theorem coeff156 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb12.threshold) earlyRect) i j)
      ep156.coefficientLower) ∧ 0 < ep156.coefficientLower := by
  have hq : 0 < ep156.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid156 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep156 := by
  apply explicit_pair_valid 159 12 ep156.coefficientLower eb159 eb12
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk12.1
  · exact indexOk12.2
  · exact lookup159
  · exact lookup12
  · rfl
  · rfl
  · exact threshold159
  · exact threshold12
  · exact coeff156.1
  · exact coeff156.2

end EarlyCompact16Pairs13

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs14
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep157 : LowerEarlyTerminalPair := ⟨159,23,(127769463405605533398631718627809258109273/979431270400000000000000000000000000000000)⟩
private theorem coeff157 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb23.threshold) earlyRect) i j)
      ep157.coefficientLower) ∧ 0 < ep157.coefficientLower := by
  have hq : 0 < ep157.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid157 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep157 := by
  apply explicit_pair_valid 159 23 ep157.coefficientLower eb159 eb23
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk23.1
  · exact indexOk23.2
  · exact lookup159
  · exact lookup23
  · rfl
  · rfl
  · exact threshold159
  · exact threshold23
  · exact coeff157.1
  · exact coeff157.2

private def ep158 : LowerEarlyTerminalPair := ⟨28,160,(1082008853360311845068537678492415973/138603520000000000000000000000000000)⟩
private theorem coeff158 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb28.threshold eb160.threshold) earlyRect) i j)
      ep158.coefficientLower) ∧ 0 < ep158.coefficientLower := by
  have hq : 0 < ep158.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid158 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep158 := by
  apply explicit_pair_valid 28 160 ep158.coefficientLower eb28 eb160
  · exact indexOk28.1
  · exact indexOk28.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup28
  · exact lookup160
  · rfl
  · rfl
  · exact threshold28
  · exact threshold160
  · exact coeff158.1
  · exact coeff158.2

private def ep159 : LowerEarlyTerminalPair := ⟨33,160,(318747672144797907549795804175898312539533/43645600768000000000000000000000000000000)⟩
private theorem coeff159 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb33.threshold eb160.threshold) earlyRect) i j)
      ep159.coefficientLower) ∧ 0 < ep159.coefficientLower := by
  have hq : 0 < ep159.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid159 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep159 := by
  apply explicit_pair_valid 33 160 ep159.coefficientLower eb33 eb160
  · exact indexOk33.1
  · exact indexOk33.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup33
  · exact lookup160
  · rfl
  · rfl
  · exact threshold33
  · exact threshold160
  · exact coeff159.1
  · exact coeff159.2

private def ep160 : LowerEarlyTerminalPair := ⟨35,160,(466084528443749938591213438720981045014471/31175429120000000000000000000000000000000)⟩
private theorem coeff160 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb35.threshold eb160.threshold) earlyRect) i j)
      ep160.coefficientLower) ∧ 0 < ep160.coefficientLower := by
  have hq : 0 < ep160.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid160 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep160 := by
  apply explicit_pair_valid 35 160 ep160.coefficientLower eb35 eb160
  · exact indexOk35.1
  · exact indexOk35.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup35
  · exact lookup160
  · rfl
  · rfl
  · exact threshold35
  · exact threshold160
  · exact coeff160.1
  · exact coeff160.2

private def ep161 : LowerEarlyTerminalPair := ⟨36,160,(82072522976687026148552180361196360591/7851008000000000000000000000000000000)⟩
private theorem coeff161 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb36.threshold eb160.threshold) earlyRect) i j)
      ep161.coefficientLower) ∧ 0 < ep161.coefficientLower := by
  have hq : 0 < ep161.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid161 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep161 := by
  apply explicit_pair_valid 36 160 ep161.coefficientLower eb36 eb160
  · exact indexOk36.1
  · exact indexOk36.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup36
  · exact lookup160
  · rfl
  · rfl
  · exact threshold36
  · exact threshold160
  · exact coeff161.1
  · exact coeff161.2

private def ep162 : LowerEarlyTerminalPair := ⟨39,160,(204123119891918940505980210536286766858417/30029838643200000000000000000000000000000)⟩
private theorem coeff162 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb39.threshold eb160.threshold) earlyRect) i j)
      ep162.coefficientLower) ∧ 0 < ep162.coefficientLower := by
  have hq : 0 < ep162.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid162 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep162 := by
  apply explicit_pair_valid 39 160 ep162.coefficientLower eb39 eb160
  · exact indexOk39.1
  · exact indexOk39.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup39
  · exact lookup160
  · rfl
  · rfl
  · exact threshold39
  · exact threshold160
  · exact coeff162.1
  · exact coeff162.2

private def ep163 : LowerEarlyTerminalPair := ⟨45,160,(843088416879115879271825765000731711/119173120000000000000000000000000000)⟩
private theorem coeff163 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb45.threshold eb160.threshold) earlyRect) i j)
      ep163.coefficientLower) ∧ 0 < ep163.coefficientLower := by
  have hq : 0 < ep163.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid163 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep163 := by
  apply explicit_pair_valid 45 160 ep163.coefficientLower eb45 eb160
  · exact indexOk45.1
  · exact indexOk45.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup45
  · exact lookup160
  · rfl
  · rfl
  · exact threshold45
  · exact threshold160
  · exact coeff163.1
  · exact coeff163.2

private def ep164 : LowerEarlyTerminalPair := ⟨159,50,(59684004733869338057329042441722016415536719/155956317440000000000000000000000000000000000)⟩
private theorem coeff164 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb50.threshold) earlyRect) i j)
      ep164.coefficientLower) ∧ 0 < ep164.coefficientLower := by
  have hq : 0 < ep164.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid164 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep164 := by
  apply explicit_pair_valid 159 50 ep164.coefficientLower eb159 eb50
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk50.1
  · exact indexOk50.2
  · exact lookup159
  · exact lookup50
  · rfl
  · rfl
  · exact threshold159
  · exact threshold50
  · exact coeff164.1
  · exact coeff164.2

private def ep165 : LowerEarlyTerminalPair := ⟨159,52,(92755430502848857059591946908509111980419/294747904000000000000000000000000000000000)⟩
private theorem coeff165 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb52.threshold) earlyRect) i j)
      ep165.coefficientLower) ∧ 0 < ep165.coefficientLower := by
  have hq : 0 < ep165.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid165 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep165 := by
  apply explicit_pair_valid 159 52 ep165.coefficientLower eb159 eb52
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk52.1
  · exact indexOk52.2
  · exact lookup159
  · exact lookup52
  · rfl
  · rfl
  · exact threshold159
  · exact threshold52
  · exact coeff165.1
  · exact coeff165.2

private def ep166 : LowerEarlyTerminalPair := ⟨159,53,(61136440608482932335470988981814710828633/222324889600000000000000000000000000000000)⟩
private theorem coeff166 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb53.threshold) earlyRect) i j)
      ep166.coefficientLower) ∧ 0 < ep166.coefficientLower := by
  have hq : 0 < ep166.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid166 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep166 := by
  apply explicit_pair_valid 159 53 ep166.coefficientLower eb159 eb53
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk53.1
  · exact indexOk53.2
  · exact lookup159
  · exact lookup53
  · rfl
  · rfl
  · exact threshold159
  · exact threshold53
  · exact coeff166.1
  · exact coeff166.2

private def ep167 : LowerEarlyTerminalPair := ⟨159,51,(12265727347952799879605580272405578079649831/71589527680000000000000000000000000000000000)⟩
private theorem coeff167 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb51.threshold) earlyRect) i j)
      ep167.coefficientLower) ∧ 0 < ep167.coefficientLower := by
  have hq : 0 < ep167.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid167 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep167 := by
  apply explicit_pair_valid 159 51 ep167.coefficientLower eb159 eb51
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk51.1
  · exact indexOk51.2
  · exact lookup159
  · exact lookup51
  · rfl
  · rfl
  · exact threshold159
  · exact threshold51
  · exact coeff167.1
  · exact coeff167.2

private def ep168 : LowerEarlyTerminalPair := ⟨159,60,(4255305255308398872416552162233353036061017/22279473920000000000000000000000000000000000)⟩
private theorem coeff168 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb60.threshold) earlyRect) i j)
      ep168.coefficientLower) ∧ 0 < ep168.coefficientLower := by
  have hq : 0 < ep168.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid168 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep168 := by
  apply explicit_pair_valid 159 60 ep168.coefficientLower eb159 eb60
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk60.1
  · exact indexOk60.2
  · exact lookup159
  · exact lookup60
  · rfl
  · rfl
  · exact threshold159
  · exact threshold60
  · exact coeff168.1
  · exact coeff168.2

end EarlyCompact16Pairs14

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs15
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep169 : LowerEarlyTerminalPair := ⟨159,66,(247641300971131336857141267124617243021163731/1861327719680000000000000000000000000000000000)⟩
private theorem coeff169 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb66.threshold) earlyRect) i j)
      ep169.coefficientLower) ∧ 0 < ep169.coefficientLower := by
  have hq : 0 < ep169.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid169 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep169 := by
  apply explicit_pair_valid 159 66 ep169.coefficientLower eb159 eb66
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk66.1
  · exact indexOk66.2
  · exact lookup159
  · exact lookup66
  · rfl
  · rfl
  · exact threshold159
  · exact threshold66
  · exact coeff169.1
  · exact coeff169.2

private def ep170 : LowerEarlyTerminalPair := ⟨76,160,(336977690904332973495772997180623079887/47818214400000000000000000000000000000)⟩
private theorem coeff170 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb76.threshold eb160.threshold) earlyRect) i j)
      ep170.coefficientLower) ∧ 0 < ep170.coefficientLower := by
  have hq : 0 < ep170.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid170 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep170 := by
  apply explicit_pair_valid 76 160 ep170.coefficientLower eb76 eb160
  · exact indexOk76.1
  · exact indexOk76.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup76
  · exact lookup160
  · rfl
  · rfl
  · exact threshold76
  · exact threshold160
  · exact coeff170.1
  · exact coeff170.2

private def ep171 : LowerEarlyTerminalPair := ⟨84,160,(24053678190489007772531934175039712139191/3273420057600000000000000000000000000000)⟩
private theorem coeff171 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb84.threshold eb160.threshold) earlyRect) i j)
      ep171.coefficientLower) ∧ 0 < ep171.coefficientLower := by
  have hq : 0 < ep171.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid171 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep171 := by
  apply explicit_pair_valid 84 160 ep171.coefficientLower eb84 eb160
  · exact indexOk84.1
  · exact indexOk84.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup84
  · exact lookup160
  · rfl
  · rfl
  · exact threshold84
  · exact threshold160
  · exact coeff171.1
  · exact coeff171.2

private def ep172 : LowerEarlyTerminalPair := ⟨86,160,(43953729405952594978946445388324718517989/2922696480000000000000000000000000000000)⟩
private theorem coeff172 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb86.threshold eb160.threshold) earlyRect) i j)
      ep172.coefficientLower) ∧ 0 < ep172.coefficientLower := by
  have hq : 0 < ep172.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid172 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep172 := by
  apply explicit_pair_valid 86 160 ep172.coefficientLower eb86 eb160
  · exact indexOk86.1
  · exact indexOk86.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup86
  · exact lookup160
  · rfl
  · rfl
  · exact threshold86
  · exact threshold160
  · exact coeff172.1
  · exact coeff172.2

private def ep173 : LowerEarlyTerminalPair := ⟨87,160,(303810241979150362256077976509430913011/27085977600000000000000000000000000000)⟩
private theorem coeff173 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb87.threshold eb160.threshold) earlyRect) i j)
      ep173.coefficientLower) ∧ 0 < ep173.coefficientLower := by
  have hq : 0 < ep173.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid173 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep173 := by
  apply explicit_pair_valid 87 160 ep173.coefficientLower eb87 eb160
  · exact indexOk87.1
  · exact indexOk87.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup87
  · exact lookup160
  · rfl
  · rfl
  · exact threshold87
  · exact threshold160
  · exact coeff173.1
  · exact coeff173.2

private def ep174 : LowerEarlyTerminalPair := ⟨90,160,(15108744870434350627355395243357883038243/2502486553600000000000000000000000000000)⟩
private theorem coeff174 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb90.threshold eb160.threshold) earlyRect) i j)
      ep174.coefficientLower) ∧ 0 < ep174.coefficientLower := by
  have hq : 0 < ep174.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid174 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep174 := by
  apply explicit_pair_valid 90 160 ep174.coefficientLower eb90 eb160
  · exact indexOk90.1
  · exact indexOk90.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup90
  · exact lookup160
  · rfl
  · rfl
  · exact threshold90
  · exact threshold160
  · exact coeff174.1
  · exact coeff174.2

private def ep175 : LowerEarlyTerminalPair := ⟨96,160,(498065621767012130938275500912605308337/78058393600000000000000000000000000000)⟩
private theorem coeff175 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb96.threshold eb160.threshold) earlyRect) i j)
      ep175.coefficientLower) ∧ 0 < ep175.coefficientLower := by
  have hq : 0 < ep175.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid175 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep175 := by
  apply explicit_pair_valid 96 160 ep175.coefficientLower eb96 eb160
  · exact indexOk96.1
  · exact indexOk96.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup96
  · exact lookup160
  · rfl
  · rfl
  · exact threshold96
  · exact threshold160
  · exact coeff175.1
  · exact coeff175.2

private def ep176 : LowerEarlyTerminalPair := ⟨100,160,(130231373480243801765480397110919681907/13542988800000000000000000000000000000)⟩
private theorem coeff176 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb100.threshold eb160.threshold) earlyRect) i j)
      ep176.coefficientLower) ∧ 0 < ep176.coefficientLower := by
  have hq : 0 < ep176.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid176 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep176 := by
  apply explicit_pair_valid 100 160 ep176.coefficientLower eb100 eb160
  · exact indexOk100.1
  · exact indexOk100.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup100
  · exact lookup160
  · rfl
  · rfl
  · exact threshold100
  · exact threshold160
  · exact coeff176.1
  · exact coeff176.2

private def ep177 : LowerEarlyTerminalPair := ⟨159,101,(198523788958588985583364263607779380660843/1055242496000000000000000000000000000000000)⟩
private theorem coeff177 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb101.threshold) earlyRect) i j)
      ep177.coefficientLower) ∧ 0 < ep177.coefficientLower := by
  have hq : 0 < ep177.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid177 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep177 := by
  apply explicit_pair_valid 159 101 ep177.coefficientLower eb159 eb101
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup159
  · exact lookup101
  · rfl
  · rfl
  · exact threshold159
  · exact threshold101
  · exact coeff177.1
  · exact coeff177.2

private def ep178 : LowerEarlyTerminalPair := ⟨327,101,(19280717852018415531024634341324437747/24774403237500000000000000000000000000)⟩
private theorem coeff178 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb327.threshold eb101.threshold) earlyRect) i j)
      ep178.coefficientLower) ∧ 0 < ep178.coefficientLower := by
  have hq : 0 < ep178.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid178 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep178 := by
  apply explicit_pair_valid 327 101 ep178.coefficientLower eb327 eb101
  · exact indexOk327.1
  · exact indexOk327.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup327
  · exact lookup101
  · rfl
  · rfl
  · exact threshold327
  · exact threshold101
  · exact coeff178.1
  · exact coeff178.2

private def ep179 : LowerEarlyTerminalPair := ⟨329,101,(4647876086393915710222159887810787327187/2477440323750000000000000000000000000000)⟩
private theorem coeff179 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb329.threshold eb101.threshold) earlyRect) i j)
      ep179.coefficientLower) ∧ 0 < ep179.coefficientLower := by
  have hq : 0 < ep179.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid179 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep179 := by
  apply explicit_pair_valid 329 101 ep179.coefficientLower eb329 eb101
  · exact indexOk329.1
  · exact indexOk329.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup329
  · exact lookup101
  · rfl
  · rfl
  · exact threshold329
  · exact threshold101
  · exact coeff179.1
  · exact coeff179.2

private def ep180 : LowerEarlyTerminalPair := ⟨187,101,(90272832802419321441798777900667993967/71948352000000000000000000000000000000)⟩
private theorem coeff180 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb101.threshold) earlyRect) i j)
      ep180.coefficientLower) ∧ 0 < ep180.coefficientLower := by
  have hq : 0 < ep180.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid180 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep180 := by
  apply explicit_pair_valid 187 101 ep180.coefficientLower eb187 eb101
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk101.1
  · exact indexOk101.2
  · exact lookup187
  · exact lookup101
  · rfl
  · rfl
  · exact threshold187
  · exact threshold101
  · exact coeff180.1
  · exact coeff180.2

end EarlyCompact16Pairs15

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs16
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep181 : LowerEarlyTerminalPair := ⟨159,332,(7306443112415920713806042563847053987728857/72653472320000000000000000000000000000000000)⟩
private theorem coeff181 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb332.threshold) earlyRect) i j)
      ep181.coefficientLower) ∧ 0 < ep181.coefficientLower := by
  have hq : 0 < ep181.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid181 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep181 := by
  apply explicit_pair_valid 159 332 ep181.coefficientLower eb159 eb332
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk332.1
  · exact indexOk332.2
  · exact lookup159
  · exact lookup332
  · rfl
  · rfl
  · exact threshold159
  · exact threshold332
  · exact coeff181.1
  · exact coeff181.2

private def ep182 : LowerEarlyTerminalPair := ⟨327,333,(3390337083476618174829635365480795507976611577/4849395511805644800000000000000000000000000000)⟩
private theorem coeff182 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb327.threshold eb333.threshold) earlyRect) i j)
      ep182.coefficientLower) ∧ 0 < ep182.coefficientLower := by
  have hq : 0 < ep182.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid182 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep182 := by
  apply explicit_pair_valid 327 333 ep182.coefficientLower eb327 eb333
  · exact indexOk327.1
  · exact indexOk327.2
  · exact indexOk333.1
  · exact indexOk333.2
  · exact lookup327
  · exact lookup333
  · rfl
  · rfl
  · exact threshold327
  · exact threshold333
  · exact coeff182.1
  · exact coeff182.2

private def ep183 : LowerEarlyTerminalPair := ⟨329,332,(2032326423709755218365324575985537413180834847/1117859534837760000000000000000000000000000000)⟩
private theorem coeff183 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb329.threshold eb332.threshold) earlyRect) i j)
      ep183.coefficientLower) ∧ 0 < ep183.coefficientLower := by
  have hq : 0 < ep183.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid183 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep183 := by
  apply explicit_pair_valid 329 332 ep183.coefficientLower eb329 eb332
  · exact indexOk329.1
  · exact indexOk329.2
  · exact indexOk332.1
  · exact indexOk332.2
  · exact lookup329
  · exact lookup332
  · rfl
  · rfl
  · exact threshold329
  · exact threshold332
  · exact coeff183.1
  · exact coeff183.2

private def ep184 : LowerEarlyTerminalPair := ⟨187,334,(266491885493617567834963734803009366805133/225933996288000000000000000000000000000000)⟩
private theorem coeff184 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb334.threshold) earlyRect) i j)
      ep184.coefficientLower) ∧ 0 < ep184.coefficientLower := by
  have hq : 0 < ep184.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid184 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep184 := by
  apply explicit_pair_valid 187 334 ep184.coefficientLower eb187 eb334
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk334.1
  · exact indexOk334.2
  · exact lookup187
  · exact lookup334
  · rfl
  · rfl
  · exact threshold187
  · exact threshold334
  · exact coeff184.1
  · exact coeff184.2

private def ep185 : LowerEarlyTerminalPair := ⟨114,325,(105872445156155488571751437953024669714331/354599967744000000000000000000000000000000)⟩
private theorem coeff185 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb114.threshold eb325.threshold) earlyRect) i j)
      ep185.coefficientLower) ∧ 0 < ep185.coefficientLower := by
  have hq : 0 < ep185.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid185 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep185 := by
  apply explicit_pair_valid 114 325 ep185.coefficientLower eb114 eb325
  · exact indexOk114.1
  · exact indexOk114.2
  · exact indexOk325.1
  · exact indexOk325.2
  · exact lookup114
  · exact lookup325
  · rfl
  · rfl
  · exact threshold114
  · exact threshold325
  · exact coeff185.1
  · exact coeff185.2

private def ep186 : LowerEarlyTerminalPair := ⟨327,328,(155437190922826373868908949267028130885739859/209317842212864000000000000000000000000000000)⟩
private theorem coeff186 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb327.threshold eb328.threshold) earlyRect) i j)
      ep186.coefficientLower) ∧ 0 < ep186.coefficientLower := by
  have hq : 0 < ep186.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid186 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep186 := by
  apply explicit_pair_valid 327 328 ep186.coefficientLower eb327 eb328
  · exact indexOk327.1
  · exact indexOk327.2
  · exact indexOk328.1
  · exact indexOk328.2
  · exact lookup327
  · exact lookup328
  · rfl
  · rfl
  · exact threshold327
  · exact threshold328
  · exact coeff186.1
  · exact coeff186.2

private def ep187 : LowerEarlyTerminalPair := ⟨329,325,(8002154394968002829567898221510623137766183/4299459749376000000000000000000000000000000)⟩
private theorem coeff187 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb329.threshold eb325.threshold) earlyRect) i j)
      ep187.coefficientLower) ∧ 0 < ep187.coefficientLower := by
  have hq : 0 < ep187.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid187 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep187 := by
  apply explicit_pair_valid 329 325 ep187.coefficientLower eb329 eb325
  · exact indexOk329.1
  · exact indexOk329.2
  · exact indexOk325.1
  · exact indexOk325.2
  · exact lookup329
  · exact lookup325
  · rfl
  · rfl
  · exact threshold329
  · exact threshold325
  · exact coeff187.1
  · exact coeff187.2

private def ep188 : LowerEarlyTerminalPair := ⟨187,331,(34018516625361608365895356518091021845953/27807261081600000000000000000000000000000)⟩
private theorem coeff188 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb331.threshold) earlyRect) i j)
      ep188.coefficientLower) ∧ 0 < ep188.coefficientLower := by
  have hq : 0 < ep188.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid188 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep188 := by
  apply explicit_pair_valid 187 331 ep188.coefficientLower eb187 eb331
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk331.1
  · exact indexOk331.2
  · exact lookup187
  · exact lookup331
  · rfl
  · rfl
  · exact threshold187
  · exact threshold331
  · exact coeff188.1
  · exact coeff188.2

private def ep189 : LowerEarlyTerminalPair := ⟨159,335,(27577907653644296601506565431346666960602807/290613889280000000000000000000000000000000000)⟩
private theorem coeff189 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb335.threshold) earlyRect) i j)
      ep189.coefficientLower) ∧ 0 < ep189.coefficientLower := by
  have hq : 0 < ep189.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid189 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep189 := by
  apply explicit_pair_valid 159 335 ep189.coefficientLower eb159 eb335
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk335.1
  · exact indexOk335.2
  · exact lookup159
  · exact lookup335
  · rfl
  · rfl
  · exact threshold159
  · exact threshold335
  · exact coeff189.1
  · exact coeff189.2

private def ep190 : LowerEarlyTerminalPair := ⟨327,336,(176646440907685957380368304744993866367733997/255106120196928000000000000000000000000000000)⟩
private theorem coeff190 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb327.threshold eb336.threshold) earlyRect) i j)
      ep190.coefficientLower) ∧ 0 < ep190.coefficientLower := by
  have hq : 0 < ep190.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid190 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep190 := by
  apply explicit_pair_valid 327 336 ep190.coefficientLower eb327 eb336
  · exact indexOk327.1
  · exact indexOk327.2
  · exact indexOk336.1
  · exact indexOk336.2
  · exact lookup327
  · exact lookup336
  · rfl
  · rfl
  · exact threshold327
  · exact threshold336
  · exact coeff190.1
  · exact coeff190.2

private def ep191 : LowerEarlyTerminalPair := ⟨329,335,(1316597369217834503000689123458245071888089/727773134660000000000000000000000000000000)⟩
private theorem coeff191 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb329.threshold eb335.threshold) earlyRect) i j)
      ep191.coefficientLower) ∧ 0 < ep191.coefficientLower := by
  have hq : 0 < ep191.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid191 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep191 := by
  apply explicit_pair_valid 329 335 ep191.coefficientLower eb329 eb335
  · exact indexOk329.1
  · exact indexOk329.2
  · exact indexOk335.1
  · exact indexOk335.2
  · exact lookup329
  · exact lookup335
  · rfl
  · rfl
  · exact threshold329
  · exact threshold335
  · exact coeff191.1
  · exact coeff191.2

private def ep192 : LowerEarlyTerminalPair := ⟨187,337,(61123423014503109797973939387079012253717/52138614528000000000000000000000000000000)⟩
private theorem coeff192 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb337.threshold) earlyRect) i j)
      ep192.coefficientLower) ∧ 0 < ep192.coefficientLower := by
  have hq : 0 < ep192.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid192 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep192 := by
  apply explicit_pair_valid 187 337 ep192.coefficientLower eb187 eb337
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk337.1
  · exact indexOk337.2
  · exact lookup187
  · exact lookup337
  · rfl
  · rfl
  · exact threshold187
  · exact threshold337
  · exact coeff192.1
  · exact coeff192.2

end EarlyCompact16Pairs16

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs17
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep193 : LowerEarlyTerminalPair := ⟨338,160,(8687283258218840422430600117099899041367/10801780940800000000000000000000000000000)⟩
private theorem coeff193 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb338.threshold eb160.threshold) earlyRect) i j)
      ep193.coefficientLower) ∧ 0 < ep193.coefficientLower := by
  have hq : 0 < ep193.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid193 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep193 := by
  apply explicit_pair_valid 338 160 ep193.coefficientLower eb338 eb160
  · exact indexOk338.1
  · exact indexOk338.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup338
  · exact lookup160
  · rfl
  · rfl
  · exact threshold338
  · exact threshold160
  · exact coeff193.1
  · exact coeff193.2

private def ep194 : LowerEarlyTerminalPair := ⟨340,160,(43424020679178876922512188708419378192703/55761591705600000000000000000000000000000)⟩
private theorem coeff194 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb340.threshold eb160.threshold) earlyRect) i j)
      ep194.coefficientLower) ∧ 0 < ep194.coefficientLower := by
  have hq : 0 < ep194.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid194 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep194 := by
  apply explicit_pair_valid 340 160 ep194.coefficientLower eb340 eb160
  · exact indexOk340.1
  · exact indexOk340.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup340
  · exact lookup160
  · rfl
  · rfl
  · exact threshold340
  · exact threshold160
  · exact coeff194.1
  · exact coeff194.2

private def ep195 : LowerEarlyTerminalPair := ⟨342,160,(5190963962831727696529593387055821270471/3069355520000000000000000000000000000000)⟩
private theorem coeff195 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb342.threshold eb160.threshold) earlyRect) i j)
      ep195.coefficientLower) ∧ 0 < ep195.coefficientLower := by
  have hq : 0 < ep195.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid195 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep195 := by
  apply explicit_pair_valid 342 160 ep195.coefficientLower eb342 eb160
  · exact indexOk342.1
  · exact indexOk342.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup342
  · exact lookup160
  · rfl
  · rfl
  · exact threshold342
  · exact threshold160
  · exact coeff195.1
  · exact coeff195.2

private def ep196 : LowerEarlyTerminalPair := ⟨187,160,(128186834385502625834362315638879634261/127852032000000000000000000000000000000)⟩
private theorem coeff196 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb160.threshold) earlyRect) i j)
      ep196.coefficientLower) ∧ 0 < ep196.coefficientLower := by
  have hq : 0 < ep196.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid196 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep196 := by
  apply explicit_pair_valid 187 160 ep196.coefficientLower eb187 eb160
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup187
  · exact lookup160
  · rfl
  · rfl
  · exact threshold187
  · exact threshold160
  · exact coeff196.1
  · exact coeff196.2

private def ep197 : LowerEarlyTerminalPair := ⟨345,346,(10138845471659839685272317568045525614062867/15060433536512000000000000000000000000000000)⟩
private theorem coeff197 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb345.threshold eb346.threshold) earlyRect) i j)
      ep197.coefficientLower) ∧ 0 < ep197.coefficientLower := by
  have hq : 0 < ep197.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid197 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep197 := by
  apply explicit_pair_valid 345 346 ep197.coefficientLower eb345 eb346
  · exact indexOk345.1
  · exact indexOk345.2
  · exact indexOk346.1
  · exact indexOk346.2
  · exact lookup345
  · exact lookup346
  · rfl
  · rfl
  · exact threshold345
  · exact threshold346
  · exact coeff197.1
  · exact coeff197.2

private def ep198 : LowerEarlyTerminalPair := ⟨347,217,(1490024313106769379856191435042362688002893/3861399294976000000000000000000000000000000)⟩
private theorem coeff198 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb347.threshold eb217.threshold) earlyRect) i j)
      ep198.coefficientLower) ∧ 0 < ep198.coefficientLower := by
  have hq : 0 < ep198.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid198 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep198 := by
  apply explicit_pair_valid 347 217 ep198.coefficientLower eb347 eb217
  · exact indexOk347.1
  · exact indexOk347.2
  · exact indexOk217.1
  · exact indexOk217.2
  · exact lookup347
  · exact lookup217
  · rfl
  · rfl
  · exact threshold347
  · exact threshold217
  · exact coeff198.1
  · exact coeff198.2

private def ep199 : LowerEarlyTerminalPair := ⟨345,160,(135613897734850862305916339865699886051/303191961600000000000000000000000000000)⟩
private theorem coeff199 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb345.threshold eb160.threshold) earlyRect) i j)
      ep199.coefficientLower) ∧ 0 < ep199.coefficientLower := by
  have hq : 0 < ep199.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid199 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep199 := by
  apply explicit_pair_valid 345 160 ep199.coefficientLower eb345 eb160
  · exact indexOk345.1
  · exact indexOk345.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup345
  · exact lookup160
  · rfl
  · rfl
  · exact threshold345
  · exact threshold160
  · exact coeff199.1
  · exact coeff199.2

private def ep200 : LowerEarlyTerminalPair := ⟨350,160,(147107917092085671378156592519659270273/411561779200000000000000000000000000000)⟩
private theorem coeff200 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb350.threshold eb160.threshold) earlyRect) i j)
      ep200.coefficientLower) ∧ 0 < ep200.coefficientLower := by
  have hq : 0 < ep200.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid200 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep200 := by
  apply explicit_pair_valid 350 160 ep200.coefficientLower eb350 eb160
  · exact indexOk350.1
  · exact indexOk350.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup350
  · exact lookup160
  · rfl
  · rfl
  · exact threshold350
  · exact threshold160
  · exact coeff200.1
  · exact coeff200.2

private def ep201 : LowerEarlyTerminalPair := ⟨235,160,(109143059906380221877807898341607995789/127852032000000000000000000000000000000)⟩
private theorem coeff201 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb235.threshold eb160.threshold) earlyRect) i j)
      ep201.coefficientLower) ∧ 0 < ep201.coefficientLower := by
  have hq : 0 < ep201.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid201 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep201 := by
  apply explicit_pair_valid 235 160 ep201.coefficientLower eb235 eb160
  · exact indexOk235.1
  · exact indexOk235.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup235
  · exact lookup160
  · rfl
  · rfl
  · exact threshold235
  · exact threshold160
  · exact coeff201.1
  · exact coeff201.2

private def ep202 : LowerEarlyTerminalPair := ⟨341,346,(2535704148774620851396617399410891826581/3298497543600000000000000000000000000000)⟩
private theorem coeff202 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb341.threshold eb346.threshold) earlyRect) i j)
      ep202.coefficientLower) ∧ 0 < ep202.coefficientLower := by
  have hq : 0 < ep202.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid202 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep202 := by
  apply explicit_pair_valid 341 346 ep202.coefficientLower eb341 eb346
  · exact indexOk341.1
  · exact indexOk341.2
  · exact indexOk346.1
  · exact indexOk346.2
  · exact lookup341
  · exact lookup346
  · rfl
  · rfl
  · exact threshold341
  · exact threshold346
  · exact coeff202.1
  · exact coeff202.2

private def ep203 : LowerEarlyTerminalPair := ⟨341,217,(5603546362556675009653172679888370693807/8963488665600000000000000000000000000000)⟩
private theorem coeff203 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb341.threshold eb217.threshold) earlyRect) i j)
      ep203.coefficientLower) ∧ 0 < ep203.coefficientLower := by
  have hq : 0 < ep203.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid203 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep203 := by
  apply explicit_pair_valid 341 217 ep203.coefficientLower eb341 eb217
  · exact indexOk341.1
  · exact indexOk341.2
  · exact indexOk217.1
  · exact indexOk217.2
  · exact lookup341
  · exact lookup217
  · rfl
  · rfl
  · exact threshold341
  · exact threshold217
  · exact coeff203.1
  · exact coeff203.2

private def ep204 : LowerEarlyTerminalPair := ⟨341,160,(66438539378749975103174454637720331879/122774220800000000000000000000000000000)⟩
private theorem coeff204 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb341.threshold eb160.threshold) earlyRect) i j)
      ep204.coefficientLower) ∧ 0 < ep204.coefficientLower := by
  have hq : 0 < ep204.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid204 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep204 := by
  apply explicit_pair_valid 341 160 ep204.coefficientLower eb341 eb160
  · exact indexOk341.1
  · exact indexOk341.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup341
  · exact lookup160
  · rfl
  · rfl
  · exact threshold341
  · exact threshold160
  · exact coeff204.1
  · exact coeff204.2

end EarlyCompact16Pairs17

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs18
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep205 : LowerEarlyTerminalPair := ⟨342,346,(159356618175306749366293825520743896617219/82462438590000000000000000000000000000000)⟩
private theorem coeff205 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb342.threshold eb346.threshold) earlyRect) i j)
      ep205.coefficientLower) ∧ 0 < ep205.coefficientLower := by
  have hq : 0 < ep205.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid205 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep205 := by
  apply explicit_pair_valid 342 346 ep205.coefficientLower eb342 eb346
  · exact indexOk342.1
  · exact indexOk342.2
  · exact indexOk346.1
  · exact indexOk346.2
  · exact lookup342
  · exact lookup346
  · rfl
  · rfl
  · exact threshold342
  · exact threshold346
  · exact coeff205.1
  · exact coeff205.2

private def ep206 : LowerEarlyTerminalPair := ⟨342,217,(57302721004733105341549416635159401394749/32012459520000000000000000000000000000000)⟩
private theorem coeff206 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb342.threshold eb217.threshold) earlyRect) i j)
      ep206.coefficientLower) ∧ 0 < ep206.coefficientLower := by
  have hq : 0 < ep206.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid206 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep206 := by
  apply explicit_pair_valid 342 217 ep206.coefficientLower eb342 eb217
  · exact indexOk342.1
  · exact indexOk342.2
  · exact indexOk217.1
  · exact indexOk217.2
  · exact lookup342
  · exact lookup217
  · rfl
  · rfl
  · exact threshold342
  · exact threshold217
  · exact coeff206.1
  · exact coeff206.2

private def ep207 : LowerEarlyTerminalPair := ⟨187,346,(1414199688453267791006238002551707981179/1144973298000000000000000000000000000000)⟩
private theorem coeff207 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb346.threshold) earlyRect) i j)
      ep207.coefficientLower) ∧ 0 < ep207.coefficientLower := by
  have hq : 0 < ep207.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid207 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep207 := by
  apply explicit_pair_valid 187 346 ep207.coefficientLower eb187 eb346
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk346.1
  · exact indexOk346.2
  · exact lookup187
  · exact lookup346
  · rfl
  · rfl
  · exact threshold187
  · exact threshold346
  · exact coeff207.1
  · exact coeff207.2

private def ep208 : LowerEarlyTerminalPair := ⟨187,217,(485540366122414128611301617108662674409/444486144000000000000000000000000000000)⟩
private theorem coeff208 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb187.threshold eb217.threshold) earlyRect) i j)
      ep208.coefficientLower) ∧ 0 < ep208.coefficientLower := by
  have hq : 0 < ep208.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid208 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep208 := by
  apply explicit_pair_valid 187 217 ep208.coefficientLower eb187 eb217
  · exact indexOk187.1
  · exact indexOk187.2
  · exact indexOk217.1
  · exact indexOk217.2
  · exact lookup187
  · exact lookup217
  · rfl
  · rfl
  · exact threshold187
  · exact threshold217
  · exact coeff208.1
  · exact coeff208.2

private def ep209 : LowerEarlyTerminalPair := ⟨358,359,(594934492380715908851401523291519902152618033/1119348364266496000000000000000000000000000000)⟩
private theorem coeff209 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb358.threshold eb359.threshold) earlyRect) i j)
      ep209.coefficientLower) ∧ 0 < ep209.coefficientLower := by
  have hq : 0 < ep209.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid209 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep209 := by
  apply explicit_pair_valid 358 359 ep209.coefficientLower eb358 eb359
  · exact indexOk358.1
  · exact indexOk358.2
  · exact indexOk359.1
  · exact indexOk359.2
  · exact lookup358
  · exact lookup359
  · rfl
  · rfl
  · exact threshold358
  · exact threshold359
  · exact coeff209.1
  · exact coeff209.2

private def ep210 : LowerEarlyTerminalPair := ⟨360,257,(13697443267461504728118257541399306667586631/49719481928704000000000000000000000000000000)⟩
private theorem coeff210 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb360.threshold eb257.threshold) earlyRect) i j)
      ep210.coefficientLower) ∧ 0 < ep210.coefficientLower := by
  have hq : 0 < ep210.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid210 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep210 := by
  apply explicit_pair_valid 360 257 ep210.coefficientLower eb360 eb257
  · exact indexOk360.1
  · exact indexOk360.2
  · exact indexOk257.1
  · exact indexOk257.2
  · exact lookup360
  · exact lookup257
  · rfl
  · rfl
  · exact threshold360
  · exact threshold257
  · exact coeff210.1
  · exact coeff210.2

private def ep211 : LowerEarlyTerminalPair := ⟨358,160,(126129534956152616481690066447740148411/552807833600000000000000000000000000000)⟩
private theorem coeff211 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb358.threshold eb160.threshold) earlyRect) i j)
      ep211.coefficientLower) ∧ 0 < ep211.coefficientLower := by
  have hq : 0 < ep211.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid211 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep211 := by
  apply explicit_pair_valid 358 160 ep211.coefficientLower eb358 eb160
  · exact indexOk358.1
  · exact indexOk358.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup358
  · exact lookup160
  · rfl
  · rfl
  · exact threshold358
  · exact threshold160
  · exact coeff211.1
  · exact coeff211.2

private def ep212 : LowerEarlyTerminalPair := ⟨363,160,(1504482983007489622634074648790799469433/10170933555200000000000000000000000000000)⟩
private theorem coeff212 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb363.threshold eb160.threshold) earlyRect) i j)
      ep212.coefficientLower) ∧ 0 < ep212.coefficientLower := by
  have hq : 0 < ep212.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid212 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep212 := by
  apply explicit_pair_valid 363 160 ep212.coefficientLower eb363 eb160
  · exact indexOk363.1
  · exact indexOk363.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup363
  · exact lookup160
  · rfl
  · rfl
  · exact threshold363
  · exact threshold160
  · exact coeff212.1
  · exact coeff212.2

private def ep213 : LowerEarlyTerminalPair := ⟨235,359,(442297776032681742104265418543165933394121/379311543296000000000000000000000000000000)⟩
private theorem coeff213 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb235.threshold eb359.threshold) earlyRect) i j)
      ep213.coefficientLower) ∧ 0 < ep213.coefficientLower := by
  have hq : 0 < ep213.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid213 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep213 := by
  apply explicit_pair_valid 235 359 ep213.coefficientLower eb235 eb359
  · exact indexOk235.1
  · exact indexOk235.2
  · exact indexOk359.1
  · exact indexOk359.2
  · exact lookup235
  · exact lookup359
  · rfl
  · rfl
  · exact threshold235
  · exact threshold359
  · exact coeff213.1
  · exact coeff213.2

private def ep214 : LowerEarlyTerminalPair := ⟨235,257,(1442610732234467219970999625544344298899/1395086336000000000000000000000000000000)⟩
private theorem coeff214 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb235.threshold eb257.threshold) earlyRect) i j)
      ep214.coefficientLower) ∧ 0 < ep214.coefficientLower := by
  have hq : 0 < ep214.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid214 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep214 := by
  apply explicit_pair_valid 235 257 ep214.coefficientLower eb235 eb257
  · exact indexOk235.1
  · exact indexOk235.2
  · exact indexOk257.1
  · exact indexOk257.2
  · exact lookup235
  · exact lookup257
  · rfl
  · rfl
  · exact threshold235
  · exact threshold257
  · exact coeff214.1
  · exact coeff214.2

private def ep215 : LowerEarlyTerminalPair := ⟨366,359,(9945253578904459488601110101037633156617/4268515871200000000000000000000000000000)⟩
private theorem coeff215 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb366.threshold eb359.threshold) earlyRect) i j)
      ep215.coefficientLower) ∧ 0 < ep215.coefficientLower := by
  have hq : 0 < ep215.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid215 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep215 := by
  apply explicit_pair_valid 366 359 ep215.coefficientLower eb366 eb359
  · exact indexOk366.1
  · exact indexOk366.2
  · exact indexOk359.1
  · exact indexOk359.2
  · exact lookup366
  · exact lookup359
  · rfl
  · rfl
  · exact threshold366
  · exact threshold359
  · exact coeff215.1
  · exact coeff215.2

private def ep216 : LowerEarlyTerminalPair := ⟨366,257,(48312407002195379338088869937438650469/21979102880000000000000000000000000000)⟩
private theorem coeff216 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb366.threshold eb257.threshold) earlyRect) i j)
      ep216.coefficientLower) ∧ 0 < ep216.coefficientLower := by
  have hq : 0 < ep216.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid216 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep216 := by
  apply explicit_pair_valid 366 257 ep216.coefficientLower eb366 eb257
  · exact indexOk366.1
  · exact indexOk366.2
  · exact indexOk257.1
  · exact indexOk257.2
  · exact lookup366
  · exact lookup257
  · rfl
  · rfl
  · exact threshold366
  · exact threshold257
  · exact coeff216.1
  · exact coeff216.2

end EarlyCompact16Pairs18

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs19
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep217 : LowerEarlyTerminalPair := ⟨366,160,(1718208168557720395239926585471333307241/859419545600000000000000000000000000000)⟩
private theorem coeff217 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb366.threshold eb160.threshold) earlyRect) i j)
      ep217.coefficientLower) ∧ 0 < ep217.coefficientLower := by
  have hq : 0 < ep217.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid217 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep217 := by
  apply explicit_pair_valid 366 160 ep217.coefficientLower eb366 eb160
  · exact indexOk366.1
  · exact indexOk366.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup366
  · exact lookup160
  · rfl
  · rfl
  · exact threshold366
  · exact threshold160
  · exact coeff217.1
  · exact coeff217.2

private def ep218 : LowerEarlyTerminalPair := ⟨370,359,(524891762960868830950518966938932974343733/106712896780000000000000000000000000000000)⟩
private theorem coeff218 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb370.threshold eb359.threshold) earlyRect) i j)
      ep218.coefficientLower) ∧ 0 < ep218.coefficientLower := by
  have hq : 0 < ep218.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid218 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep218 := by
  apply explicit_pair_valid 370 359 ep218.coefficientLower eb370 eb359
  · exact indexOk370.1
  · exact indexOk370.2
  · exact indexOk359.1
  · exact indexOk359.2
  · exact lookup370
  · exact lookup359
  · rfl
  · rfl
  · exact threshold370
  · exact threshold359
  · exact coeff218.1
  · exact coeff218.2

private def ep219 : LowerEarlyTerminalPair := ⟨370,257,(375849512730643393802047757199590401943/78496796000000000000000000000000000000)⟩
private theorem coeff219 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb370.threshold eb257.threshold) earlyRect) i j)
      ep219.coefficientLower) ∧ 0 < ep219.coefficientLower := by
  have hq : 0 < ep219.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid219 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep219 := by
  apply explicit_pair_valid 370 257 ep219.coefficientLower eb370 eb257
  · exact indexOk370.1
  · exact indexOk370.2
  · exact indexOk257.1
  · exact indexOk257.2
  · exact lookup370
  · exact lookup257
  · rfl
  · rfl
  · exact threshold370
  · exact threshold257
  · exact coeff219.1
  · exact coeff219.2

private def ep220 : LowerEarlyTerminalPair := ⟨370,160,(13962932713177021683153531208106939935587/3069355520000000000000000000000000000000)⟩
private theorem coeff220 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb370.threshold eb160.threshold) earlyRect) i j)
      ep220.coefficientLower) ∧ 0 < ep220.coefficientLower := by
  have hq : 0 < ep220.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid220 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep220 := by
  apply explicit_pair_valid 370 160 ep220.coefficientLower eb370 eb160
  · exact indexOk370.1
  · exact indexOk370.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup370
  · exact lookup160
  · rfl
  · rfl
  · exact threshold370
  · exact threshold160
  · exact coeff220.1
  · exact coeff220.2

private def ep221 : LowerEarlyTerminalPair := ⟨243,359,(1038843054717700552522153336556618113273/296337143200000000000000000000000000000)⟩
private theorem coeff221 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb243.threshold eb359.threshold) earlyRect) i j)
      ep221.coefficientLower) ∧ 0 < ep221.coefficientLower := by
  have hq : 0 < ep221.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid221 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep221 := by
  apply explicit_pair_valid 243 359 ep221.coefficientLower eb243 eb359
  · exact indexOk243.1
  · exact indexOk243.2
  · exact indexOk359.1
  · exact indexOk359.2
  · exact lookup243
  · exact lookup359
  · rfl
  · rfl
  · exact threshold243
  · exact threshold359
  · exact coeff221.1
  · exact coeff221.2

private def ep222 : LowerEarlyTerminalPair := ⟨243,257,(18390470112134476955589880778236128127/5449556000000000000000000000000000000)⟩
private theorem coeff222 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb243.threshold eb257.threshold) earlyRect) i j)
      ep222.coefficientLower) ∧ 0 < ep222.coefficientLower := by
  have hq : 0 < ep222.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid222 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep222 := by
  apply explicit_pair_valid 243 257 ep222.coefficientLower eb243 eb257
  · exact indexOk243.1
  · exact indexOk243.2
  · exact indexOk257.1
  · exact indexOk257.2
  · exact lookup243
  · exact lookup257
  · rfl
  · rfl
  · exact threshold243
  · exact threshold257
  · exact coeff222.1
  · exact coeff222.2

private def ep223 : LowerEarlyTerminalPair := ⟨243,160,(403760656193878920823209440275905283367/127852032000000000000000000000000000000)⟩
private theorem coeff223 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb243.threshold eb160.threshold) earlyRect) i j)
      ep223.coefficientLower) ∧ 0 < ep223.coefficientLower := by
  have hq : 0 < ep223.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid223 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep223 := by
  apply explicit_pair_valid 243 160 ep223.coefficientLower eb243 eb160
  · exact indexOk243.1
  · exact indexOk243.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup243
  · exact lookup160
  · rfl
  · rfl
  · exact threshold243
  · exact threshold160
  · exact coeff223.1
  · exact coeff223.2

private def ep224 : LowerEarlyTerminalPair := ⟨159,375,(542179747887515223639722015523135434822088627/1449496471808000000000000000000000000000000000)⟩
private theorem coeff224 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb375.threshold) earlyRect) i j)
      ep224.coefficientLower) ∧ 0 < ep224.coefficientLower := by
  have hq : 0 < ep224.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid224 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep224 := by
  apply explicit_pair_valid 159 375 ep224.coefficientLower eb159 eb375
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk375.1
  · exact indexOk375.2
  · exact lookup159
  · exact lookup375
  · rfl
  · rfl
  · exact threshold159
  · exact threshold375
  · exact coeff224.1
  · exact coeff224.2

private def ep225 : LowerEarlyTerminalPair := ⟨159,297,(7300197540694981381551531031138516474659/25088645120000000000000000000000000000000)⟩
private theorem coeff225 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb297.threshold) earlyRect) i j)
      ep225.coefficientLower) ∧ 0 < ep225.coefficientLower := by
  have hq : 0 < ep225.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid225 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep225 := by
  apply explicit_pair_valid 159 297 ep225.coefficientLower eb159 eb297
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk297.1
  · exact indexOk297.2
  · exact lookup159
  · exact lookup297
  · rfl
  · rfl
  · exact threshold159
  · exact threshold297
  · exact coeff225.1
  · exact coeff225.2

private def ep226 : LowerEarlyTerminalPair := ⟨159,376,(27632724828400894643002912061714850982194429/136189101620000000000000000000000000000000000)⟩
private theorem coeff226 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb376.threshold) earlyRect) i j)
      ep226.coefficientLower) ∧ 0 < ep226.coefficientLower := by
  have hq : 0 < ep226.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid226 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep226 := by
  apply explicit_pair_valid 159 376 ep226.coefficientLower eb159 eb376
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk376.1
  · exact indexOk376.2
  · exact lookup159
  · exact lookup376
  · rfl
  · rfl
  · exact threshold159
  · exact threshold376
  · exact coeff226.1
  · exact coeff226.2

private def ep227 : LowerEarlyTerminalPair := ⟨159,380,(37536179424899153724179755267223523245633061/207070924544000000000000000000000000000000000)⟩
private theorem coeff227 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb380.threshold) earlyRect) i j)
      ep227.coefficientLower) ∧ 0 < ep227.coefficientLower := by
  have hq : 0 < ep227.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid227 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep227 := by
  apply explicit_pair_valid 159 380 ep227.coefficientLower eb159 eb380
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk380.1
  · exact indexOk380.2
  · exact lookup159
  · exact lookup380
  · rfl
  · rfl
  · exact threshold159
  · exact threshold380
  · exact coeff227.1
  · exact coeff227.2

private def ep228 : LowerEarlyTerminalPair := ⟨159,382,(58211404858887515335687591905148732133297454373/1325435044764160000000000000000000000000000000000)⟩
private theorem coeff228 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb159.threshold eb382.threshold) earlyRect) i j)
      ep228.coefficientLower) ∧ 0 < ep228.coefficientLower := by
  have hq : 0 < ep228.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid228 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep228 := by
  apply explicit_pair_valid 159 382 ep228.coefficientLower eb159 eb382
  · exact indexOk159.1
  · exact indexOk159.2
  · exact indexOk382.1
  · exact indexOk382.2
  · exact lookup159
  · exact lookup382
  · rfl
  · rfl
  · exact threshold159
  · exact threshold382
  · exact coeff228.1
  · exact coeff228.2

end EarlyCompact16Pairs19

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs20
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep229 : LowerEarlyTerminalPair := ⟨27,382,(1032164301929341513821076526708602951749723373/714760716596224000000000000000000000000000000)⟩
private theorem coeff229 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb382.threshold) earlyRect) i j)
      ep229.coefficientLower) ∧ 0 < ep229.coefficientLower := by
  have hq : 0 < ep229.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid229 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep229 := by
  apply explicit_pair_valid 27 382 ep229.coefficientLower eb27 eb382
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk382.1
  · exact indexOk382.2
  · exact lookup27
  · exact lookup382
  · rfl
  · rfl
  · exact threshold27
  · exact threshold382
  · exact coeff229.1
  · exact coeff229.2

private def ep230 : LowerEarlyTerminalPair := ⟨105,383,(20501845526178637906420129282480888271537354012579/7144201533178735872000000000000000000000000000000)⟩
private theorem coeff230 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb105.threshold eb383.threshold) earlyRect) i j)
      ep230.coefficientLower) ∧ 0 < ep230.coefficientLower := by
  have hq : 0 < ep230.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid230 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep230 := by
  apply explicit_pair_valid 105 383 ep230.coefficientLower eb105 eb383
  · exact indexOk105.1
  · exact indexOk105.2
  · exact indexOk383.1
  · exact indexOk383.2
  · exact lookup105
  · exact lookup383
  · rfl
  · rfl
  · exact threshold105
  · exact threshold383
  · exact coeff230.1
  · exact coeff230.2

private def ep231 : LowerEarlyTerminalPair := ⟨107,382,(570455383460918162027410189985964892057477212571/92551001612202240000000000000000000000000000000)⟩
private theorem coeff231 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb107.threshold eb382.threshold) earlyRect) i j)
      ep231.coefficientLower) ∧ 0 < ep231.coefficientLower := by
  have hq : 0 < ep231.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid231 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep231 := by
  apply explicit_pair_valid 107 382 ep231.coefficientLower eb107 eb382
  · exact indexOk107.1
  · exact indexOk107.2
  · exact indexOk382.1
  · exact indexOk382.2
  · exact lookup107
  · exact lookup382
  · rfl
  · rfl
  · exact threshold107
  · exact threshold382
  · exact coeff231.1
  · exact coeff231.2

private def ep232 : LowerEarlyTerminalPair := ⟨43,384,(175560465716679085899665914718210233779481756821/38814614566464512000000000000000000000000000000)⟩
private theorem coeff232 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb43.threshold eb384.threshold) earlyRect) i j)
      ep232.coefficientLower) ∧ 0 < ep232.coefficientLower := by
  have hq : 0 < ep232.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid232 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep232 := by
  apply explicit_pair_valid 43 384 ep232.coefficientLower eb43 eb384
  · exact indexOk43.1
  · exact indexOk43.2
  · exact indexOk384.1
  · exact indexOk384.2
  · exact lookup43
  · exact lookup384
  · rfl
  · rfl
  · exact threshold43
  · exact threshold384
  · exact coeff232.1
  · exact coeff232.2

private def ep233 : LowerEarlyTerminalPair := ⟨385,375,(416410011615376337564275944800144908085103001/340311491963699200000000000000000000000000000)⟩
private theorem coeff233 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb385.threshold eb375.threshold) earlyRect) i j)
      ep233.coefficientLower) ∧ 0 < ep233.coefficientLower := by
  have hq : 0 < ep233.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid233 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep233 := by
  apply explicit_pair_valid 385 375 ep233.coefficientLower eb385 eb375
  · exact indexOk385.1
  · exact indexOk385.2
  · exact indexOk375.1
  · exact indexOk375.2
  · exact lookup385
  · exact lookup375
  · rfl
  · rfl
  · exact threshold385
  · exact threshold375
  · exact coeff233.1
  · exact coeff233.2

private def ep234 : LowerEarlyTerminalPair := ⟨386,297,(31385471953032160902977932147408829161502693/28751976982220800000000000000000000000000000)⟩
private theorem coeff234 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb386.threshold eb297.threshold) earlyRect) i j)
      ep234.coefficientLower) ∧ 0 < ep234.coefficientLower := by
  have hq : 0 < ep234.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid234 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep234 := by
  apply explicit_pair_valid 386 297 ep234.coefficientLower eb386 eb297
  · exact indexOk386.1
  · exact indexOk386.2
  · exact indexOk297.1
  · exact indexOk297.2
  · exact lookup386
  · exact lookup297
  · rfl
  · rfl
  · exact threshold386
  · exact threshold297
  · exact coeff234.1
  · exact coeff234.2

private def ep235 : LowerEarlyTerminalPair := ⟨385,121,(22695924160372612870572823923953964872771553/26494340712448000000000000000000000000000000)⟩
private theorem coeff235 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb385.threshold eb121.threshold) earlyRect) i j)
      ep235.coefficientLower) ∧ 0 < ep235.coefficientLower := by
  have hq : 0 < ep235.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid235 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep235 := by
  apply explicit_pair_valid 385 121 ep235.coefficientLower eb385 eb121
  · exact indexOk385.1
  · exact indexOk385.2
  · exact indexOk121.1
  · exact indexOk121.2
  · exact lookup385
  · exact lookup121
  · rfl
  · rfl
  · exact threshold385
  · exact threshold121
  · exact coeff235.1
  · exact coeff235.2

private def ep236 : LowerEarlyTerminalPair := ⟨387,380,(2265956084260603108363325387769786035954879377/2225644357262592000000000000000000000000000000)⟩
private theorem coeff236 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb387.threshold eb380.threshold) earlyRect) i j)
      ep236.coefficientLower) ∧ 0 < ep236.coefficientLower := by
  have hq : 0 < ep236.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid236 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep236 := by
  apply explicit_pair_valid 387 380 ep236.coefficientLower eb387 eb380
  · exact indexOk387.1
  · exact indexOk387.2
  · exact indexOk380.1
  · exact indexOk380.2
  · exact lookup387
  · exact lookup380
  · rfl
  · rfl
  · exact threshold387
  · exact threshold380
  · exact coeff236.1
  · exact coeff236.2

private def ep237 : LowerEarlyTerminalPair := ⟨388,375,(68334852374479760445708398416583433857984382403/59979900458601984000000000000000000000000000000)⟩
private theorem coeff237 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb388.threshold eb375.threshold) earlyRect) i j)
      ep237.coefficientLower) ∧ 0 < ep237.coefficientLower := by
  have hq : 0 < ep237.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid237 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep237 := by
  apply explicit_pair_valid 388 375 ep237.coefficientLower eb388 eb375
  · exact indexOk388.1
  · exact indexOk388.2
  · exact indexOk375.1
  · exact indexOk375.2
  · exact lookup388
  · exact lookup375
  · rfl
  · rfl
  · exact threshold388
  · exact threshold375
  · exact coeff237.1
  · exact coeff237.2

private def ep238 : LowerEarlyTerminalPair := ⟨389,297,(1152565973037146238515267279984488893041636773/1138151242486988800000000000000000000000000000)⟩
private theorem coeff238 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb389.threshold eb297.threshold) earlyRect) i j)
      ep238.coefficientLower) ∧ 0 < ep238.coefficientLower := by
  have hq : 0 < ep238.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid238 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep238 := by
  apply explicit_pair_valid 389 297 ep238.coefficientLower eb389 eb297
  · exact indexOk389.1
  · exact indexOk389.2
  · exact indexOk297.1
  · exact indexOk297.2
  · exact lookup389
  · exact lookup297
  · rfl
  · rfl
  · exact threshold389
  · exact threshold297
  · exact coeff238.1
  · exact coeff238.2

private def ep239 : LowerEarlyTerminalPair := ⟨388,160,(91300185499217566933689341051982456210371/138560552908800000000000000000000000000000)⟩
private theorem coeff239 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb388.threshold eb160.threshold) earlyRect) i j)
      ep239.coefficientLower) ∧ 0 < ep239.coefficientLower := by
  have hq : 0 < ep239.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid239 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep239 := by
  apply explicit_pair_valid 388 160 ep239.coefficientLower eb388 eb160
  · exact indexOk388.1
  · exact indexOk388.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup388
  · exact lookup160
  · rfl
  · rfl
  · exact threshold388
  · exact threshold160
  · exact coeff239.1
  · exact coeff239.2

private def ep240 : LowerEarlyTerminalPair := ⟨390,380,(33511073765201820728738303212416227479294315561/35864669071317196800000000000000000000000000000)⟩
private theorem coeff240 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb390.threshold eb380.threshold) earlyRect) i j)
      ep240.coefficientLower) ∧ 0 < ep240.coefficientLower := by
  have hq : 0 < ep240.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid240 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep240 := by
  apply explicit_pair_valid 390 380 ep240.coefficientLower eb390 eb380
  · exact indexOk390.1
  · exact indexOk390.2
  · exact indexOk380.1
  · exact indexOk380.2
  · exact lookup390
  · exact lookup380
  · rfl
  · rfl
  · exact threshold390
  · exact threshold380
  · exact coeff240.1
  · exact coeff240.2

end EarlyCompact16Pairs20

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs21
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep241 : LowerEarlyTerminalPair := ⟨385,160,(182249893983760519616864674758164904649/245674739200000000000000000000000000000)⟩
private theorem coeff241 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb385.threshold eb160.threshold) earlyRect) i j)
      ep241.coefficientLower) ∧ 0 < ep241.coefficientLower := by
  have hq : 0 < ep241.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid241 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep241 := by
  apply explicit_pair_valid 385 160 ep241.coefficientLower eb385 eb160
  · exact indexOk385.1
  · exact indexOk385.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup385
  · exact lookup160
  · rfl
  · rfl
  · exact threshold385
  · exact threshold160
  · exact coeff241.1
  · exact coeff241.2

private def ep242 : LowerEarlyTerminalPair := ⟨391,375,(28083935346167515951072277333726755698564772123/23956974889874432000000000000000000000000000000)⟩
private theorem coeff242 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb391.threshold eb375.threshold) earlyRect) i j)
      ep242.coefficientLower) ∧ 0 < ep242.coefficientLower := by
  have hq : 0 < ep242.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid242 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep242 := by
  apply explicit_pair_valid 391 375 ep242.coefficientLower eb391 eb375
  · exact indexOk391.1
  · exact indexOk391.2
  · exact indexOk375.1
  · exact indexOk375.2
  · exact lookup391
  · exact lookup375
  · rfl
  · rfl
  · exact threshold391
  · exact threshold375
  · exact coeff242.1
  · exact coeff242.2

private def ep243 : LowerEarlyTerminalPair := ⟨392,297,(21090314296404984797103141564724512624481253/20240585665287680000000000000000000000000000)⟩
private theorem coeff243 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb392.threshold eb297.threshold) earlyRect) i j)
      ep243.coefficientLower) ∧ 0 < ep243.coefficientLower := by
  have hq : 0 < ep243.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid243 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep243 := by
  apply explicit_pair_valid 392 297 ep243.coefficientLower eb392 eb297
  · exact indexOk392.1
  · exact indexOk392.2
  · exact indexOk297.1
  · exact indexOk297.2
  · exact lookup392
  · exact lookup297
  · rfl
  · rfl
  · exact threshold392
  · exact threshold297
  · exact coeff243.1
  · exact coeff243.2

private def ep244 : LowerEarlyTerminalPair := ⟨391,160,(11646855055382366406515886470467839506253/16843643801600000000000000000000000000000)⟩
private theorem coeff244 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb391.threshold eb160.threshold) earlyRect) i j)
      ep244.coefficientLower) ∧ 0 < ep244.coefficientLower := by
  have hq : 0 < ep244.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid244 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep244 := by
  apply explicit_pair_valid 391 160 ep244.coefficientLower eb391 eb160
  · exact indexOk391.1
  · exact indexOk391.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup391
  · exact lookup160
  · rfl
  · rfl
  · exact threshold391
  · exact threshold160
  · exact coeff244.1
  · exact coeff244.2

private def ep245 : LowerEarlyTerminalPair := ⟨393,380,(484736752326120194102493618367009402083783869987/501373192406145024000000000000000000000000000000)⟩
private theorem coeff245 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb393.threshold eb380.threshold) earlyRect) i j)
      ep245.coefficientLower) ∧ 0 < ep245.coefficientLower := by
  have hq : 0 < ep245.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid245 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep245 := by
  apply explicit_pair_valid 393 380 ep245.coefficientLower eb393 eb380
  · exact indexOk393.1
  · exact indexOk393.2
  · exact indexOk380.1
  · exact indexOk380.2
  · exact lookup393
  · exact lookup380
  · rfl
  · rfl
  · exact threshold393
  · exact threshold380
  · exact coeff245.1
  · exact coeff245.2

private def ep246 : LowerEarlyTerminalPair := ⟨27,375,(5942652851504181026068035960249762234893029/3349983003648000000000000000000000000000000)⟩
private theorem coeff246 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb375.threshold) earlyRect) i j)
      ep246.coefficientLower) ∧ 0 < ep246.coefficientLower := by
  have hq : 0 < ep246.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid246 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep246 := by
  apply explicit_pair_valid 27 375 ep246.coefficientLower eb27 eb375
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk375.1
  · exact indexOk375.2
  · exact lookup27
  · exact lookup375
  · rfl
  · rfl
  · exact threshold27
  · exact threshold375
  · exact coeff246.1
  · exact coeff246.2

private def ep247 : LowerEarlyTerminalPair := ⟨27,297,(19134574320974147332939155689876531119/11324856000000000000000000000000000000)⟩
private theorem coeff247 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb297.threshold) earlyRect) i j)
      ep247.coefficientLower) ∧ 0 < ep247.coefficientLower := by
  have hq : 0 < ep247.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid247 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep247 := by
  apply explicit_pair_valid 27 297 ep247.coefficientLower eb27 eb297
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk297.1
  · exact indexOk297.2
  · exact lookup27
  · exact lookup297
  · rfl
  · rfl
  · exact threshold27
  · exact threshold297
  · exact coeff247.1
  · exact coeff247.2

private def ep248 : LowerEarlyTerminalPair := ⟨27,160,(346943988941844928178944271138194754713/270859776000000000000000000000000000000)⟩
private theorem coeff248 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb160.threshold) earlyRect) i j)
      ep248.coefficientLower) ∧ 0 < ep248.coefficientLower := by
  have hq : 0 < ep248.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid248 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep248 := by
  apply explicit_pair_valid 27 160 ep248.coefficientLower eb27 eb160
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup27
  · exact lookup160
  · rfl
  · rfl
  · exact threshold27
  · exact threshold160
  · exact coeff248.1
  · exact coeff248.2

private def ep249 : LowerEarlyTerminalPair := ⟨27,380,(26421545963012810166944605391463641439152897/16749915018240000000000000000000000000000000)⟩
private theorem coeff249 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb27.threshold eb380.threshold) earlyRect) i j)
      ep249.coefficientLower) ∧ 0 < ep249.coefficientLower := by
  have hq : 0 < ep249.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid249 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep249 := by
  apply explicit_pair_valid 27 380 ep249.coefficientLower eb27 eb380
  · exact indexOk27.1
  · exact indexOk27.2
  · exact indexOk380.1
  · exact indexOk380.2
  · exact lookup27
  · exact lookup380
  · rfl
  · rfl
  · exact threshold27
  · exact threshold380
  · exact coeff249.1
  · exact coeff249.2

private def ep250 : LowerEarlyTerminalPair := ⟨134,160,(3541128618240315513850930741697072995177/7507459660800000000000000000000000000000)⟩
private theorem coeff250 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb134.threshold eb160.threshold) earlyRect) i j)
      ep250.coefficientLower) ∧ 0 < ep250.coefficientLower := by
  have hq : 0 < ep250.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid250 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep250 := by
  apply explicit_pair_valid 134 160 ep250.coefficientLower eb134 eb160
  · exact indexOk134.1
  · exact indexOk134.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup134
  · exact lookup160
  · rfl
  · rfl
  · exact threshold134
  · exact threshold160
  · exact coeff250.1
  · exact coeff250.2

private def ep251 : LowerEarlyTerminalPair := ⟨129,160,(798449688256194078019887373244501958759/1363925024000000000000000000000000000000)⟩
private theorem coeff251 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb129.threshold eb160.threshold) earlyRect) i j)
      ep251.coefficientLower) ∧ 0 < ep251.coefficientLower := by
  have hq : 0 < ep251.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid251 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep251 := by
  apply explicit_pair_valid 129 160 ep251.coefficientLower eb129 eb160
  · exact indexOk129.1
  · exact indexOk129.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup129
  · exact lookup160
  · rfl
  · rfl
  · exact threshold129
  · exact threshold160
  · exact coeff251.1
  · exact coeff251.2

private def ep252 : LowerEarlyTerminalPair := ⟨131,160,(434440105272737208724923962469349089057/243558040000000000000000000000000000000)⟩
private theorem coeff252 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb131.threshold eb160.threshold) earlyRect) i j)
      ep252.coefficientLower) ∧ 0 < ep252.coefficientLower := by
  have hq : 0 < ep252.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid252 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep252 := by
  apply explicit_pair_valid 131 160 ep252.coefficientLower eb131 eb160
  · exact indexOk131.1
  · exact indexOk131.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup131
  · exact lookup160
  · rfl
  · rfl
  · exact threshold131
  · exact threshold160
  · exact coeff252.1
  · exact coeff252.2

end EarlyCompact16Pairs21

open Freiman
open Blockers16Early3Data
namespace EarlyCompact16Pairs22
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def ep253 : LowerEarlyTerminalPair := ⟨75,160,(99864169479843529776874497899846844099/90286592000000000000000000000000000000)⟩
private theorem coeff253 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb75.threshold eb160.threshold) earlyRect) i j)
      ep253.coefficientLower) ∧ 0 < ep253.coefficientLower := by
  have hq : 0 < ep253.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid253 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep253 := by
  apply explicit_pair_valid 75 160 ep253.coefficientLower eb75 eb160
  · exact indexOk75.1
  · exact indexOk75.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup75
  · exact lookup160
  · rfl
  · rfl
  · exact threshold75
  · exact threshold160
  · exact coeff253.1
  · exact coeff253.2

private def ep254 : LowerEarlyTerminalPair := ⟨127,160,(120424964063497721821283906224190614357/191272857600000000000000000000000000000)⟩
private theorem coeff254 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb127.threshold eb160.threshold) earlyRect) i j)
      ep254.coefficientLower) ∧ 0 < ep254.coefficientLower := by
  have hq : 0 < ep254.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid254 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep254 := by
  apply explicit_pair_valid 127 160 ep254.coefficientLower eb127 eb160
  · exact indexOk127.1
  · exact indexOk127.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup127
  · exact lookup160
  · rfl
  · rfl
  · exact threshold127
  · exact threshold160
  · exact coeff254.1
  · exact coeff254.2

private def ep255 : LowerEarlyTerminalPair := ⟨137,160,(11025443345667800990758022347795991449/21288652800000000000000000000000000000)⟩
private theorem coeff255 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb137.threshold eb160.threshold) earlyRect) i j)
      ep255.coefficientLower) ∧ 0 < ep255.coefficientLower := by
  have hq : 0 < ep255.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid255 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep255 := by
  apply explicit_pair_valid 137 160 ep255.coefficientLower eb137 eb160
  · exact indexOk137.1
  · exact indexOk137.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup137
  · exact lookup160
  · rfl
  · rfl
  · exact threshold137
  · exact threshold160
  · exact coeff255.1
  · exact coeff255.2

private def ep256 : LowerEarlyTerminalPair := ⟨140,160,(6219959923190715933268517664551423239/18811865600000000000000000000000000000)⟩
private theorem coeff256 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb140.threshold eb160.threshold) earlyRect) i j)
      ep256.coefficientLower) ∧ 0 < ep256.coefficientLower := by
  have hq : 0 < ep256.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid256 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep256 := by
  apply explicit_pair_valid 140 160 ep256.coefficientLower eb140 eb160
  · exact indexOk140.1
  · exact indexOk140.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup140
  · exact lookup160
  · rfl
  · rfl
  · exact threshold140
  · exact threshold160
  · exact coeff256.1
  · exact coeff256.2

private def ep257 : LowerEarlyTerminalPair := ⟨144,160,(58291159097016984412061436166128808447/249423334400000000000000000000000000000)⟩
private theorem coeff257 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb144.threshold eb160.threshold) earlyRect) i j)
      ep257.coefficientLower) ∧ 0 < ep257.coefficientLower := by
  have hq : 0 < ep257.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid257 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep257 := by
  apply explicit_pair_valid 144 160 ep257.coefficientLower eb144 eb160
  · exact indexOk144.1
  · exact indexOk144.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup144
  · exact lookup160
  · rfl
  · rfl
  · exact threshold144
  · exact threshold160
  · exact coeff257.1
  · exact coeff257.2

private def ep258 : LowerEarlyTerminalPair := ⟨146,160,(113825447092174548738536330471554454791/165158400000000000000000000000000000000)⟩
private theorem coeff258 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb146.threshold eb160.threshold) earlyRect) i j)
      ep258.coefficientLower) ∧ 0 < ep258.coefficientLower := by
  have hq : 0 < ep258.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid258 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep258 := by
  apply explicit_pair_valid 146 160 ep258.coefficientLower eb146 eb160
  · exact indexOk146.1
  · exact indexOk146.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup146
  · exact lookup160
  · rfl
  · rfl
  · exact threshold146
  · exact threshold160
  · exact coeff258.1
  · exact coeff258.2

private def ep259 : LowerEarlyTerminalPair := ⟨147,160,(330745908632963860591491426788145907/971520000000000000000000000000000000)⟩
private theorem coeff259 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb147.threshold eb160.threshold) earlyRect) i j)
      ep259.coefficientLower) ∧ 0 < ep259.coefficientLower := by
  have hq : 0 < ep259.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid259 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep259 := by
  apply explicit_pair_valid 147 160 ep259.coefficientLower eb147 eb160
  · exact indexOk147.1
  · exact indexOk147.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup147
  · exact lookup160
  · rfl
  · rfl
  · exact threshold147
  · exact threshold160
  · exact coeff259.1
  · exact coeff259.2

private def ep260 : LowerEarlyTerminalPair := ⟨150,160,(8163380142492530596712240686197551929673/13253631283200000000000000000000000000000)⟩
private theorem coeff260 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb150.threshold eb160.threshold) earlyRect) i j)
      ep260.coefficientLower) ∧ 0 < ep260.coefficientLower := by
  have hq : 0 < ep260.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid260 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep260 := by
  apply explicit_pair_valid 150 160 ep260.coefficientLower eb150 eb160
  · exact indexOk150.1
  · exact indexOk150.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup150
  · exact lookup160
  · rfl
  · rfl
  · exact threshold150
  · exact threshold160
  · exact coeff260.1
  · exact coeff260.2

private def ep261 : LowerEarlyTerminalPair := ⟨154,160,(87448678411880530424707439489743733881751/47334397440000000000000000000000000000000)⟩
private theorem coeff261 : (∀ i j : Fin 3, certCoefficientBoundValid
    ((certBernsteinCoefficients (certCrossPolynomial eb154.threshold eb160.threshold) earlyRect) i j)
      ep261.coefficientLower) ∧ 0 < ep261.coefficientLower := by
  have hq : 0 < ep261.coefficientLower := by decide +kernel
  refine ⟨?_, hq⟩
  apply coeffsBool_sound _ _ hq
  decide +kernel
private theorem valid261 : lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 ep261 := by
  apply explicit_pair_valid 154 160 ep261.coefficientLower eb154 eb160
  · exact indexOk154.1
  · exact indexOk154.2
  · exact indexOk160.1
  · exact indexOk160.2
  · exact lookup154
  · exact lookup160
  · rfl
  · rfl
  · exact threshold154
  · exact threshold160
  · exact coeff261.1
  · exact coeff261.2

end EarlyCompact16Pairs22

open Freiman

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem solution :
    ∀ p ∈ lowerEarlyTerminalEarly3.pairs,
      lowerEarlyTerminalPairValid lowerEarlyTerminalEarly3 p := by
  intro p hp
  have hlist : lowerEarlyTerminalEarly3.pairs = [
    EarlyCompact16Pairs01.ep001,
    EarlyCompact16Pairs01.ep002,
    EarlyCompact16Pairs01.ep003,
    EarlyCompact16Pairs01.ep004,
    EarlyCompact16Pairs01.ep005,
    EarlyCompact16Pairs01.ep006,
    EarlyCompact16Pairs01.ep007,
    EarlyCompact16Pairs01.ep008,
    EarlyCompact16Pairs01.ep009,
    EarlyCompact16Pairs01.ep010,
    EarlyCompact16Pairs01.ep011,
    EarlyCompact16Pairs01.ep012,
    EarlyCompact16Pairs02.ep013,
    EarlyCompact16Pairs02.ep014,
    EarlyCompact16Pairs02.ep015,
    EarlyCompact16Pairs02.ep016,
    EarlyCompact16Pairs02.ep017,
    EarlyCompact16Pairs02.ep018,
    EarlyCompact16Pairs02.ep019,
    EarlyCompact16Pairs02.ep020,
    EarlyCompact16Pairs02.ep021,
    EarlyCompact16Pairs02.ep022,
    EarlyCompact16Pairs02.ep023,
    EarlyCompact16Pairs02.ep024,
    EarlyCompact16Pairs03.ep025,
    EarlyCompact16Pairs03.ep026,
    EarlyCompact16Pairs03.ep027,
    EarlyCompact16Pairs03.ep028,
    EarlyCompact16Pairs03.ep029,
    EarlyCompact16Pairs03.ep030,
    EarlyCompact16Pairs03.ep031,
    EarlyCompact16Pairs03.ep032,
    EarlyCompact16Pairs03.ep033,
    EarlyCompact16Pairs03.ep034,
    EarlyCompact16Pairs03.ep035,
    EarlyCompact16Pairs03.ep036,
    EarlyCompact16Pairs04.ep037,
    EarlyCompact16Pairs04.ep038,
    EarlyCompact16Pairs04.ep039,
    EarlyCompact16Pairs04.ep040,
    EarlyCompact16Pairs04.ep041,
    EarlyCompact16Pairs04.ep042,
    EarlyCompact16Pairs04.ep043,
    EarlyCompact16Pairs04.ep044,
    EarlyCompact16Pairs04.ep045,
    EarlyCompact16Pairs04.ep046,
    EarlyCompact16Pairs04.ep047,
    EarlyCompact16Pairs04.ep048,
    EarlyCompact16Pairs05.ep049,
    EarlyCompact16Pairs05.ep050,
    EarlyCompact16Pairs05.ep051,
    EarlyCompact16Pairs05.ep052,
    EarlyCompact16Pairs05.ep053,
    EarlyCompact16Pairs05.ep054,
    EarlyCompact16Pairs05.ep055,
    EarlyCompact16Pairs05.ep056,
    EarlyCompact16Pairs05.ep057,
    EarlyCompact16Pairs05.ep058,
    EarlyCompact16Pairs05.ep059,
    EarlyCompact16Pairs05.ep060,
    EarlyCompact16Pairs06.ep061,
    EarlyCompact16Pairs06.ep062,
    EarlyCompact16Pairs06.ep063,
    EarlyCompact16Pairs06.ep064,
    EarlyCompact16Pairs06.ep065,
    EarlyCompact16Pairs06.ep066,
    EarlyCompact16Pairs06.ep067,
    EarlyCompact16Pairs06.ep068,
    EarlyCompact16Pairs06.ep069,
    EarlyCompact16Pairs06.ep070,
    EarlyCompact16Pairs06.ep071,
    EarlyCompact16Pairs06.ep072,
    EarlyCompact16Pairs07.ep073,
    EarlyCompact16Pairs07.ep074,
    EarlyCompact16Pairs07.ep075,
    EarlyCompact16Pairs07.ep076,
    EarlyCompact16Pairs07.ep077,
    EarlyCompact16Pairs07.ep078,
    EarlyCompact16Pairs07.ep079,
    EarlyCompact16Pairs07.ep080,
    EarlyCompact16Pairs07.ep081,
    EarlyCompact16Pairs07.ep082,
    EarlyCompact16Pairs07.ep083,
    EarlyCompact16Pairs07.ep084,
    EarlyCompact16Pairs08.ep085,
    EarlyCompact16Pairs08.ep086,
    EarlyCompact16Pairs08.ep087,
    EarlyCompact16Pairs08.ep088,
    EarlyCompact16Pairs08.ep089,
    EarlyCompact16Pairs08.ep090,
    EarlyCompact16Pairs08.ep091,
    EarlyCompact16Pairs08.ep092,
    EarlyCompact16Pairs08.ep093,
    EarlyCompact16Pairs08.ep094,
    EarlyCompact16Pairs08.ep095,
    EarlyCompact16Pairs08.ep096,
    EarlyCompact16Pairs09.ep097,
    EarlyCompact16Pairs09.ep098,
    EarlyCompact16Pairs09.ep099,
    EarlyCompact16Pairs09.ep100,
    EarlyCompact16Pairs09.ep101,
    EarlyCompact16Pairs09.ep102,
    EarlyCompact16Pairs09.ep103,
    EarlyCompact16Pairs09.ep104,
    EarlyCompact16Pairs09.ep105,
    EarlyCompact16Pairs09.ep106,
    EarlyCompact16Pairs09.ep107,
    EarlyCompact16Pairs09.ep108,
    EarlyCompact16Pairs10.ep109,
    EarlyCompact16Pairs10.ep110,
    EarlyCompact16Pairs10.ep111,
    EarlyCompact16Pairs10.ep112,
    EarlyCompact16Pairs10.ep113,
    EarlyCompact16Pairs10.ep114,
    EarlyCompact16Pairs10.ep115,
    EarlyCompact16Pairs10.ep116,
    EarlyCompact16Pairs10.ep117,
    EarlyCompact16Pairs10.ep118,
    EarlyCompact16Pairs10.ep119,
    EarlyCompact16Pairs10.ep120,
    EarlyCompact16Pairs11.ep121,
    EarlyCompact16Pairs11.ep122,
    EarlyCompact16Pairs11.ep123,
    EarlyCompact16Pairs11.ep124,
    EarlyCompact16Pairs11.ep125,
    EarlyCompact16Pairs11.ep126,
    EarlyCompact16Pairs11.ep127,
    EarlyCompact16Pairs11.ep128,
    EarlyCompact16Pairs11.ep129,
    EarlyCompact16Pairs11.ep130,
    EarlyCompact16Pairs11.ep131,
    EarlyCompact16Pairs11.ep132,
    EarlyCompact16Pairs12.ep133,
    EarlyCompact16Pairs12.ep134,
    EarlyCompact16Pairs12.ep135,
    EarlyCompact16Pairs12.ep136,
    EarlyCompact16Pairs12.ep137,
    EarlyCompact16Pairs12.ep138,
    EarlyCompact16Pairs12.ep139,
    EarlyCompact16Pairs12.ep140,
    EarlyCompact16Pairs12.ep141,
    EarlyCompact16Pairs12.ep142,
    EarlyCompact16Pairs12.ep143,
    EarlyCompact16Pairs12.ep144,
    EarlyCompact16Pairs13.ep145,
    EarlyCompact16Pairs13.ep146,
    EarlyCompact16Pairs13.ep147,
    EarlyCompact16Pairs13.ep148,
    EarlyCompact16Pairs13.ep149,
    EarlyCompact16Pairs13.ep150,
    EarlyCompact16Pairs13.ep151,
    EarlyCompact16Pairs13.ep152,
    EarlyCompact16Pairs13.ep153,
    EarlyCompact16Pairs13.ep154,
    EarlyCompact16Pairs13.ep155,
    EarlyCompact16Pairs13.ep156,
    EarlyCompact16Pairs14.ep157,
    EarlyCompact16Pairs14.ep158,
    EarlyCompact16Pairs14.ep159,
    EarlyCompact16Pairs14.ep160,
    EarlyCompact16Pairs14.ep161,
    EarlyCompact16Pairs14.ep162,
    EarlyCompact16Pairs14.ep163,
    EarlyCompact16Pairs14.ep164,
    EarlyCompact16Pairs14.ep165,
    EarlyCompact16Pairs14.ep166,
    EarlyCompact16Pairs14.ep167,
    EarlyCompact16Pairs14.ep168,
    EarlyCompact16Pairs15.ep169,
    EarlyCompact16Pairs15.ep170,
    EarlyCompact16Pairs15.ep171,
    EarlyCompact16Pairs15.ep172,
    EarlyCompact16Pairs15.ep173,
    EarlyCompact16Pairs15.ep174,
    EarlyCompact16Pairs15.ep175,
    EarlyCompact16Pairs15.ep176,
    EarlyCompact16Pairs15.ep177,
    EarlyCompact16Pairs15.ep178,
    EarlyCompact16Pairs15.ep179,
    EarlyCompact16Pairs15.ep180,
    EarlyCompact16Pairs16.ep181,
    EarlyCompact16Pairs16.ep182,
    EarlyCompact16Pairs16.ep183,
    EarlyCompact16Pairs16.ep184,
    EarlyCompact16Pairs16.ep185,
    EarlyCompact16Pairs16.ep186,
    EarlyCompact16Pairs16.ep187,
    EarlyCompact16Pairs16.ep188,
    EarlyCompact16Pairs16.ep189,
    EarlyCompact16Pairs16.ep190,
    EarlyCompact16Pairs16.ep191,
    EarlyCompact16Pairs16.ep192,
    EarlyCompact16Pairs17.ep193,
    EarlyCompact16Pairs17.ep194,
    EarlyCompact16Pairs17.ep195,
    EarlyCompact16Pairs17.ep196,
    EarlyCompact16Pairs17.ep197,
    EarlyCompact16Pairs17.ep198,
    EarlyCompact16Pairs17.ep199,
    EarlyCompact16Pairs17.ep200,
    EarlyCompact16Pairs17.ep201,
    EarlyCompact16Pairs17.ep202,
    EarlyCompact16Pairs17.ep203,
    EarlyCompact16Pairs17.ep204,
    EarlyCompact16Pairs18.ep205,
    EarlyCompact16Pairs18.ep206,
    EarlyCompact16Pairs18.ep207,
    EarlyCompact16Pairs18.ep208,
    EarlyCompact16Pairs18.ep209,
    EarlyCompact16Pairs18.ep210,
    EarlyCompact16Pairs18.ep211,
    EarlyCompact16Pairs18.ep212,
    EarlyCompact16Pairs18.ep213,
    EarlyCompact16Pairs18.ep214,
    EarlyCompact16Pairs18.ep215,
    EarlyCompact16Pairs18.ep216,
    EarlyCompact16Pairs19.ep217,
    EarlyCompact16Pairs19.ep218,
    EarlyCompact16Pairs19.ep219,
    EarlyCompact16Pairs19.ep220,
    EarlyCompact16Pairs19.ep221,
    EarlyCompact16Pairs19.ep222,
    EarlyCompact16Pairs19.ep223,
    EarlyCompact16Pairs19.ep224,
    EarlyCompact16Pairs19.ep225,
    EarlyCompact16Pairs19.ep226,
    EarlyCompact16Pairs19.ep227,
    EarlyCompact16Pairs19.ep228,
    EarlyCompact16Pairs20.ep229,
    EarlyCompact16Pairs20.ep230,
    EarlyCompact16Pairs20.ep231,
    EarlyCompact16Pairs20.ep232,
    EarlyCompact16Pairs20.ep233,
    EarlyCompact16Pairs20.ep234,
    EarlyCompact16Pairs20.ep235,
    EarlyCompact16Pairs20.ep236,
    EarlyCompact16Pairs20.ep237,
    EarlyCompact16Pairs20.ep238,
    EarlyCompact16Pairs20.ep239,
    EarlyCompact16Pairs20.ep240,
    EarlyCompact16Pairs21.ep241,
    EarlyCompact16Pairs21.ep242,
    EarlyCompact16Pairs21.ep243,
    EarlyCompact16Pairs21.ep244,
    EarlyCompact16Pairs21.ep245,
    EarlyCompact16Pairs21.ep246,
    EarlyCompact16Pairs21.ep247,
    EarlyCompact16Pairs21.ep248,
    EarlyCompact16Pairs21.ep249,
    EarlyCompact16Pairs21.ep250,
    EarlyCompact16Pairs21.ep251,
    EarlyCompact16Pairs21.ep252,
    EarlyCompact16Pairs22.ep253,
    EarlyCompact16Pairs22.ep254,
    EarlyCompact16Pairs22.ep255,
    EarlyCompact16Pairs22.ep256,
    EarlyCompact16Pairs22.ep257,
    EarlyCompact16Pairs22.ep258,
    EarlyCompact16Pairs22.ep259,
    EarlyCompact16Pairs22.ep260,
    EarlyCompact16Pairs22.ep261
    ] := by decide +kernel
  rw [hlist] at hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid001
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid002
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid003
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid004
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid005
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid006
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid007
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid008
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid009
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid010
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid011
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs01.valid012
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid013
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid014
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid015
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid016
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid017
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid018
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid019
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid020
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid021
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid022
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid023
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs02.valid024
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid025
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid026
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid027
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid028
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid029
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid030
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid031
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid032
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid033
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid034
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid035
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs03.valid036
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid037
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid038
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid039
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid040
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid041
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid042
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid043
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid044
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid045
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid046
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid047
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs04.valid048
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid049
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid050
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid051
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid052
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid053
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid054
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid055
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid056
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid057
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid058
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid059
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs05.valid060
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid061
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid062
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid063
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid064
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid065
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid066
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid067
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid068
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid069
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid070
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid071
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs06.valid072
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid073
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid074
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid075
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid076
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid077
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid078
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid079
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid080
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid081
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid082
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid083
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs07.valid084
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid085
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid086
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid087
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid088
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid089
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid090
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid091
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid092
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid093
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid094
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid095
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs08.valid096
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid097
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid098
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid099
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid100
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid101
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid102
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid103
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid104
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid105
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid106
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid107
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs09.valid108
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid109
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid110
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid111
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid112
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid113
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid114
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid115
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid116
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid117
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid118
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid119
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs10.valid120
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid121
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid122
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid123
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid124
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid125
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid126
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid127
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid128
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid129
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid130
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid131
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs11.valid132
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid133
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid134
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid135
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid136
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid137
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid138
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid139
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid140
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid141
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid142
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid143
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs12.valid144
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid145
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid146
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid147
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid148
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid149
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid150
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid151
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid152
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid153
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid154
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid155
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs13.valid156
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid157
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid158
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid159
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid160
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid161
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid162
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid163
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid164
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid165
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid166
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid167
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs14.valid168
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid169
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid170
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid171
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid172
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid173
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid174
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid175
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid176
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid177
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid178
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid179
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs15.valid180
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid181
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid182
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid183
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid184
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid185
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid186
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid187
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid188
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid189
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid190
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid191
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs16.valid192
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid193
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid194
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid195
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid196
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid197
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid198
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid199
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid200
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid201
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid202
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid203
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs17.valid204
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid205
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid206
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid207
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid208
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid209
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid210
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid211
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid212
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid213
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid214
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid215
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs18.valid216
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid217
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid218
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid219
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid220
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid221
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid222
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid223
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid224
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid225
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid226
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid227
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs19.valid228
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid229
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid230
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid231
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid232
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid233
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid234
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid235
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid236
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid237
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid238
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid239
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs20.valid240
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid241
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid242
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid243
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid244
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid245
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid246
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid247
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid248
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid249
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid250
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid251
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs21.valid252
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid253
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid254
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid255
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid256
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid257
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid258
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid259
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid260
  rcases hp with hp | hp
  · subst p
    exact EarlyCompact16Pairs22.valid261
  · simp at hp

#print axioms solution
