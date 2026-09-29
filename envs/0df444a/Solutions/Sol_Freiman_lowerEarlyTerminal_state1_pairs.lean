-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state1_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:13:53.466584+00:00
-- url     : https://prove2.me/submissions/40623d1d-3772-4ab2-9323-cf5a54af49b0

import Definitions.Def_Freiman_lowerEarlyTerminalDataState1
import Mathlib.Tactic

set_option Elab.async false
set_option linter.all false

open Freiman
namespace State1Pairs17
set_option maxRecDepth 262144
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

private def earlyRect : CertRectangle := ⟨(1/2),(4/5),(3/4),(4/5)⟩
private theorem bounds_length : lowerEarlyTerminalState1.bounds.length = 1238 := by decide +kernel



private structure IntField where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

private def scaled (z : IntField) (den : ℤ) : CertField :=
  ⟨(z.a : ℚ) / den, (z.b : ℚ) / den, (z.c : ℚ) / den, (z.d : ℚ) / den⟩

private def numerator (z : IntField) : ℤ :=
  z.a * 10^30 +
    z.b * (if 0 ≤ z.b then 1732050807568877293527446341505 else 1732050807568877293527446341506) +
    z.c * (if 0 ≤ z.c then 2645751311064590590501615753639 else 2645751311064590590501615753640) +
    z.d * (if 0 ≤ z.d then 4582575694955840006588047193728 else 4582575694955840006588047193729)

private theorem lower_scaled (z : IntField) (den : ℤ) (hd : 0 < den) :
    certFieldLower (scaled z den) = (numerator z : ℚ) / ((den * 10^30 : ℤ) : ℚ) := by
  have hdq : (0 : ℚ) < den := by exact_mod_cast hd
  have hb : (0 : ℚ) ≤ (z.b : ℚ) / den ↔ 0 ≤ z.b := by
    rw [le_div_iff₀ hdq, zero_mul]
    norm_cast
  have hc : (0 : ℚ) ≤ (z.c : ℚ) / den ↔ 0 ≤ z.c := by
    rw [le_div_iff₀ hdq, zero_mul]
    norm_cast
  have hz : (0 : ℚ) ≤ (z.d : ℚ) / den ↔ 0 ≤ z.d := by
    rw [le_div_iff₀ hdq, zero_mul]
    norm_cast
  simp only [certFieldLower, scaled, certDirectedTerm, hb, hc, hz,
    certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper,
    certSqrt21Lower, certSqrt21Upper, numerator]
  split_ifs <;> push_cast <;> field_simp <;> ring

private theorem lower_scaled_lt (z : IntField) (den qn qd : ℤ)
    (hd : 0 < den) (hqd : 0 < qd)
    (h : qn * (den * 10^30) < numerator z * qd) :
    (qn : ℚ) / qd < certFieldLower (scaled z den) := by
  rw [lower_scaled z den hd]
  have hqdq : (0 : ℚ) < qd := by exact_mod_cast hqd
  have hD : (0 : ℚ) < ((den * 10^30 : ℤ) : ℚ) := by
    exact_mod_cast (mul_pos hd (by norm_num : (0 : ℤ) < 10^30))
  apply (div_lt_div_iff₀ hqdq hD).2
  exact_mod_cast h

private theorem field_ext {x y : CertField}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) (hd : x.d = y.d) :
    x = y := by
  cases x; cases y; cases ha; cases hb; cases hc; cases hd; rfl

private def mulN (x y : IntField) : IntField :=
  ⟨x.a*y.a+3*x.b*y.b+7*x.c*y.c+21*x.d*y.d,
   x.a*y.b+x.b*y.a+7*x.c*y.d+7*x.d*y.c,
   x.a*y.c+x.c*y.a+3*x.b*y.d+3*x.d*y.b,
   x.a*y.d+x.d*y.a+x.b*y.c+x.c*y.b⟩

private def subN (x y : IntField) (dx dy : ℤ) : IntField :=
  ⟨x.a*dy-y.a*dx, x.b*dy-y.b*dx, x.c*dy-y.c*dx, x.d*dy-y.d*dx⟩

private theorem scaled_mul (x y : IntField) (dx dy : ℤ) (hx : 0 < dx) (hy : 0 < dy) :
    certFieldMul (scaled x dx) (scaled y dy) = scaled (mulN x y) (dx*dy) := by
  have hxq : (0 : ℚ) < dx := by exact_mod_cast hx
  have hyq : (0 : ℚ) < dy := by exact_mod_cast hy
  apply field_ext <;> dsimp [scaled, certFieldMul, mulN] <;>
    push_cast <;> field_simp <;> ring

private theorem scaled_sub (x y : IntField) (dx dy : ℤ) (hx : 0 < dx) (hy : 0 < dy) :
    certFieldSub (scaled x dx) (scaled y dy) = scaled (subN x y dx dy) (dx*dy) := by
  have hxq : (0 : ℚ) < dx := by exact_mod_cast hx
  have hyq : (0 : ℚ) < dy := by exact_mod_cast hy
  apply field_ext <;> dsimp [scaled, certFieldSub, subN] <;>
    push_cast <;> field_simp <;> ring

private def crossN (a x y b u v : IntField) (da dx dy db du dv : ℤ) : IntField :=
  subN (mulN a (mulN x y)) (mulN b (mulN u v)) (da*(dx*dy)) (db*(du*dv))

private theorem cross_scaled_lt (a x y b u v : IntField) (da dx dy db du dv qn qd : ℤ)
    (ha : 0 < da) (hx : 0 < dx) (hy : 0 < dy)
    (hb : 0 < db) (hu : 0 < du) (hv : 0 < dv) (hqd : 0 < qd)
    (h : qn * ((da*(dx*dy)*(db*(du*dv))) * 10^30) <
      numerator (crossN a x y b u v da dx dy db du dv) * qd) :
    (qn : ℚ) / qd < certFieldLower
      (certFieldSub
        (certFieldMul (scaled a da) (certFieldMul (scaled x dx) (scaled y dy)))
        (certFieldMul (scaled b db) (certFieldMul (scaled u du) (scaled v dv)))) := by
  rw [scaled_mul x y dx dy hx hy, scaled_mul u v du dv hu hv,
    scaled_mul a _ da _ ha (mul_pos hx hy), scaled_mul b _ db _ hb (mul_pos hu hv),
    scaled_sub _ _ _ _ (mul_pos ha (mul_pos hx hy)) (mul_pos hb (mul_pos hu hv))]
  exact lower_scaled_lt _ _ _ _ (mul_pos (mul_pos ha (mul_pos hx hy))
    (mul_pos hb (mul_pos hu hv))) hqd h


private theorem blend_sub (a b : ℚ) (v w : Fin 3 → CertField) (i : Fin 3) :
    certQuadBlend a b (fun k => certFieldSub (v k) (w k)) i =
      certFieldSub (certQuadBlend a b v i) (certQuadBlend a b w i) := by
  apply field_ext <;>
    simp only [certQuadBlend, certFieldAdd, certFieldSub, certFieldScale] <;> ring

private theorem blend_mul_left (a b : ℚ) (z : CertField)
    (v : Fin 3 → CertField) (i : Fin 3) :
    certQuadBlend a b (fun k => certFieldMul z (v k)) i =
      certFieldMul z (certQuadBlend a b v i) := by
  apply field_ext <;>
    simp only [certQuadBlend, certFieldAdd, certFieldScale, certFieldMul] <;> ring

private theorem blend_mul_right (a b : ℚ) (v : Fin 3 → CertField)
    (z : CertField) (i : Fin 3) :
    certQuadBlend a b (fun k => certFieldMul (v k) z) i =
      certFieldMul (certQuadBlend a b v i) z := by
  apply field_ext <;>
    simp only [certQuadBlend, certFieldAdd, certFieldScale, certFieldMul] <;> ring

private def productBlend (a b : ℚ) (x y : CertField) : Fin 3 → CertField :=
  certQuadBlend a b (certProductCoefficients x y)

private def factoredCoefficients (l u : CertThreshold) (R : CertRectangle) : CertPoly22 :=
  fun i j => certFieldSub
    (certFieldMul l.c (certFieldMul
      (productBlend R.r0 R.r1 u.x0 u.x1 i)
      (productBlend R.s0 R.s1 l.y0 l.y1 j)))
    (certFieldMul u.c (certFieldMul
      (productBlend R.r0 R.r1 l.x0 l.x1 i)
      (productBlend R.s0 R.s1 u.y0 u.y1 j)))

private theorem bernstein_factored (l u : CertThreshold) (R : CertRectangle) :
    certBernsteinCoefficients (certCrossPolynomial l u) R =
      factoredCoefficients l u R := by
  funext i j
  dsimp only [certBernsteinCoefficients, certCrossPolynomial,
    factoredCoefficients, productBlend]
  delta certCrossPolynomial
  simp only [blend_sub, blend_mul_left, blend_mul_right]


private def addN (x y : IntField) : IntField :=
  ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩

private def smulN (k : ℤ) (x : IntField) : IntField :=
  ⟨k*x.a, k*x.b, k*x.c, k*x.d⟩

private def oneN : IntField := ⟨1,0,0,0⟩

private def blendN (K : ℤ) (E F : Fin 3 → ℤ)
    (x y : IntField) (dx dy : ℤ) (i : Fin 3) : IntField :=
  addN (smulN (K*dx*dy) oneN)
    (addN (smulN (E i) (addN (smulN dy x) (smulN dx y)))
      (smulN (F i) (mulN x y)))

private def sE : Fin 3 → ℤ := ![300,310,320]
private def sF : Fin 3 → ℤ := ![225,240,256]
private def tE : Fin 3 → ℤ := ![50,65,80]
private def tF : Fin 3 → ℤ := ![25,40,64]

private theorem t_blend_scaled (x y : IntField) (dx dy : ℤ)
    (hx : 0 < dx) (hy : 0 < dy) :
    productBlend (1/2) (4/5) (scaled x dx) (scaled y dy) =
      fun i => scaled (blendN 100 tE tF x y dx dy i) (100*dx*dy) := by
  funext i
  fin_cases i <;>
    apply field_ext <;>
    dsimp [productBlend, certQuadBlend, certProductCoefficients, certFieldAdd,
      certFieldScale, certFieldMul, scaled, blendN, addN, smulN, oneN, mulN, tE, tF] <;>
    push_cast <;> field_simp <;> ring

private theorem s_blend_scaled (x y : IntField) (dx dy : ℤ)
    (hx : 0 < dx) (hy : 0 < dy) :
    productBlend (3/4) (4/5) (scaled x dx) (scaled y dy) =
      fun i => scaled (blendN 400 sE sF x y dx dy i) (400*dx*dy) := by
  funext i
  fin_cases i <;>
    apply field_ext <;>
    dsimp [productBlend, certQuadBlend, certProductCoefficients, certFieldAdd,
      certFieldScale, certFieldMul, scaled, blendN, addN, smulN, oneN, mulN, sE, sF] <;>
    push_cast <;> field_simp <;> ring

private theorem all3 (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem cross_scaled_all
    (a b : IntField) (x y u v : Fin 3 → IntField)
    (da db : ℤ) (dx dy du dv : Fin 3 → ℤ) (qn qd : ℤ)
    (ha : 0 < da) (hx : ∀ i, 0 < dx i) (hy : ∀ j, 0 < dy j)
    (hb : 0 < db) (hu : ∀ i, 0 < du i) (hv : ∀ j, 0 < dv j)
    (hqd : 0 < qd)
    (h : ∀ i j, qn * ((da*(dx i*dy j)*(db*(du i*dv j))) * 10^30) <
      numerator (crossN a (x i) (y j) b (u i) (v j)
        da (dx i) (dy j) db (du i) (dv j)) * qd) :
    ∀ i j, (qn : ℚ) / qd < certFieldLower
      (certFieldSub
        (certFieldMul (scaled a da)
          (certFieldMul (scaled (x i) (dx i)) (scaled (y j) (dy j))))
        (certFieldMul (scaled b db)
          (certFieldMul (scaled (u i) (du i)) (scaled (v j) (dv j))))) := by
  intro i j
  exact cross_scaled_lt a (x i) (y j) b (u i) (v j)
    da (dx i) (dy j) db (du i) (dv j) qn qd
    ha (hx i) (hy j) hb (hu i) (hv j) hqd (h i j)

private theorem self_cross_coefficient_valid (t : CertThreshold) (R : CertRectangle)
    (i j : Fin 3) :
    certCoefficientBoundValid
      (certBernsteinCoefficients (certCrossPolynomial t t) R i j) 0 := by
  have hcross : certCrossPolynomial t t = fun _ _ => (⟨0, 0, 0, 0⟩ : CertField) := by
    funext a b
    simp only [certCrossPolynomial, certFieldSub, sub_self]
  rw [hcross]
  simp [certCoefficientBoundValid, certBernsteinCoefficients, certQuadBlend,
    certFieldAdd, certFieldScale, certFieldLower, certDirectedTerm]

private structure BoundKit (lo : Bool) where
  id : ℕ
  b : CertBound
  idpos : 0 < id
  idlen : id ≤ 1238
  lookup : lowerEarlyTerminalBound lowerEarlyTerminalState1 id = b
  orient : b.lower = lo
  thresholdValid : certThresholdDataValid b.threshold
  cn : IntField
  cd : ℤ
  cdpos : 0 < cd
  cscaled : b.threshold.c = scaled cn cd
  xn : Fin 3 → IntField
  xd : Fin 3 → ℤ
  xdpos : ∀ i, 0 < xd i
  xscaled : productBlend (1/2) (4/5) b.threshold.x0 b.threshold.x1 =
    fun i => scaled (xn i) (xd i)
  yn : Fin 3 → IntField
  yd : Fin 3 → ℤ
  ydpos : ∀ i, 0 < yd i
  yscaled : productBlend (3/4) (4/5) b.threshold.y0 b.threshold.y1 =
    fun i => scaled (yn i) (yd i)
private def n1 : IntField := ⟨1703,(-884),0,0⟩
private theorem pos1 : (0:ℤ) < 253 := by decide +kernel
private theorem cp1 : (⟨(1703/253),(-884/253),0,0⟩ : CertField) = scaled n1 253 := by decide +kernel
private def n2 : IntField := ⟨2259915,0,0,130195⟩
private theorem pos2 : (0:ℤ) < 10878294 := by decide +kernel
private theorem cp2 : (⟨(107615/518014),0,0,(130195/10878294)⟩ : CertField) = scaled n2 10878294 := by decide +kernel
private def n3 : IntField := ⟨2835,0,0,1⟩
private theorem pos3 : (0:ℤ) < 6846 := by decide +kernel
private theorem cp3 : (⟨(135/326),0,0,(1/6846)⟩ : CertField) = scaled n3 6846 := by decide +kernel
private def n4 : IntField := ⟨193,0,0,(-1)⟩
private theorem pos4 : (0:ℤ) < 454 := by decide +kernel
private theorem cp4 : (⟨(193/454),0,0,(-1/454)⟩ : CertField) = scaled n4 454 := by decide +kernel
private def n5 : IntField := ⟨9,1,0,0⟩
private theorem pos5 : (0:ℤ) < 39 := by decide +kernel
private theorem cp5 : (⟨(3/13),(1/39),0,0⟩ : CertField) = scaled n5 39 := by decide +kernel
private def n6 : IntField := ⟨4,1,0,0⟩
private theorem pos6 : (0:ℤ) < 13 := by decide +kernel
private theorem cp6 : (⟨(4/13),(1/13),0,0⟩ : CertField) = scaled n6 13 := by decide +kernel
private def n7 : IntField := ⟨30,(-1),0,0⟩
private theorem pos7 : (0:ℤ) < 69 := by decide +kernel
private theorem cp7 : (⟨(10/23),(-1/69),0,0⟩ : CertField) = scaled n7 69 := by decide +kernel
private def n8 : IntField := ⟨5,(-1),0,0⟩
private theorem pos8 : (0:ℤ) < 11 := by decide +kernel
private theorem cp8 : (⟨(5/11),(-1/11),0,0⟩ : CertField) = scaled n8 11 := by decide +kernel
private def n9 : IntField := ⟨725,0,0,1⟩
private theorem pos9 : (0:ℤ) < 2602 := by decide +kernel
private theorem cp9 : (⟨(725/2602),0,0,(1/2602)⟩ : CertField) = scaled n9 2602 := by decide +kernel
private def n10 : IntField := ⟨31,0,0,(-1)⟩
private theorem pos10 : (0:ℤ) < 94 := by decide +kernel
private theorem cp10 : (⟨(31/94),0,0,(-1/94)⟩ : CertField) = scaled n10 94 := by decide +kernel
private def n11 : IntField := ⟨5311383,0,0,171157⟩
private theorem pos11 : (0:ℤ) < 5050050 := by decide +kernel
private theorem cp11 : (⟨(1770461/1683350),0,0,(171157/5050050)⟩ : CertField) = scaled n11 5050050 := by decide +kernel
private def n12 : IntField := ⟨41,0,0,1⟩
private theorem pos12 : (0:ℤ) < 166 := by decide +kernel
private theorem cp12 : (⟨(41/166),0,0,(1/166)⟩ : CertField) = scaled n12 166 := by decide +kernel
private def n13 : IntField := ⟨1851,0,0,(-1)⟩
private theorem pos13 : (0:ℤ) < 6718 := by decide +kernel
private theorem cp13 : (⟨(1851/6718),0,0,(-1/6718)⟩ : CertField) = scaled n13 6718 := by decide +kernel
private def n14 : IntField := ⟨105,0,0,1⟩
private theorem pos14 : (0:ℤ) < 262 := by decide +kernel
private theorem cp14 : (⟨(105/262),0,0,(1/262)⟩ : CertField) = scaled n14 262 := by decide +kernel
private def n15 : IntField := ⟨3231,0,0,(-1)⟩
private theorem pos15 : (0:ℤ) < 7710 := by decide +kernel
private theorem cp15 : (⟨(1077/2570),0,0,(-1/7710)⟩ : CertField) = scaled n15 7710 := by decide +kernel
private def n16 : IntField := ⟨6343,0,0,(-511)⟩
private theorem pos16 : (0:ℤ) < 4454 := by decide +kernel
private theorem cp16 : (⟨(6343/4454),0,0,(-511/4454)⟩ : CertField) = scaled n16 4454 := by decide +kernel
private def n17 : IntField := ⟨19,0,0,(-1)⟩
private theorem pos17 : (0:ℤ) < 34 := by decide +kernel
private theorem cp17 : (⟨(19/34),0,0,(-1/34)⟩ : CertField) = scaled n17 34 := by decide +kernel
private def n18 : IntField := ⟨19833,0,0,(-91)⟩
private theorem pos18 : (0:ℤ) < 50394 := by decide +kernel
private theorem cp18 : (⟨(6611/16798),0,0,(-91/50394)⟩ : CertField) = scaled n18 50394 := by decide +kernel
private def n19 : IntField := ⟨87,0,0,1⟩
private theorem pos19 : (0:ℤ) < 222 := by decide +kernel
private theorem cp19 : (⟨(29/74),0,0,(1/222)⟩ : CertField) = scaled n19 222 := by decide +kernel
private def n20 : IntField := ⟨(-449175),969439,0,0⟩
private theorem pos20 : (0:ℤ) < 2379971 := by decide +kernel
private theorem cp20 : (⟨(-449175/2379971),(969439/2379971),0,0⟩ : CertField) = scaled n20 2379971 := by decide +kernel
private def n21 : IntField := ⟨168,1,0,0⟩
private theorem pos21 : (0:ℤ) < 409 := by decide +kernel
private theorem cp21 : (⟨(168/409),(1/409),0,0⟩ : CertField) = scaled n21 409 := by decide +kernel
private def n22 : IntField := ⟨223,(-1),0,0⟩
private theorem pos22 : (0:ℤ) < 529 := by decide +kernel
private theorem cp22 : (⟨(223/529),(-1/529),0,0⟩ : CertField) = scaled n22 529 := by decide +kernel
private def n23 : IntField := ⟨48,1,0,0⟩
private theorem pos23 : (0:ℤ) < 177 := by decide +kernel
private theorem cp23 : (⟨(16/59),(1/177),0,0⟩ : CertField) = scaled n23 177 := by decide +kernel
private def n24 : IntField := ⟨133,(-1),0,0⟩
private theorem pos24 : (0:ℤ) < 478 := by decide +kernel
private theorem cp24 : (⟨(133/478),(-1/478),0,0⟩ : CertField) = scaled n24 478 := by decide +kernel
private def n25 : IntField := ⟨(-4068621),6005837,0,0⟩
private theorem pos25 : (0:ℤ) < 11250772 := by decide +kernel
private theorem cp25 : (⟨(-4068621/11250772),(6005837/11250772),0,0⟩ : CertField) = scaled n25 11250772 := by decide +kernel
private def n26 : IntField := ⟨1950,(-1),0,0⟩
private theorem pos26 : (0:ℤ) < 7081 := by decide +kernel
private theorem cp26 : (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) = scaled n26 7081 := by decide +kernel
private def n27 : IntField := ⟨(-89774),2123203,0,0⟩
private theorem pos27 : (0:ℤ) < 6105143 := by decide +kernel
private theorem cp27 : (⟨(-89774/6105143),(2123203/6105143),0,0⟩ : CertField) = scaled n27 6105143 := by decide +kernel
private def n28 : IntField := ⟨3411,(-1),0,0⟩
private theorem pos28 : (0:ℤ) < 8142 := by decide +kernel
private theorem cp28 : (⟨(1137/2714),(-1/8142),0,0⟩ : CertField) = scaled n28 8142 := by decide +kernel
private def n29 : IntField := ⟨451983,0,0,26039⟩
private theorem pos29 : (0:ℤ) < 1110030 := by decide +kernel
private theorem cp29 : (⟨(150661/370010),0,0,(26039/1110030)⟩ : CertField) = scaled n29 1110030 := by decide +kernel
private def n30 : IntField := ⟨331431,894529,0,0⟩
private theorem pos30 : (0:ℤ) < 191958 := by decide +kernel
private theorem cp30 : (⟨(110477/63986),(894529/191958),0,0⟩ : CertField) = scaled n30 191958 := by decide +kernel
private def n31 : IntField := ⟨3,(-1),0,0⟩
private theorem pos31 : (0:ℤ) < 2 := by decide +kernel
private theorem cp31 : (⟨(3/2),(-1/2),0,0⟩ : CertField) = scaled n31 2 := by decide +kernel
private def n32 : IntField := ⟨(-1),1,0,0⟩
private theorem pos32 : (0:ℤ) < 2 := by decide +kernel
private theorem cp32 : (⟨(-1/2),(1/2),0,0⟩ : CertField) = scaled n32 2 := by decide +kernel
private def n33 : IntField := ⟨341,1,0,0⟩
private theorem pos33 : (0:ℤ) < 1237 := by decide +kernel
private theorem cp33 : (⟨(341/1237),(1/1237),0,0⟩ : CertField) = scaled n33 1237 := by decide +kernel
private def n34 : IntField := ⟨246,(-1),0,0⟩
private theorem pos34 : (0:ℤ) < 877 := by decide +kernel
private theorem cp34 : (⟨(246/877),(-1/877),0,0⟩ : CertField) = scaled n34 877 := by decide +kernel
private def n35 : IntField := ⟨89,1,0,0⟩
private theorem pos35 : (0:ℤ) < 214 := by decide +kernel
private theorem cp35 : (⟨(89/214),(1/214),0,0⟩ : CertField) = scaled n35 214 := by decide +kernel
private def n36 : IntField := ⟨9,(-1),0,0⟩
private theorem pos36 : (0:ℤ) < 13 := by decide +kernel
private theorem cp36 : (⟨(9/13),(-1/13),0,0⟩ : CertField) = scaled n36 13 := by decide +kernel
private def n37 : IntField := ⟨3146175,0,0,(-9775)⟩
private theorem pos37 : (0:ℤ) < 336938 := by decide +kernel
private theorem cp37 : (⟨(3146175/336938),0,0,(-9775/336938)⟩ : CertField) = scaled n37 336938 := by decide +kernel
private def n38 : IntField := ⟨299,0,0,1⟩
private theorem pos38 : (0:ℤ) < 1090 := by decide +kernel
private theorem cp38 : (⟨(299/1090),0,0,(1/1090)⟩ : CertField) = scaled n38 1090 := by decide +kernel
private def n39 : IntField := ⟨4209,0,0,(-1)⟩
private theorem pos39 : (0:ℤ) < 15090 := by decide +kernel
private theorem cp39 : (⟨(1403/5030),0,0,(-1/15090)⟩ : CertField) = scaled n39 15090 := by decide +kernel
private def n40 : IntField := ⟨29,0,0,1⟩
private theorem pos40 : (0:ℤ) < 82 := by decide +kernel
private theorem cp40 : (⟨(29/82),0,0,(1/82)⟩ : CertField) = scaled n40 82 := by decide +kernel
private def n41 : IntField := ⟨487,0,0,(-1)⟩
private theorem pos41 : (0:ℤ) < 1174 := by decide +kernel
private theorem cp41 : (⟨(487/1174),0,0,(-1/1174)⟩ : CertField) = scaled n41 1174 := by decide +kernel
private def n42 : IntField := ⟨880929,0,0,(-2737)⟩
private theorem pos42 : (0:ℤ) < 48134 := by decide +kernel
private theorem cp42 : (⟨(880929/48134),0,0,(-2737/48134)⟩ : CertField) = scaled n42 48134 := by decide +kernel
private def n43 : IntField := ⟨17481,0,0,91⟩
private theorem pos43 : (0:ℤ) < 1394 := by decide +kernel
private theorem cp43 : (⟨(17481/1394),0,0,(91/1394)⟩ : CertField) = scaled n43 1394 := by decide +kernel
private def n44 : IntField := ⟨117,0,0,(-1)⟩
private theorem pos44 : (0:ℤ) < 402 := by decide +kernel
private theorem cp44 : (⟨(39/134),0,0,(-1/402)⟩ : CertField) = scaled n44 402 := by decide +kernel
private def n45 : IntField := ⟨(-69748),1965815,0,0⟩
private theorem pos45 : (0:ℤ) < 386377 := by decide +kernel
private theorem cp45 : (⟨(-69748/386377),(1965815/386377),0,0⟩ : CertField) = scaled n45 386377 := by decide +kernel
private def n46 : IntField := ⟨5163,1,0,0⟩
private theorem pos46 : (0:ℤ) < 18654 := by decide +kernel
private theorem cp46 : (⟨(1721/6218),(1/18654),0,0⟩ : CertField) = scaled n46 18654 := by decide +kernel
private def n47 : IntField := ⟨251898,461834,0,0⟩
private theorem pos47 : (0:ℤ) < 117507 := by decide +kernel
private theorem cp47 : (⟨(83966/39169),(461834/117507),0,0⟩ : CertField) = scaled n47 117507 := by decide +kernel
private def n48 : IntField := ⟨1272,1,0,0⟩
private theorem pos48 : (0:ℤ) < 3013 := by decide +kernel
private theorem cp48 : (⟨(1272/3013),(1/3013),0,0⟩ : CertField) = scaled n48 3013 := by decide +kernel
private def n49 : IntField := ⟨146275,0,0,(-8775)⟩
private theorem pos49 : (0:ℤ) < 471338 := by decide +kernel
private theorem cp49 : (⟨(146275/471338),0,0,(-8775/471338)⟩ : CertField) = scaled n49 471338 := by decide +kernel
private def n50 : IntField := ⟨39,0,0,1⟩
private theorem pos50 : (0:ℤ) < 150 := by decide +kernel
private theorem cp50 : (⟨(13/50),0,0,(1/150)⟩ : CertField) = scaled n50 150 := by decide +kernel
private def n51 : IntField := ⟨689,0,0,(-1)⟩
private theorem pos51 : (0:ℤ) < 2350 := by decide +kernel
private theorem cp51 : (⟨(689/2350),0,0,(-1/2350)⟩ : CertField) = scaled n51 2350 := by decide +kernel
private def n52 : IntField := ⟨6757,0,0,(-13)⟩
private theorem pos52 : (0:ℤ) < 22270 := by decide +kernel
private theorem cp52 : (⟨(6757/22270),0,0,(-13/22270)⟩ : CertField) = scaled n52 22270 := by decide +kernel
private def n53 : IntField := ⟨219,0,0,(-1)⟩
private theorem pos53 : (0:ℤ) < 510 := by decide +kernel
private theorem cp53 : (⟨(73/170),0,0,(-1/510)⟩ : CertField) = scaled n53 510 := by decide +kernel
private def n54 : IntField := ⟨29,0,0,(-1)⟩
private theorem pos54 : (0:ℤ) < 82 := by decide +kernel
private theorem cp54 : (⟨(29/82),0,0,(-1/82)⟩ : CertField) = scaled n54 82 := by decide +kernel
private def n55 : IntField := ⟨5869,0,0,(-21)⟩
private theorem pos55 : (0:ℤ) < 16798 := by decide +kernel
private theorem cp55 : (⟨(5869/16798),0,0,(-21/16798)⟩ : CertField) = scaled n55 16798 := by decide +kernel
private def n56 : IntField := ⟨2811,0,0,(-224)⟩
private theorem pos56 : (0:ℤ) < 2227 := by decide +kernel
private theorem cp56 : (⟨(2811/2227),0,0,(-224/2227)⟩ : CertField) = scaled n56 2227 := by decide +kernel
private def n57 : IntField := ⟨(-310869),812695,0,0⟩
private theorem pos57 : (0:ℤ) < 2379971 := by decide +kernel
private theorem cp57 : (⟨(-310869/2379971),(812695/2379971),0,0⟩ : CertField) = scaled n57 2379971 := by decide +kernel
private def n58 : IntField := ⟨126,1,0,0⟩
private theorem pos58 : (0:ℤ) < 429 := by decide +kernel
private theorem cp58 : (⟨(42/143),(1/429),0,0⟩ : CertField) = scaled n58 429 := by decide +kernel
private def n59 : IntField := ⟨43,(-1),0,0⟩
private theorem pos59 : (0:ℤ) < 142 := by decide +kernel
private theorem cp59 : (⟨(43/142),(-1/142),0,0⟩ : CertField) = scaled n59 142 := by decide +kernel
private def n60 : IntField := ⟨40957,0,0,(-2457)⟩
private theorem pos60 : (0:ℤ) < 67334 := by decide +kernel
private theorem cp60 : (⟨(40957/67334),0,0,(-2457/67334)⟩ : CertField) = scaled n60 67334 := by decide +kernel
private def n61 : IntField := ⟨(-1372541),2429307,0,0⟩
private theorem pos61 : (0:ℤ) < 5625386 := by decide +kernel
private theorem cp61 : (⟨(-1372541/5625386),(2429307/5625386),0,0⟩ : CertField) = scaled n61 5625386 := by decide +kernel
private def n62 : IntField := ⟨1809,1,0,0⟩
private theorem pos62 : (0:ℤ) < 6094 := by decide +kernel
private theorem cp62 : (⟨(1809/6094),(1/6094),0,0⟩ : CertField) = scaled n62 6094 := by decide +kernel
private def n63 : IntField := ⟨384531,0,0,51442⟩
private theorem pos63 : (0:ℤ) < 555015 := by decide +kernel
private theorem cp63 : (⟨(128177/185005),0,0,(51442/555015)⟩ : CertField) = scaled n63 555015 := by decide +kernel
private def n64 : IntField := ⟨1719,0,0,1⟩
private theorem pos64 : (0:ℤ) < 5794 := by decide +kernel
private theorem cp64 : (⟨(1719/5794),0,0,(1/5794)⟩ : CertField) = scaled n64 5794 := by decide +kernel
private def n65 : IntField := ⟨16995,0,0,1054⟩
private theorem pos65 : (0:ℤ) < 25197 := by decide +kernel
private theorem cp65 : (⟨(5665/8399),0,0,(1054/25197)⟩ : CertField) = scaled n65 25197 := by decide +kernel
private def n66 : IntField := ⟨147,0,0,1⟩
private theorem pos66 : (0:ℤ) < 514 := by decide +kernel
private theorem cp66 : (⟨(147/514),0,0,(1/514)⟩ : CertField) = scaled n66 514 := by decide +kernel
private def n67 : IntField := ⟨366559,1948134,0,0⟩
private theorem pos67 : (0:ℤ) < 7058447 := by decide +kernel
private theorem cp67 : (⟨(366559/7058447),(1948134/7058447),0,0⟩ : CertField) = scaled n67 7058447 := by decide +kernel
private def n68 : IntField := ⟨3015,1,0,0⟩
private theorem pos68 : (0:ℤ) < 7278 := by decide +kernel
private theorem cp68 : (⟨(1005/2426),(1/7278),0,0⟩ : CertField) = scaled n68 7278 := by decide +kernel
private def n69 : IntField := ⟨145776,400249,0,0⟩
private theorem pos69 : (0:ℤ) < 95979 := by decide +kernel
private theorem cp69 : (⟨(48592/31993),(400249/95979),0,0⟩ : CertField) = scaled n69 95979 := by decide +kernel
private def n70 : IntField := ⟨237,1,0,0⟩
private theorem pos70 : (0:ℤ) < 814 := by decide +kernel
private theorem cp70 : (⟨(237/814),(1/814),0,0⟩ : CertField) = scaled n70 814 := by decide +kernel
private def n71 : IntField := ⟨317,(-1),0,0⟩
private theorem pos71 : (0:ℤ) < 1069 := by decide +kernel
private theorem cp71 : (⟨(317/1069),(-1/1069),0,0⟩ : CertField) = scaled n71 1069 := by decide +kernel
private def n72 : IntField := ⟨1156855,0,0,81040⟩
private theorem pos72 : (0:ℤ) < 168469 := by decide +kernel
private theorem cp72 : (⟨(165265/24067),0,0,(81040/168469)⟩ : CertField) = scaled n72 168469 := by decide +kernel
private def n73 : IntField := ⟨4585,0,0,(-1)⟩
private theorem pos73 : (0:ℤ) < 15526 := by decide +kernel
private theorem cp73 : (⟨(655/2218),0,0,(-1/15526)⟩ : CertField) = scaled n73 15526 := by decide +kernel
private def n74 : IntField := ⟨1619597,0,0,113456⟩
private theorem pos74 : (0:ℤ) < 120335 := by decide +kernel
private theorem cp74 : (⟨(1619597/120335),0,0,(113456/120335)⟩ : CertField) = scaled n74 120335 := by decide +kernel
private def n75 : IntField := ⟨9665,0,0,(-64)⟩
private theorem pos75 : (0:ℤ) < 697 := by decide +kernel
private theorem cp75 : (⟨(9665/697),0,0,(-64/697)⟩ : CertField) = scaled n75 697 := by decide +kernel
private def n76 : IntField := ⟨313,0,0,(-1)⟩
private theorem pos76 : (0:ℤ) < 1042 := by decide +kernel
private theorem cp76 : (⟨(313/1042),0,0,(-1/1042)⟩ : CertField) = scaled n76 1042 := by decide +kernel
private def n77 : IntField := ⟨(-2456013),11588245,0,0⟩
private theorem pos77 : (0:ℤ) < 2318262 := by decide +kernel
private theorem cp77 : (⟨(-818671/772754),(11588245/2318262),0,0⟩ : CertField) = scaled n77 2318262 := by decide +kernel
private def n78 : IntField := ⟨4264,1,0,0⟩
private theorem pos78 : (0:ℤ) < 14557 := by decide +kernel
private theorem cp78 : (⟨(4264/14557),(1/14557),0,0⟩ : CertField) = scaled n78 14557 := by decide +kernel
private def n79 : IntField := ⟨222876,413128,0,0⟩
private theorem pos79 : (0:ℤ) < 117507 := by decide +kernel
private theorem cp79 : (⟨(74292/39169),(413128/117507),0,0⟩ : CertField) = scaled n79 117507 := by decide +kernel
private def n80 : IntField := ⟨16627,0,0,(-77)⟩
private theorem pos80 : (0:ℤ) < 1394 := by decide +kernel
private theorem cp80 : (⟨(16627/1394),0,0,(-77/1394)⟩ : CertField) = scaled n80 1394 := by decide +kernel
private def n81 : IntField := ⟨121,0,0,1⟩
private theorem pos81 : (0:ℤ) < 430 := by decide +kernel
private theorem cp81 : (⟨(121/430),0,0,(1/430)⟩ : CertField) = scaled n81 430 := by decide +kernel
private def n82 : IntField := ⟨275,0,0,(-1)⟩
private theorem pos82 : (0:ℤ) < 922 := by decide +kernel
private theorem cp82 : (⟨(275/922),0,0,(-1/922)⟩ : CertField) = scaled n82 922 := by decide +kernel
private def n83 : IntField := ⟨13485,0,0,665⟩
private theorem pos83 : (0:ℤ) < 47838 := by decide +kernel
private theorem cp83 : (⟨(4495/15946),0,0,(95/6834)⟩ : CertField) = scaled n83 47838 := by decide +kernel
private def n84 : IntField := ⟨117,0,0,1⟩
private theorem pos84 : (0:ℤ) < 402 := by decide +kernel
private theorem cp84 : (⟨(39/134),0,0,(1/402)⟩ : CertField) = scaled n84 402 := by decide +kernel
private def n85 : IntField := ⟨15,0,0,(-1)⟩
private theorem pos85 : (0:ℤ) < 34 := by decide +kernel
private theorem cp85 : (⟨(15/34),0,0,(-1/34)⟩ : CertField) = scaled n85 34 := by decide +kernel
private def n86 : IntField := ⟨83,0,0,1⟩
private theorem pos86 : (0:ℤ) < 202 := by decide +kernel
private theorem cp86 : (⟨(83/202),0,0,(1/202)⟩ : CertField) = scaled n86 202 := by decide +kernel
private def n87 : IntField := ⟨9,0,0,(-1)⟩
private theorem pos87 : (0:ℤ) < 10 := by decide +kernel
private theorem cp87 : (⟨(9/10),0,0,(-1/10)⟩ : CertField) = scaled n87 10 := by decide +kernel
private def n88 : IntField := ⟨1651,0,0,(-18)⟩
private theorem pos88 : (0:ℤ) < 697 := by decide +kernel
private theorem cp88 : (⟨(1651/697),0,0,(-18/697)⟩ : CertField) = scaled n88 697 := by decide +kernel
private def n89 : IntField := ⟨911075,0,0,87035⟩
private theorem pos89 : (0:ℤ) < 336938 := by decide +kernel
private theorem cp89 : (⟨(911075/336938),0,0,(87035/336938)⟩ : CertField) = scaled n89 336938 := by decide +kernel
private def n90 : IntField := ⟨1275505,0,0,121849⟩
private theorem pos90 : (0:ℤ) < 240670 := by decide +kernel
private theorem cp90 : (⟨(255101/48134),0,0,(121849/240670)⟩ : CertField) = scaled n90 240670 := by decide +kernel
private def n91 : IntField := ⟨7723,0,0,91⟩
private theorem pos91 : (0:ℤ) < 1394 := by decide +kernel
private theorem cp91 : (⟨(7723/1394),0,0,(91/1394)⟩ : CertField) = scaled n91 1394 := by decide +kernel
private def n92 : IntField := ⟨147,0,0,(-1)⟩
private theorem pos92 : (0:ℤ) < 514 := by decide +kernel
private theorem cp92 : (⟨(147/514),0,0,(-1/514)⟩ : CertField) = scaled n92 514 := by decide +kernel
private def n93 : IntField := ⟨75,0,0,(-5)⟩
private theorem pos93 : (0:ℤ) < 102 := by decide +kernel
private theorem cp93 : (⟨(25/34),0,0,(-5/102)⟩ : CertField) = scaled n93 102 := by decide +kernel
private def n94 : IntField := ⟨(-3),0,0,1⟩
private theorem pos94 : (0:ℤ) < 6 := by decide +kernel
private theorem cp94 : (⟨(-1/2),0,0,(1/6)⟩ : CertField) = scaled n94 6 := by decide +kernel
private def n95 : IntField := ⟨(-1),0,0,1⟩
private theorem pos95 : (0:ℤ) < 10 := by decide +kernel
private theorem cp95 : (⟨(-1/10),0,0,(1/10)⟩ : CertField) = scaled n95 10 := by decide +kernel
private def n96 : IntField := ⟨18879,0,0,931⟩
private theorem pos96 : (0:ℤ) < 34170 := by decide +kernel
private theorem cp96 : (⟨(6293/11390),0,0,(931/34170)⟩ : CertField) = scaled n96 34170 := by decide +kernel
private def n97 : IntField := ⟨(-31948),28553,0,0⟩
private theorem pos97 : (0:ℤ) < 28083 := by decide +kernel
private theorem cp97 : (⟨(-31948/28083),(28553/28083),0,0⟩ : CertField) = scaled n97 28083 := by decide +kernel
private def n98 : IntField := ⟨5,1,0,0⟩
private theorem pos98 : (0:ℤ) < 22 := by decide +kernel
private theorem cp98 : (⟨(5/22),(1/22),0,0⟩ : CertField) = scaled n98 22 := by decide +kernel
private def n99 : IntField := ⟨(-718368),626311,0,0⟩
private theorem pos99 : (0:ℤ) < 585948 := by decide +kernel
private theorem cp99 : (⟨(-59864/48829),(626311/585948),0,0⟩ : CertField) = scaled n99 585948 := by decide +kernel
private def n100 : IntField := ⟨(-1405395),1375466,0,0⟩
private theorem pos100 : (0:ℤ) < 1525029 := by decide +kernel
private theorem cp100 : (⟨(-468465/508343),(1375466/1525029),0,0⟩ : CertField) = scaled n100 1525029 := by decide +kernel
private def n101 : IntField := ⟨517,(-1),0,0⟩
private theorem pos101 : (0:ℤ) < 1249 := by decide +kernel
private theorem cp101 : (⟨(517/1249),(-1/1249),0,0⟩ : CertField) = scaled n101 1249 := by decide +kernel
private def n102 : IntField := ⟨(-166418),237950,0,0⟩
private theorem pos102 : (0:ℤ) < 365079 := by decide +kernel
private theorem cp102 : (⟨(-166418/365079),(237950/365079),0,0⟩ : CertField) = scaled n102 365079 := by decide +kernel
private def n103 : IntField := ⟨(-1918155),2592133,0,0⟩
private theorem pos103 : (0:ℤ) < 3808662 := by decide +kernel
private theorem cp103 : (⟨(-639385/1269554),(2592133/3808662),0,0⟩ : CertField) = scaled n103 3808662 := by decide +kernel
private def n104 : IntField := ⟨(-4753457),10645601,0,0⟩
private theorem pos104 : (0:ℤ) < 19825377 := by decide +kernel
private theorem cp104 : (⟨(-4753457/19825377),(10645601/19825377),0,0⟩ : CertField) = scaled n104 19825377 := by decide +kernel
private def n105 : IntField := ⟨7126725,1955485,0,0⟩
private theorem pos105 : (0:ℤ) < 5220637 := by decide +kernel
private theorem cp105 : (⟨(7126725/5220637),(1955485/5220637),0,0⟩ : CertField) = scaled n105 5220637 := by decide +kernel
private def n106 : IntField := ⟨441215,0,0,(-46655)⟩
private theorem pos106 : (0:ℤ) < 341054 := by decide +kernel
private theorem cp106 : (⟨(441215/341054),0,0,(-6665/48722)⟩ : CertField) = scaled n106 341054 := by decide +kernel
private def n107 : IntField := ⟨1209,0,0,1⟩
private theorem pos107 : (0:ℤ) < 2866 := by decide +kernel
private theorem cp107 : (⟨(1209/2866),0,0,(1/2866)⟩ : CertField) = scaled n107 2866 := by decide +kernel
private def n108 : IntField := ⟨15,(-1),0,0⟩
private theorem pos108 : (0:ℤ) < 37 := by decide +kernel
private theorem cp108 : (⟨(15/37),(-1/37),0,0⟩ : CertField) = scaled n108 37 := by decide +kernel
private def n109 : IntField := ⟨271,(-1),0,0⟩
private theorem pos109 : (0:ℤ) < 1006 := by decide +kernel
private theorem cp109 : (⟨(271/1006),(-1/1006),0,0⟩ : CertField) = scaled n109 1006 := by decide +kernel
private def n110 : IntField := ⟨51959375,12944345,0,0⟩
private theorem pos110 : (0:ℤ) < 37567058 := by decide +kernel
private theorem cp110 : (⟨(51959375/37567058),(12944345/37567058),0,0⟩ : CertField) = scaled n110 37567058 := by decide +kernel
private def n111 : IntField := ⟨767,1,0,0⟩
private theorem pos111 : (0:ℤ) < 2749 := by decide +kernel
private theorem cp111 : (⟨(767/2749),(1/2749),0,0⟩ : CertField) = scaled n111 2749 := by decide +kernel
private def n112 : IntField := ⟨409653009,102638027,0,0⟩
private theorem pos112 : (0:ℤ) < 294014566 := by decide +kernel
private theorem cp112 : (⟨(409653009/294014566),(102638027/294014566),0,0⟩ : CertField) = scaled n112 294014566 := by decide +kernel
private def n113 : IntField := ⟨8171,22664,0,0⟩
private theorem pos113 : (0:ℤ) < 31993 := by decide +kernel
private theorem cp113 : (⟨(8171/31993),(22664/31993),0,0⟩ : CertField) = scaled n113 31993 := by decide +kernel
private def n114 : IntField := ⟨460875,0,0,3875⟩
private theorem pos114 : (0:ℤ) < 336938 := by decide +kernel
private theorem cp114 : (⟨(460875/336938),0,0,(3875/336938)⟩ : CertField) = scaled n114 336938 := by decide +kernel
private def n115 : IntField := ⟨129045,0,0,1085⟩
private theorem pos115 : (0:ℤ) < 48134 := by decide +kernel
private theorem cp115 : (⟨(129045/48134),0,0,(1085/48134)⟩ : CertField) = scaled n115 48134 := by decide +kernel
private def n116 : IntField := ⟨2931,0,0,(-29)⟩
private theorem pos116 : (0:ℤ) < 1394 := by decide +kernel
private theorem cp116 : (⟨(2931/1394),0,0,(-29/1394)⟩ : CertField) = scaled n116 1394 := by decide +kernel
private def n117 : IntField := ⟨(-69144),911665,0,0⟩
private theorem pos117 : (0:ℤ) < 1159131 := by decide +kernel
private theorem cp117 : (⟨(-23048/386377),(911665/1159131),0,0⟩ : CertField) = scaled n117 1159131 := by decide +kernel
private def n118 : IntField := ⟨12536,23388,0,0⟩
private theorem pos118 : (0:ℤ) < 39169 := by decide +kernel
private theorem cp118 : (⟨(12536/39169),(23388/39169),0,0⟩ : CertField) = scaled n118 39169 := by decide +kernel
private def n119 : IntField := ⟨13461,13073,0,0⟩
private theorem pos119 : (0:ℤ) < 33598 := by decide +kernel
private theorem cp119 : (⟨(13461/33598),(13073/33598),0,0⟩ : CertField) = scaled n119 33598 := by decide +kernel
private def n120 : IntField := ⟨360273,736243,0,0⟩
private theorem pos120 : (0:ℤ) < 1694452 := by decide +kernel
private theorem cp120 : (⟨(360273/1694452),(736243/1694452),0,0⟩ : CertField) = scaled n120 1694452 := by decide +kernel
private def n121 : IntField := ⟨198,(-1),0,0⟩
private theorem pos121 : (0:ℤ) < 537 := by decide +kernel
private theorem cp121 : (⟨(66/179),(-1/537),0,0⟩ : CertField) = scaled n121 537 := by decide +kernel
private def n122 : IntField := ⟨7,0,0,0⟩
private theorem pos122 : (0:ℤ) < 5 := by decide +kernel
private theorem cp122 : (⟨(7/5),0,0,0⟩ : CertField) = scaled n122 5 := by decide +kernel
private def n123 : IntField := ⟨189,0,0,(-1)⟩
private theorem pos123 : (0:ℤ) < 510 := by decide +kernel
private theorem cp123 : (⟨(63/170),0,0,(-1/510)⟩ : CertField) = scaled n123 510 := by decide +kernel
private def n124 : IntField := ⟨1,0,0,0⟩
private theorem pos124 : (0:ℤ) < 1 := by decide +kernel
private theorem cp124 : (⟨1,0,0,0⟩ : CertField) = scaled n124 1 := by decide +kernel
private def n125 : IntField := ⟨539885,0,0,(-10055)⟩
private theorem pos125 : (0:ℤ) < 341054 := by decide +kernel
private theorem cp125 : (⟨(539885/341054),0,0,(-10055/341054)⟩ : CertField) = scaled n125 341054 := by decide +kernel
private def n126 : IntField := ⟨755839,0,0,(-14077)⟩
private theorem pos126 : (0:ℤ) < 243610 := by decide +kernel
private theorem cp126 : (⟨(755839/243610),0,0,(-14077/243610)⟩ : CertField) = scaled n126 243610 := by decide +kernel
private def n127 : IntField := ⟨153,0,0,0⟩
private theorem pos127 : (0:ℤ) < 250 := by decide +kernel
private theorem cp127 : (⟨(153/250),0,0,0⟩ : CertField) = scaled n127 250 := by decide +kernel
private def n128 : IntField := ⟨193703,0,0,(-4748)⟩
private theorem pos128 : (0:ℤ) < 848225 := by decide +kernel
private theorem cp128 : (⟨(193703/848225),0,0,(-4748/848225)⟩ : CertField) = scaled n128 848225 := by decide +kernel
private def n129 : IntField := ⟨3539,0,0,1⟩
private theorem pos129 : (0:ℤ) < 9250 := by decide +kernel
private theorem cp129 : (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) = scaled n129 9250 := by decide +kernel
private def n130 : IntField := ⟨105,0,0,(-1)⟩
private theorem pos130 : (0:ℤ) < 262 := by decide +kernel
private theorem cp130 : (⟨(105/262),0,0,(-1/262)⟩ : CertField) = scaled n130 262 := by decide +kernel
private def n131 : IntField := ⟨35,1,0,0⟩
private theorem pos131 : (0:ℤ) < 94 := by decide +kernel
private theorem cp131 : (⟨(35/94),(1/94),0,0⟩ : CertField) = scaled n131 94 := by decide +kernel
private def n132 : IntField := ⟨628621,0,0,62208⟩
private theorem pos132 : (0:ℤ) < 804215 := by decide +kernel
private theorem cp132 : (⟨(628621/804215),0,0,(62208/804215)⟩ : CertField) = scaled n132 804215 := by decide +kernel
private def n133 : IntField := ⟨217,0,0,1⟩
private theorem pos133 : (0:ℤ) < 574 := by decide +kernel
private theorem cp133 : (⟨(31/82),0,0,(1/574)⟩ : CertField) = scaled n133 574 := by decide +kernel
private def n134 : IntField := ⟨3035,0,0,(-1)⟩
private theorem pos134 : (0:ℤ) < 7846 := by decide +kernel
private theorem cp134 : (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) = scaled n134 7846 := by decide +kernel
private def n135 : IntField := ⟨24871,0,0,108⟩
private theorem pos135 : (0:ℤ) < 28987 := by decide +kernel
private theorem cp135 : (⟨(3553/4141),0,0,(108/28987)⟩ : CertField) = scaled n135 28987 := by decide +kernel
private def n136 : IntField := ⟨83,0,0,(-1)⟩
private theorem pos136 : (0:ℤ) < 202 := by decide +kernel
private theorem cp136 : (⟨(83/202),0,0,(-1/202)⟩ : CertField) = scaled n136 202 := by decide +kernel
private def n137 : IntField := ⟨13109,0,0,(-176)⟩
private theorem pos137 : (0:ℤ) < 43885 := by decide +kernel
private theorem cp137 : (⟨(13109/43885),0,0,(-176/43885)⟩ : CertField) = scaled n137 43885 := by decide +kernel
private def n138 : IntField := ⟨251,0,0,1⟩
private theorem pos138 : (0:ℤ) < 670 := by decide +kernel
private theorem cp138 : (⟨(251/670),0,0,(1/670)⟩ : CertField) = scaled n138 670 := by decide +kernel
private def n139 : IntField := ⟨21343,0,0,(-391)⟩
private theorem pos139 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp139 : (⟨(3049/8282),0,0,(-391/57974)⟩ : CertField) = scaled n139 57974 := by decide +kernel
private def n140 : IntField := ⟨(-24300),51497,0,0⟩
private theorem pos140 : (0:ℤ) < 147323 := by decide +kernel
private theorem cp140 : (⟨(-24300/147323),(51497/147323),0,0⟩ : CertField) = scaled n140 147323 := by decide +kernel
private def n141 : IntField := ⟨247,1,0,0⟩
private theorem pos141 : (0:ℤ) < 649 := by decide +kernel
private theorem cp141 : (⟨(247/649),(1/649),0,0⟩ : CertField) = scaled n141 649 := by decide +kernel
private def n142 : IntField := ⟨177,(-1),0,0⟩
private theorem pos142 : (0:ℤ) < 454 := by decide +kernel
private theorem cp142 : (⟨(177/454),(-1/454),0,0⟩ : CertField) = scaled n142 454 := by decide +kernel
private def n143 : IntField := ⟨(-2406288),3511661,0,0⟩
private theorem pos143 : (0:ℤ) < 7660796 := by decide +kernel
private theorem cp143 : (⟨(-601572/1915199),(3511661/7660796),0,0⟩ : CertField) = scaled n143 7660796 := by decide +kernel
private def n144 : IntField := ⟨187203,1481141,0,0⟩
private theorem pos144 : (0:ℤ) < 5421097 := by decide +kernel
private theorem cp144 : (⟨(187203/5421097),(1481141/5421097),0,0⟩ : CertField) = scaled n144 5421097 := by decide +kernel
private def n145 : IntField := ⟨3230,(-1),0,0⟩
private theorem pos145 : (0:ℤ) < 8353 := by decide +kernel
private theorem cp145 : (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = scaled n145 8353 := by decide +kernel
private def n146 : IntField := ⟨1355921,0,0,(-33236)⟩
private theorem pos146 : (0:ℤ) < 3029375 := by decide +kernel
private theorem cp146 : (⟨(1355921/3029375),0,0,(-33236/3029375)⟩ : CertField) = scaled n146 3029375 := by decide +kernel
private def n147 : IntField := ⟨9833,0,0,(-171)⟩
private theorem pos147 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp147 : (⟨(9833/12314),0,0,(-171/12314)⟩ : CertField) = scaled n147 12314 := by decide +kernel
private def n148 : IntField := ⟨31,0,0,1⟩
private theorem pos148 : (0:ℤ) < 94 := by decide +kernel
private theorem cp148 : (⟨(31/94),0,0,(1/94)⟩ : CertField) = scaled n148 94 := by decide +kernel
private def n149 : IntField := ⟨554601,1145809,0,0⟩
private theorem pos149 : (0:ℤ) < 304278 := by decide +kernel
private theorem cp149 : (⟨(184867/101426),(1145809/304278),0,0⟩ : CertField) = scaled n149 304278 := by decide +kernel
private def n150 : IntField := ⟨96,(-1),0,0⟩
private theorem pos150 : (0:ℤ) < 249 := by decide +kernel
private theorem cp150 : (⟨(32/83),(-1/249),0,0⟩ : CertField) = scaled n150 249 := by decide +kernel
private def n151 : IntField := ⟨(-297343),2732382,0,0⟩
private theorem pos151 : (0:ℤ) < 612457 := by decide +kernel
private theorem cp151 : (⟨(-297343/612457),(2732382/612457),0,0⟩ : CertField) = scaled n151 612457 := by decide +kernel
private def n152 : IntField := ⟨4479,(-1),0,0⟩
private theorem pos152 : (0:ℤ) < 16062 := by decide +kernel
private theorem cp152 : (⟨(1493/5354),(-1/16062),0,0⟩ : CertField) = scaled n152 16062 := by decide +kernel
private def n153 : IntField := ⟨2514041,3575763,0,0⟩
private theorem pos153 : (0:ℤ) < 1135849 := by decide +kernel
private theorem cp153 : (⟨(2514041/1135849),(3575763/1135849),0,0⟩ : CertField) = scaled n153 1135849 := by decide +kernel
private def n154 : IntField := ⟨1413,(-1),0,0⟩
private theorem pos154 : (0:ℤ) < 3718 := by decide +kernel
private theorem cp154 : (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = scaled n154 3718 := by decide +kernel
private def n155 : IntField := ⟨6937,0,0,57⟩
private theorem pos155 : (0:ℤ) < 658 := by decide +kernel
private theorem cp155 : (⟨(991/94),0,0,(57/658)⟩ : CertField) = scaled n155 658 := by decide +kernel
private def n156 : IntField := ⟨21,0,0,(-1)⟩
private theorem pos156 : (0:ℤ) < 42 := by decide +kernel
private theorem cp156 : (⟨(1/2),0,0,(-1/42)⟩ : CertField) = scaled n156 42 := by decide +kernel
private def n157 : IntField := ⟨85625,0,0,565⟩
private theorem pos157 : (0:ℤ) < 9478 := by decide +kernel
private theorem cp157 : (⟨(85625/9478),0,0,(565/9478)⟩ : CertField) = scaled n157 9478 := by decide +kernel
private def n158 : IntField := ⟨4893,0,0,1⟩
private theorem pos158 : (0:ℤ) < 17682 := by decide +kernel
private theorem cp158 : (⟨(233/842),0,0,(1/17682)⟩ : CertField) = scaled n158 17682 := by decide +kernel
private def n159 : IntField := ⟨523,0,0,1⟩
private theorem pos159 : (0:ℤ) < 1354 := by decide +kernel
private theorem cp159 : (⟨(523/1354),0,0,(1/1354)⟩ : CertField) = scaled n159 1354 := by decide +kernel
private def n160 : IntField := ⟨119875,0,0,791⟩
private theorem pos160 : (0:ℤ) < 6770 := by decide +kernel
private theorem cp160 : (⟨(23975/1354),0,0,(791/6770)⟩ : CertField) = scaled n160 6770 := by decide +kernel
private def n161 : IntField := ⟨8449,0,0,33⟩
private theorem pos161 : (0:ℤ) < 658 := by decide +kernel
private theorem cp161 : (⟨(1207/94),0,0,(33/658)⟩ : CertField) = scaled n161 658 := by decide +kernel
private def n162 : IntField := ⟨345,0,0,1⟩
private theorem pos162 : (0:ℤ) < 1266 := by decide +kernel
private theorem cp162 : (⟨(115/422),0,0,(1/1266)⟩ : CertField) = scaled n162 1266 := by decide +kernel
private def n163 : IntField := ⟨1577625,0,0,20000⟩
private theorem pos163 : (0:ℤ) < 7881307 := by decide +kernel
private theorem cp163 : (⟨(225375/1125901),0,0,(20000/7881307)⟩ : CertField) = scaled n163 7881307 := by decide +kernel
private def n164 : IntField := ⟨231,0,0,(-4)⟩
private theorem pos164 : (0:ℤ) < 707 := by decide +kernel
private theorem cp164 : (⟨(33/101),0,0,(-4/707)⟩ : CertField) = scaled n164 707 := by decide +kernel
private def n165 : IntField := ⟨(-16887),43160,0,0⟩
private theorem pos165 : (0:ℤ) < 147323 := by decide +kernel
private theorem cp165 : (⟨(-16887/147323),(43160/147323),0,0⟩ : CertField) = scaled n165 147323 := by decide +kernel
private def n166 : IntField := ⟨63105,0,0,800⟩
private theorem pos166 : (0:ℤ) < 160843 := by decide +kernel
private theorem cp166 : (⟨(63105/160843),0,0,(800/160843)⟩ : CertField) = scaled n166 160843 := by decide +kernel
private def n167 : IntField := ⟨(-73993),129086,0,0⟩
private theorem pos167 : (0:ℤ) < 348218 := by decide +kernel
private theorem cp167 : (⟨(-73993/348218),(64543/174109),0,0⟩ : CertField) = scaled n167 348218 := by decide +kernel
private def n168 : IntField := ⟨3962749,0,0,275891⟩
private theorem pos168 : (0:ℤ) < 6058750 := by decide +kernel
private theorem cp168 : (⟨(3962749/6058750),0,0,(275891/6058750)⟩ : CertField) = scaled n168 6058750 := by decide +kernel
private def n169 : IntField := ⟨8727,0,0,(-143)⟩
private theorem pos169 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp169 : (⟨(8727/12314),0,0,(-143/12314)⟩ : CertField) = scaled n169 12314 := by decide +kernel
private def n170 : IntField := ⟨5976,566539,0,0⟩
private theorem pos170 : (0:ℤ) < 2214839 := by decide +kernel
private theorem cp170 : (⟨(5976/2214839),(566539/2214839),0,0⟩ : CertField) = scaled n170 2214839 := by decide +kernel
private def n171 : IntField := ⟨3734,1,0,0⟩
private theorem pos171 : (0:ℤ) < 9757 := by decide +kernel
private theorem cp171 : (⟨(3734/9757),(1/9757),0,0⟩ : CertField) = scaled n171 9757 := by decide +kernel
private def n172 : IntField := ⟨244971,512554,0,0⟩
private theorem pos172 : (0:ℤ) < 152139 := by decide +kernel
private theorem cp172 : (⟨(81657/50713),(512554/152139),0,0⟩ : CertField) = scaled n172 152139 := by decide +kernel
private def n173 : IntField := ⟨414366,6708677,0,0⟩
private theorem pos173 : (0:ℤ) < 1837371 := by decide +kernel
private theorem cp173 : (⟨(138122/612457),(6708677/1837371),0,0⟩ : CertField) = scaled n173 1837371 := by decide +kernel
private def n174 : IntField := ⟨4840,(-1),0,0⟩
private theorem pos174 : (0:ℤ) < 16393 := by decide +kernel
private theorem cp174 : (⟨(4840/16393),(-1/16393),0,0⟩ : CertField) = scaled n174 16393 := by decide +kernel
private def n175 : IntField := ⟨202772,290686,0,0⟩
private theorem pos175 : (0:ℤ) < 103259 := by decide +kernel
private theorem cp175 : (⟨(202772/103259),(290686/103259),0,0⟩ : CertField) = scaled n175 103259 := by decide +kernel
private def n176 : IntField := ⟨1123605,0,0,(-81920)⟩
private theorem pos176 : (0:ℤ) < 99519 := by decide +kernel
private theorem cp176 : (⟨(53505/4739),0,0,(-81920/99519)⟩ : CertField) = scaled n176 99519 := by decide +kernel
private def n177 : IntField := ⟨4009,0,0,1⟩
private theorem pos177 : (0:ℤ) < 13690 := by decide +kernel
private theorem cp177 : (⟨(4009/13690),0,0,(1/13690)⟩ : CertField) = scaled n177 13690 := by decide +kernel
private def n178 : IntField := ⟨224721,0,0,(-16384)⟩
private theorem pos178 : (0:ℤ) < 10155 := by decide +kernel
private theorem cp178 : (⟨(74907/3385),0,0,(-16384/10155)⟩ : CertField) = scaled n178 10155 := by decide +kernel
private def n179 : IntField := ⟨9891,0,0,(-16)⟩
private theorem pos179 : (0:ℤ) < 987 := by decide +kernel
private theorem cp179 : (⟨(471/47),0,0,(-16/987)⟩ : CertField) = scaled n179 987 := by decide +kernel
private def n180 : IntField := ⟨2299633,0,0,(-203377)⟩
private theorem pos180 : (0:ℤ) < 21210854 := by decide +kernel
private theorem cp180 : (⟨(328519/3030122),0,0,(-203377/21210854)⟩ : CertField) = scaled n180 21210854 := by decide +kernel
private def n181 : IntField := ⟨681,0,0,1⟩
private theorem pos181 : (0:ℤ) < 1770 := by decide +kernel
private theorem cp181 : (⟨(227/590),0,0,(1/1770)⟩ : CertField) = scaled n181 1770 := by decide +kernel
private def n182 : IntField := ⟨19899,0,0,(-1)⟩
private theorem pos182 : (0:ℤ) < 51358 := by decide +kernel
private theorem cp182 : (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) = scaled n182 51358 := by decide +kernel
private def n183 : IntField := ⟨1323,0,0,(-1)⟩
private theorem pos183 : (0:ℤ) < 4354 := by decide +kernel
private theorem cp183 : (⟨(189/622),0,0,(-1/4354)⟩ : CertField) = scaled n183 4354 := by decide +kernel
private def n184 : IntField := ⟨10967,0,0,1189⟩
private theorem pos184 : (0:ℤ) < 198830 := by decide +kernel
private theorem cp184 : (⟨(10967/198830),0,0,(1189/198830)⟩ : CertField) = scaled n184 198830 := by decide +kernel
private def n185 : IntField := ⟨1311,0,0,(-1)⟩
private theorem pos185 : (0:ℤ) < 3370 := by decide +kernel
private theorem cp185 : (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) = scaled n185 3370 := by decide +kernel
private def n186 : IntField := ⟨28623,0,0,3071⟩
private theorem pos186 : (0:ℤ) < 454510 := by decide +kernel
private theorem cp186 : (⟨(4089/64930),0,0,(3071/454510)⟩ : CertField) = scaled n186 454510 := by decide +kernel
private def n187 : IntField := ⟨579,0,0,1⟩
private theorem pos187 : (0:ℤ) < 1510 := by decide +kernel
private theorem cp187 : (⟨(579/1510),0,0,(1/1510)⟩ : CertField) = scaled n187 1510 := by decide +kernel
private def n188 : IntField := ⟨1169,0,0,(-1)⟩
private theorem pos188 : (0:ℤ) < 3010 := by decide +kernel
private theorem cp188 : (⟨(167/430),0,0,(-1/3010)⟩ : CertField) = scaled n188 3010 := by decide +kernel
private def n189 : IntField := ⟨(-11491011),26699858,0,0⟩
private theorem pos189 : (0:ℤ) < 250733964 := by decide +kernel
private theorem cp189 : (⟨(-3830337/83577988),(13349929/125366982),0,0⟩ : CertField) = scaled n189 250733964 := by decide +kernel
private def n190 : IntField := ⟨1059,1,0,0⟩
private theorem pos190 : (0:ℤ) < 2742 := by decide +kernel
private theorem cp190 : (⟨(353/914),(1/2742),0,0⟩ : CertField) = scaled n190 2742 := by decide +kernel
private def n191 : IntField := ⟨1364,(-1),0,0⟩
private theorem pos191 : (0:ℤ) < 3517 := by decide +kernel
private theorem cp191 : (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) = scaled n191 3517 := by decide +kernel
private def n192 : IntField := ⟨3289,1,0,0⟩
private theorem pos192 : (0:ℤ) < 10753 := by decide +kernel
private theorem cp192 : (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = scaled n192 10753 := by decide +kernel
private def n193 : IntField := ⟨71,(-1),0,0⟩
private theorem pos193 : (0:ℤ) < 229 := by decide +kernel
private theorem cp193 : (⟨(71/229),(-1/229),0,0⟩ : CertField) = scaled n193 229 := by decide +kernel
private def n194 : IntField := ⟨16097431,0,0,(-1423639)⟩
private theorem pos194 : (0:ℤ) < 75753050 := by decide +kernel
private theorem cp194 : (⟨(16097431/75753050),0,0,(-1423639/75753050)⟩ : CertField) = scaled n194 75753050 := by decide +kernel
private def n195 : IntField := ⟨1693486,4861851,0,0⟩
private theorem pos195 : (0:ℤ) < 4216979 := by decide +kernel
private theorem cp195 : (⟨(1693486/4216979),(4861851/4216979),0,0⟩ : CertField) = scaled n195 4216979 := by decide +kernel
private def n196 : IntField := ⟨469,1,0,0⟩
private theorem pos196 : (0:ℤ) < 1549 := by decide +kernel
private theorem cp196 : (⟨(469/1549),(1/1549),0,0⟩ : CertField) = scaled n196 1549 := by decide +kernel
private def n197 : IntField := ⟨579,(-1),0,0⟩
private theorem pos197 : (0:ℤ) < 1894 := by decide +kernel
private theorem cp197 : (⟨(579/1894),(-1/1894),0,0⟩ : CertField) = scaled n197 1894 := by decide +kernel
private def n198 : IntField := ⟨553,1,0,0⟩
private theorem pos198 : (0:ℤ) < 1429 := by decide +kernel
private theorem cp198 : (⟨(553/1429),(1/1429),0,0⟩ : CertField) = scaled n198 1429 := by decide +kernel
private def n199 : IntField := ⟨14961695,0,0,945270⟩
private theorem pos199 : (0:ℤ) < 7881307 := by decide +kernel
private theorem cp199 : (⟨(2137385/1125901),0,0,(945270/7881307)⟩ : CertField) = scaled n199 7881307 := by decide +kernel
private def n200 : IntField := ⟨313,0,0,1⟩
private theorem pos200 : (0:ℤ) < 1042 := by decide +kernel
private theorem cp200 : (⟨(313/1042),0,0,(1/1042)⟩ : CertField) = scaled n200 1042 := by decide +kernel
private def n201 : IntField := ⟨8531,0,0,(-1)⟩
private theorem pos201 : (0:ℤ) < 27970 := by decide +kernel
private theorem cp201 : (⟨(8531/27970),0,0,(-1/27970)⟩ : CertField) = scaled n201 27970 := by decide +kernel
private def n202 : IntField := ⟨2992339,0,0,189054⟩
private theorem pos202 : (0:ℤ) < 804215 := by decide +kernel
private theorem cp202 : (⟨(2992339/804215),0,0,(189054/804215)⟩ : CertField) = scaled n202 804215 := by decide +kernel
private def n203 : IntField := ⟨16489,0,0,(-324)⟩
private theorem pos203 : (0:ℤ) < 4141 := by decide +kernel
private theorem cp203 : (⟨(16489/4141),0,0,(-324/4141)⟩ : CertField) = scaled n203 4141 := by decide +kernel
private def n204 : IntField := ⟨539,0,0,(-1)⟩
private theorem pos204 : (0:ℤ) < 1750 := by decide +kernel
private theorem cp204 : (⟨(77/250),0,0,(-1/1750)⟩ : CertField) = scaled n204 1750 := by decide +kernel
private def n205 : IntField := ⟨(-14351173),69686630,0,0⟩
private theorem pos205 : (0:ℤ) < 50928131 := by decide +kernel
private theorem cp205 : (⟨(-14351173/50928131),(69686630/50928131),0,0⟩ : CertField) = scaled n205 50928131 := by decide +kernel
private def n206 : IntField := ⟨8222,1,0,0⟩
private theorem pos206 : (0:ℤ) < 27073 := by decide +kernel
private theorem cp206 : (⟨(8222/27073),(1/27073),0,0⟩ : CertField) = scaled n206 27073 := by decide +kernel
private def n207 : IntField := ⟨14937036,28731998,0,0⟩
private theorem pos207 : (0:ℤ) < 29542461 := by decide +kernel
private theorem cp207 : (⟨(4979012/9847487),(28731998/29542461),0,0⟩ : CertField) = scaled n207 29542461 := by decide +kernel
private def n208 : IntField := ⟨7767,1,0,0⟩
private theorem pos208 : (0:ℤ) < 20022 := by decide +kernel
private theorem cp208 : (⟨(2589/6674),(1/20022),0,0⟩ : CertField) = scaled n208 20022 := by decide +kernel
private def n209 : IntField := ⟨207179,0,0,(-3915)⟩
private theorem pos209 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp209 : (⟨(29597/8282),0,0,(-3915/57974)⟩ : CertField) = scaled n209 57974 := by decide +kernel
private def n210 : IntField := ⟨275,0,0,1⟩
private theorem pos210 : (0:ℤ) < 922 := by decide +kernel
private theorem cp210 : (⟨(275/922),0,0,(1/922)⟩ : CertField) = scaled n210 922 := by decide +kernel
private def n211 : IntField := ⟨489,0,0,(-1)⟩
private theorem pos211 : (0:ℤ) < 1594 := by decide +kernel
private theorem cp211 : (⟨(489/1594),0,0,(-1/1594)⟩ : CertField) = scaled n211 1594 := by decide +kernel
private def n212 : IntField := ⟨12288129,0,0,(-983651)⟩
private theorem pos212 : (0:ℤ) < 209049862 := by decide +kernel
private theorem cp212 : (⟨(1755447/29864266),0,0,(-983651/209049862)⟩ : CertField) = scaled n212 209049862 := by decide +kernel
private def n213 : IntField := ⟨1311,0,0,1⟩
private theorem pos213 : (0:ℤ) < 3370 := by decide +kernel
private theorem cp213 : (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) = scaled n213 3370 := by decide +kernel
private def n214 : IntField := ⟨34601,0,0,(-1)⟩
private theorem pos214 : (0:ℤ) < 88618 := by decide +kernel
private theorem cp214 : (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) = scaled n214 88618 := by decide +kernel
private def n215 : IntField := ⟨58431,0,0,6527⟩
private theorem pos215 : (0:ℤ) < 1843390 := by decide +kernel
private theorem cp215 : (⟨(58431/1843390),0,0,(6527/1843390)⟩ : CertField) = scaled n215 1843390 := by decide +kernel
private def n216 : IntField := ⟨2141,0,0,(-1)⟩
private theorem pos216 : (0:ℤ) < 5470 := by decide +kernel
private theorem cp216 : (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) = scaled n216 5470 := by decide +kernel
private def n217 : IntField := ⟨17591,0,0,1957⟩
private theorem pos217 : (0:ℤ) < 502670 := by decide +kernel
private theorem cp217 : (⟨(2513/71810),0,0,(1957/502670)⟩ : CertField) = scaled n217 502670 := by decide +kernel
private def n218 : IntField := ⟨1169,0,0,1⟩
private theorem pos218 : (0:ℤ) < 3010 := by decide +kernel
private theorem cp218 : (⟨(167/430),0,0,(1/3010)⟩ : CertField) = scaled n218 3010 := by decide +kernel
private def n219 : IntField := ⟨1959,0,0,(-1)⟩
private theorem pos219 : (0:ℤ) < 5010 := by decide +kernel
private theorem cp219 : (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) = scaled n219 5010 := by decide +kernel
private def n220 : IntField := ⟨(-19962981),46792268,0,0⟩
private theorem pos220 : (0:ℤ) < 770972124 := by decide +kernel
private theorem cp220 : (⟨(-6654327/256990708),(11698067/192743031),0,0⟩ : CertField) = scaled n220 770972124 := by decide +kernel
private def n221 : IntField := ⟨1932,1,0,0⟩
private theorem pos221 : (0:ℤ) < 4957 := by decide +kernel
private theorem cp221 : (⟨(1932/4957),(1/4957),0,0⟩ : CertField) = scaled n221 4957 := by decide +kernel
private def n222 : IntField := ⟨2337,(-1),0,0⟩
private theorem pos222 : (0:ℤ) < 5982 := by decide +kernel
private theorem cp222 : (⟨(779/1994),(-1/5982),0,0⟩ : CertField) = scaled n222 5982 := by decide +kernel
private def n223 : IntField := ⟨86016903,0,0,(-6885557)⟩
private theorem pos223 : (0:ℤ) < 746606650 := by decide +kernel
private theorem cp223 : (⟨(86016903/746606650),0,0,(-6885557/746606650)⟩ : CertField) = scaled n223 746606650 := by decide +kernel
private def n224 : IntField := ⟨73300124,183314232,0,0⟩
private theorem pos224 : (0:ℤ) < 312797329 := by decide +kernel
private theorem cp224 : (⟨(73300124/312797329),(183314232/312797329),0,0⟩ : CertField) = scaled n224 312797329 := by decide +kernel
private def n225 : IntField := ⟨13260,1,0,0⟩
private theorem pos225 : (0:ℤ) < 33937 := by decide +kernel
private theorem cp225 : (⟨(13260/33937),(1/33937),0,0⟩ : CertField) = scaled n225 33937 := by decide +kernel
private def n226 : IntField := ⟨278,(-1),0,0⟩
private theorem pos226 : (0:ℤ) < 709 := by decide +kernel
private theorem cp226 : (⟨(278/709),(-1/709),0,0⟩ : CertField) = scaled n226 709 := by decide +kernel
private def n227 : IntField := ⟨63629565,0,0,5472215⟩
private theorem pos227 : (0:ℤ) < 65710974 := by decide +kernel
private theorem cp227 : (⟨(21209855/21903658),0,0,(781745/9387282)⟩ : CertField) = scaled n227 65710974 := by decide +kernel
private def n228 : IntField := ⟨5409,0,0,(-1)⟩
private theorem pos228 : (0:ℤ) < 13866 := by decide +kernel
private theorem cp228 : (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) = scaled n228 13866 := by decide +kernel
private def n229 : IntField := ⟨89081391,0,0,7661101⟩
private theorem pos229 : (0:ℤ) < 46936410 := by decide +kernel
private theorem cp229 : (⟨(29693797/15645470),0,0,(7661101/46936410)⟩ : CertField) = scaled n229 46936410 := by decide +kernel
private def n230 : IntField := ⟨35613,0,0,(-5933)⟩
private theorem pos230 : (0:ℤ) < 4062 := by decide +kernel
private theorem cp230 : (⟨(11871/1354),0,0,(-5933/4062)⟩ : CertField) = scaled n230 4062 := by decide +kernel
private def n231 : IntField := ⟨223209,0,0,(-37115)⟩
private theorem pos231 : (0:ℤ) < 28434 := by decide +kernel
private theorem cp231 : (⟨(10629/1354),0,0,(-37115/28434)⟩ : CertField) = scaled n231 28434 := by decide +kernel
private def n232 : IntField := ⟨1520885,0,0,11855⟩
private theorem pos232 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp232 : (⟨(1520885/1160054),0,0,(11855/1160054)⟩ : CertField) = scaled n232 1160054 := by decide +kernel
private def n233 : IntField := ⟨1341,0,0,(-1)⟩
private theorem pos233 : (0:ℤ) < 3526 := by decide +kernel
private theorem cp233 : (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) = scaled n233 3526 := by decide +kernel
private def n234 : IntField := ⟨2129239,0,0,16597⟩
private theorem pos234 : (0:ℤ) < 828610 := by decide +kernel
private theorem cp234 : (⟨(2129239/828610),0,0,(16597/828610)⟩ : CertField) = scaled n234 828610 := by decide +kernel
private def n235 : IntField := ⟨3927,0,0,(-31)⟩
private theorem pos235 : (0:ℤ) < 1974 := by decide +kernel
private theorem cp235 : (⟨(187/94),0,0,(-31/1974)⟩ : CertField) = scaled n235 1974 := by decide +kernel
private def n236 : IntField := ⟨3192489,(-1103911),0,0⟩
private theorem pos236 : (0:ℤ) < 2634918 := by decide +kernel
private theorem cp236 : (⟨(1064163/878306),(-1103911/2634918),0,0⟩ : CertField) = scaled n236 2634918 := by decide +kernel
private def n237 : IntField := ⟨95261469,(-32011552),0,0⟩
private theorem pos237 : (0:ℤ) < 81646851 := by decide +kernel
private theorem cp237 : (⟨(31753823/27215617),(-32011552/81646851),0,0⟩ : CertField) = scaled n237 81646851 := by decide +kernel
private def n238 : IntField := ⟨1043795,(-348332),0,0⟩
private theorem pos238 : (0:ℤ) < 894179 := by decide +kernel
private theorem cp238 : (⟨(1043795/894179),(-348332/894179),0,0⟩ : CertField) = scaled n238 894179 := by decide +kernel
private def n239 : IntField := ⟨(-92974),79215,0,0⟩
private theorem pos239 : (0:ℤ) < 101343 := by decide +kernel
private theorem cp239 : (⟨(-92974/101343),(26405/33781),0,0⟩ : CertField) = scaled n239 101343 := by decide +kernel
private def n240 : IntField := ⟨(-2086470),1739113,0,0⟩
private theorem pos240 : (0:ℤ) < 2114508 := by decide +kernel
private theorem cp240 : (⟨(-347745/352418),(1739113/2114508),0,0⟩ : CertField) = scaled n240 2114508 := by decide +kernel
private def n241 : IntField := ⟨(-13629),11923,0,0⟩
private theorem pos241 : (0:ℤ) < 15873 := by decide +kernel
private theorem cp241 : (⟨(-413/481),(11923/15873),0,0⟩ : CertField) = scaled n241 15873 := by decide +kernel
private def n242 : IntField := ⟨(-310436),548976,0,0⟩
private theorem pos242 : (0:ℤ) < 1317459 := by decide +kernel
private theorem cp242 : (⟨(-310436/1317459),(182992/439153),0,0⟩ : CertField) = scaled n242 1317459 := by decide +kernel
private def n243 : IntField := ⟨(-1816839),2983688,0,0⟩
private theorem pos243 : (0:ℤ) < 6872151 := by decide +kernel
private theorem cp243 : (⟨(-605613/2290717),(2983688/6872151),0,0⟩ : CertField) = scaled n243 6872151 := by decide +kernel
private def n244 : IntField := ⟨(-2807),6130,0,0⟩
private theorem pos244 : (0:ℤ) < 15873 := by decide +kernel
private theorem cp244 : (⟨(-2807/15873),(6130/15873),0,0⟩ : CertField) = scaled n244 15873 := by decide +kernel
private def n245 : IntField := ⟨2316036,762601,0,0⟩
private theorem pos245 : (0:ℤ) < 2293177 := by decide +kernel
private theorem cp245 : (⟨(2316036/2293177),(762601/2293177),0,0⟩ : CertField) = scaled n245 2293177 := by decide +kernel
private def n246 : IntField := ⟨16794977,5158262,0,0⟩
private theorem pos246 : (0:ℤ) < 16501418 := by decide +kernel
private theorem cp246 : (⟨(16794977/16501418),(2579131/8250709),0,0⟩ : CertField) = scaled n246 16501418 := by decide +kernel
private def n247 : IntField := ⟨59115,0,0,(-907)⟩
private theorem pos247 : (0:ℤ) < 20310 := by decide +kernel
private theorem cp247 : (⟨(3941/1354),0,0,(-907/20310)⟩ : CertField) = scaled n247 20310 := by decide +kernel
private def n248 : IntField := ⟨13766,29019,0,0⟩
private theorem pos248 : (0:ℤ) < 50713 := by decide +kernel
private theorem cp248 : (⟨(13766/50713),(29019/50713),0,0⟩ : CertField) = scaled n248 50713 := by decide +kernel
private def n249 : IntField := ⟨922125,0,0,(-75625)⟩
private theorem pos249 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp249 : (⟨(922125/1160054),0,0,(-75625/1160054)⟩ : CertField) = scaled n249 1160054 := by decide +kernel
private def n250 : IntField := ⟨(-64511),814289,0,0⟩
private theorem pos250 : (0:ℤ) < 1224914 := by decide +kernel
private theorem cp250 : (⟨(-64511/1224914),(814289/1224914),0,0⟩ : CertField) = scaled n250 1224914 := by decide +kernel
private def n251 : IntField := ⟨731,(-1),0,0⟩
private theorem pos251 : (0:ℤ) < 2497 := by decide +kernel
private theorem cp251 : (⟨(731/2497),(-1/2497),0,0⟩ : CertField) = scaled n251 2497 := by decide +kernel
private def n252 : IntField := ⟨376986,542948,0,0⟩
private theorem pos252 : (0:ℤ) < 1135849 := by decide +kernel
private theorem cp252 : (⟨(376986/1135849),(542948/1135849),0,0⟩ : CertField) = scaled n252 1135849 := by decide +kernel
private def n253 : IntField := ⟨581,0,0,(-4)⟩
private theorem pos253 : (0:ℤ) < 329 := by decide +kernel
private theorem cp253 : (⟨(83/47),0,0,(-4/329)⟩ : CertField) = scaled n253 329 := by decide +kernel
private def n254 : IntField := ⟨295575,0,0,(-4535)⟩
private theorem pos254 : (0:ℤ) < 199038 := by decide +kernel
private theorem cp254 : (⟨(14075/9478),0,0,(-4535/199038)⟩ : CertField) = scaled n254 199038 := by decide +kernel
private def n255 : IntField := ⟨(-29697),96839,0,0⟩
private theorem pos255 : (0:ℤ) < 138697 := by decide +kernel
private theorem cp255 : (⟨(-29697/138697),(96839/138697),0,0⟩ : CertField) = scaled n255 138697 := by decide +kernel
private def n256 : IntField := ⟨1007355,0,0,(-21065)⟩
private theorem pos256 : (0:ℤ) < 2251802 := by decide +kernel
private theorem cp256 : (⟨(1007355/2251802),0,0,(-21065/2251802)⟩ : CertField) = scaled n256 2251802 := by decide +kernel
private def n257 : IntField := ⟨(-1608438),1758380,0,0⟩
private theorem pos257 : (0:ℤ) < 1675033 := by decide +kernel
private theorem cp257 : (⟨(-1608438/1675033),(1758380/1675033),0,0⟩ : CertField) = scaled n257 1675033 := by decide +kernel
private def n258 : IntField := ⟨22155,0,0,2123⟩
private theorem pos258 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp258 : (⟨(3165/8282),0,0,(2123/57974)⟩ : CertField) = scaled n258 57974 := by decide +kernel
private def n259 : IntField := ⟨1413,(-1),0,0⟩
private theorem pos259 : (0:ℤ) < 4654 := by decide +kernel
private theorem cp259 : (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = scaled n259 4654 := by decide +kernel
private def n260 : IntField := ⟨(-1405947),6145065,0,0⟩
private theorem pos260 : (0:ℤ) < 10207366 := by decide +kernel
private theorem cp260 : (⟨(-1405947/10207366),(6145065/10207366),0,0⟩ : CertField) = scaled n260 10207366 := by decide +kernel
private def n261 : IntField := ⟨439845,0,0,34225⟩
private theorem pos261 : (0:ℤ) < 199038 := by decide +kernel
private theorem cp261 : (⟨(20945/9478),0,0,(34225/199038)⟩ : CertField) = scaled n261 199038 := by decide +kernel
private def n262 : IntField := ⟨87969,0,0,6845⟩
private theorem pos262 : (0:ℤ) < 20310 := by decide +kernel
private theorem cp262 : (⟨(29323/6770),0,0,(1369/4062)⟩ : CertField) = scaled n262 20310 := by decide +kernel
private def n263 : IntField := ⟨6699,0,0,395⟩
private theorem pos263 : (0:ℤ) < 1974 := by decide +kernel
private theorem cp263 : (⟨(319/94),0,0,(395/1974)⟩ : CertField) = scaled n263 1974 := by decide +kernel
private def n264 : IntField := ⟨2389135,0,0,11720⟩
private theorem pos264 : (0:ℤ) < 10951829 := by decide +kernel
private theorem cp264 : (⟨(341305/1564547),0,0,(11720/10951829)⟩ : CertField) = scaled n264 10951829 := by decide +kernel
private def n265 : IntField := ⟨2555,0,0,(-232)⟩
private theorem pos265 : (0:ℤ) < 4739 := by decide +kernel
private theorem cp265 : (⟨(365/677),0,0,(-232/4739)⟩ : CertField) = scaled n265 4739 := by decide +kernel
private def n266 : IntField := ⟨(-8563189),17479377,0,0⟩
private theorem pos266 : (0:ℤ) < 52684372 := by decide +kernel
private theorem cp266 : (⟨(-8563189/52684372),(17479377/52684372),0,0⟩ : CertField) = scaled n266 52684372 := by decide +kernel
private def n267 : IntField := ⟨3344789,0,0,16408⟩
private theorem pos267 : (0:ℤ) < 7822735 := by decide +kernel
private theorem cp267 : (⟨(3344789/7822735),0,0,(16408/7822735)⟩ : CertField) = scaled n267 7822735 := by decide +kernel
private def n268 : IntField := ⟨5265060656,(-1995772076),0,0⟩
private theorem pos268 : (0:ℤ) < 3004340799 := by decide +kernel
private theorem cp268 : (⟨(5265060656/3004340799),(-1995772076/3004340799),0,0⟩ : CertField) = scaled n268 3004340799 := by decide +kernel
private def n269 : IntField := ⟨241283046042,(-80769866134),0,0⟩
private theorem pos269 : (0:ℤ) < 165650874873 := by decide +kernel
private theorem cp269 : (⟨(80427682014/55216958291),(-80769866134/165650874873),0,0⟩ : CertField) = scaled n269 165650874873 := by decide +kernel
private def n270 : IntField := ⟨140862474075,(-16043976857),0,0⟩
private theorem pos270 : (0:ℤ) < 163148767737 := by decide +kernel
private theorem cp270 : (⟨(46954158025/54382922579),(-16043976857/163148767737),0,0⟩ : CertField) = scaled n270 163148767737 := by decide +kernel
private def n271 : IntField := ⟨972627,416997,0,0⟩
private theorem pos271 : (0:ℤ) < 1062082 := by decide +kernel
private theorem cp271 : (⟨(972627/1062082),(59571/151726),0,0⟩ : CertField) = scaled n271 1062082 := by decide +kernel
private def n272 : IntField := ⟨54884910,21043743,0,0⟩
private theorem pos272 : (0:ℤ) < 59249003 := by decide +kernel
private theorem cp272 : (⟨(54884910/59249003),(21043743/59249003),0,0⟩ : CertField) = scaled n272 59249003 := by decide +kernel
private def n273 : IntField := ⟨1758829,679351,0,0⟩
private theorem pos273 : (0:ℤ) < 1852277 := by decide +kernel
private theorem cp273 : (⟨(1758829/1852277),(679351/1852277),0,0⟩ : CertField) = scaled n273 1852277 := by decide +kernel
private def n274 : IntField := ⟨5787,(-1),0,0⟩
private theorem pos274 : (0:ℤ) < 14838 := by decide +kernel
private theorem cp274 : (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) = scaled n274 14838 := by decide +kernel
private def n275 : IntField := ⟨13125251,4796555,0,0⟩
private theorem pos275 : (0:ℤ) < 14262244 := by decide +kernel
private theorem cp275 : (⟨(13125251/14262244),(4796555/14262244),0,0⟩ : CertField) = scaled n275 14262244 := by decide +kernel
private def n276 : IntField := ⟨578159889,158601532,0,0⟩
private theorem pos276 : (0:ℤ) < 586345127 := by decide +kernel
private theorem cp276 : (⟨(578159889/586345127),(158601532/586345127),0,0⟩ : CertField) = scaled n276 586345127 := by decide +kernel
private def n277 : IntField := ⟨72484603,22447511,0,0⟩
private theorem pos277 : (0:ℤ) < 74620302 := by decide +kernel
private theorem cp277 : (⟨(72484603/74620302),(22447511/74620302),0,0⟩ : CertField) = scaled n277 74620302 := by decide +kernel
private def n278 : IntField := ⟨15100278,4563022,0,0⟩
private theorem pos278 : (0:ℤ) < 14953519 := by decide +kernel
private theorem cp278 : (⟨(15100278/14953519),(4563022/14953519),0,0⟩ : CertField) = scaled n278 14953519 := by decide +kernel
private def n279 : IntField := ⟨1769568852,409725352,0,0⟩
private theorem pos279 : (0:ℤ) < 1668385477 := by decide +kernel
private theorem cp279 : (⟨(1769568852/1668385477),(409725352/1668385477),0,0⟩ : CertField) = scaled n279 1668385477 := by decide +kernel
private def n280 : IntField := ⟨108863233,29134455,0,0⟩
private theorem pos280 : (0:ℤ) < 104316086 := by decide +kernel
private theorem cp280 : (⟨(108863233/104316086),(4162065/14902298),0,0⟩ : CertField) = scaled n280 104316086 := by decide +kernel
private def n281 : IntField := ⟨31,0,0,0⟩
private theorem pos281 : (0:ℤ) < 100 := by decide +kernel
private theorem cp281 : (⟨(31/100),0,0,0⟩ : CertField) = scaled n281 100 := by decide +kernel
private def n282 : IntField := ⟨(-14207442),10860688,0,0⟩
private theorem pos282 : (0:ℤ) < 15174291 := by decide +kernel
private theorem cp282 : (⟨(-4735814/5058097),(10860688/15174291),0,0⟩ : CertField) = scaled n282 15174291 := by decide +kernel
private def n283 : IntField := ⟨4519,(-1),0,0⟩
private theorem pos283 : (0:ℤ) < 12598 := by decide +kernel
private theorem cp283 : (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = scaled n283 12598 := by decide +kernel
private def n284 : IntField := ⟨2,(-1),0,0⟩
private theorem pos284 : (0:ℤ) < 1 := by decide +kernel
private theorem cp284 : (⟨2,-1,0,0⟩ : CertField) = scaled n284 1 := by decide +kernel
private def n285 : IntField := ⟨7469552,(-2765481),0,0⟩
private theorem pos285 : (0:ℤ) < 7968235 := by decide +kernel
private theorem cp285 : (⟨(7469552/7968235),(-2765481/7968235),0,0⟩ : CertField) = scaled n285 7968235 := by decide +kernel
private def n286 : IntField := ⟨(-35971057),60750714,0,0⟩
private theorem pos286 : (0:ℤ) < 197265783 := by decide +kernel
private theorem cp286 : (⟨(-35971057/197265783),(20250238/65755261),0,0⟩ : CertField) = scaled n286 197265783 := by decide +kernel
private def n287 : IntField := ⟨677899,177747,0,0⟩
private theorem pos287 : (0:ℤ) < 922502 := by decide +kernel
private theorem cp287 : (⟨(677899/922502),(177747/922502),0,0⟩ : CertField) = scaled n287 922502 := by decide +kernel
private def n288 : IntField := ⟨83,1,0,0⟩
private theorem pos288 : (0:ℤ) < 313 := by decide +kernel
private theorem cp288 : (⟨(83/313),(1/313),0,0⟩ : CertField) = scaled n288 313 := by decide +kernel
private def n289 : IntField := ⟨93,1,0,0⟩
private theorem pos289 : (0:ℤ) < 262 := by decide +kernel
private theorem cp289 : (⟨(93/262),(1/262),0,0⟩ : CertField) = scaled n289 262 := by decide +kernel
private def n290 : IntField := ⟨34471293,8562275,0,0⟩
private theorem pos290 : (0:ℤ) < 46454565 := by decide +kernel
private theorem cp290 : (⟨(11490431/15484855),(1712455/9290913),0,0⟩ : CertField) = scaled n290 46454565 := by decide +kernel
private def n291 : IntField := ⟨1590,1,0,0⟩
private theorem pos291 : (0:ℤ) < 5893 := by decide +kernel
private theorem cp291 : (⟨(1590/5893),(1/5893),0,0⟩ : CertField) = scaled n291 5893 := by decide +kernel
private def n292 : IntField := ⟨1759149,0,0,37499⟩
private theorem pos292 : (0:ℤ) < 1315290 := by decide +kernel
private theorem cp292 : (⟨(586383/438430),0,0,(37499/1315290)⟩ : CertField) = scaled n292 1315290 := by decide +kernel
private def n293 : IntField := ⟨1491,0,0,1⟩
private theorem pos293 : (0:ℤ) < 5530 := by decide +kernel
private theorem cp293 : (⟨(213/790),0,0,(1/5530)⟩ : CertField) = scaled n293 5530 := by decide +kernel
private def n294 : IntField := ⟨121,0,0,(-1)⟩
private theorem pos294 : (0:ℤ) < 430 := by decide +kernel
private theorem cp294 : (⟨(121/430),0,0,(-1/430)⟩ : CertField) = scaled n294 430 := by decide +kernel
private def n295 : IntField := ⟨1859,0,0,1⟩
private theorem pos295 : (0:ℤ) < 5158 := by decide +kernel
private theorem cp295 : (⟨(1859/5158),0,0,(1/5158)⟩ : CertField) = scaled n295 5158 := by decide +kernel
private def n296 : IntField := ⟨59273105,13426007,0,0⟩
private theorem pos296 : (0:ℤ) < 77757764 := by decide +kernel
private theorem cp296 : (⟨(59273105/77757764),(1918001/11108252),0,0⟩ : CertField) = scaled n296 77757764 := by decide +kernel
private def n297 : IntField := ⟨1991,1,0,0⟩
private theorem pos297 : (0:ℤ) < 5521 := by decide +kernel
private theorem cp297 : (⟨(1991/5521),(1/5521),0,0⟩ : CertField) = scaled n297 5521 := by decide +kernel
private def n298 : IntField := ⟨1586290,3840344,0,0⟩
private theorem pos298 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp298 : (⟨(1586290/10727197),(3840344/10727197),0,0⟩ : CertField) = scaled n298 10727197 := by decide +kernel
private def n299 : IntField := ⟨1256535,0,0,26785⟩
private theorem pos299 : (0:ℤ) < 1841406 := by decide +kernel
private theorem cp299 : (⟨(59835/87686),0,0,(26785/1841406)⟩ : CertField) = scaled n299 1841406 := by decide +kernel
private def n300 : IntField := ⟨2619,0,0,(-451)⟩
private theorem pos300 : (0:ℤ) < 510 := by decide +kernel
private theorem cp300 : (⟨(873/170),0,0,(-451/510)⟩ : CertField) = scaled n300 510 := by decide +kernel
private def n301 : IntField := ⟨27,0,0,1⟩
private theorem pos301 : (0:ℤ) < 118 := by decide +kernel
private theorem cp301 : (⟨(27/118),0,0,(1/118)⟩ : CertField) = scaled n301 118 := by decide +kernel
private def n302 : IntField := ⟨615684,448863,0,0⟩
private theorem pos302 : (0:ℤ) < 1064531 := by decide +kernel
private theorem cp302 : (⟨(615684/1064531),(448863/1064531),0,0⟩ : CertField) = scaled n302 1064531 := by decide +kernel
private def n303 : IntField := ⟨241,0,0,(-44)⟩
private theorem pos303 : (0:ℤ) < 85 := by decide +kernel
private theorem cp303 : (⟨(241/85),0,0,(-44/85)⟩ : CertField) = scaled n303 85 := by decide +kernel
private def n304 : IntField := ⟨61,1,0,0⟩
private theorem pos304 : (0:ℤ) < 169 := by decide +kernel
private theorem cp304 : (⟨(61/169),(1/169),0,0⟩ : CertField) = scaled n304 169 := by decide +kernel
private def n305 : IntField := ⟨210711,0,0,14399⟩
private theorem pos305 : (0:ℤ) < 458430 := by decide +kernel
private theorem cp305 : (⟨(70237/152810),0,0,(2057/65490)⟩ : CertField) = scaled n305 458430 := by decide +kernel
private def n306 : IntField := ⟨1089,0,0,1⟩
private theorem pos306 : (0:ℤ) < 2950 := by decide +kernel
private theorem cp306 : (⟨(1089/2950),0,0,(1/2950)⟩ : CertField) = scaled n306 2950 := by decide +kernel
private def n307 : IntField := ⟨87,0,0,(-1)⟩
private theorem pos307 : (0:ℤ) < 222 := by decide +kernel
private theorem cp307 : (⟨(29/74),0,0,(-1/222)⟩ : CertField) = scaled n307 222 := by decide +kernel
private def n308 : IntField := ⟨77513961,66212564,0,0⟩
private theorem pos308 : (0:ℤ) < 167131367 := by decide +kernel
private theorem cp308 : (⟨(77513961/167131367),(66212564/167131367),0,0⟩ : CertField) = scaled n308 167131367 := by decide +kernel
private def n309 : IntField := ⟨88747320,37227830,0,0⟩
private theorem pos309 : (0:ℤ) < 128644477 := by decide +kernel
private theorem cp309 : (⟨(88747320/128644477),(37227830/128644477),0,0⟩ : CertField) = scaled n309 128644477 := by decide +kernel
private def n310 : IntField := ⟨1161,1,0,0⟩
private theorem pos310 : (0:ℤ) < 3142 := by decide +kernel
private theorem cp310 : (⟨(1161/3142),(1/3142),0,0⟩ : CertField) = scaled n310 3142 := by decide +kernel
private def n311 : IntField := ⟨1384994,(-714779),0,0⟩
private theorem pos311 : (0:ℤ) < 867613 := by decide +kernel
private theorem cp311 : (⟨(1384994/867613),(-714779/867613),0,0⟩ : CertField) = scaled n311 867613 := by decide +kernel
private def n312 : IntField := ⟨4949,0,0,(-451)⟩
private theorem pos312 : (0:ℤ) < 4214 := by decide +kernel
private theorem cp312 : (⟨(101/86),0,0,(-451/4214)⟩ : CertField) = scaled n312 4214 := by decide +kernel
private def n313 : IntField := ⟨20949305,(-9833499),0,0⟩
private theorem pos313 : (0:ℤ) < 22604836 := by decide +kernel
private theorem cp313 : (⟨(20949305/22604836),(-9833499/22604836),0,0⟩ : CertField) = scaled n313 22604836 := by decide +kernel
private def n314 : IntField := ⟨21,0,0,1⟩
private theorem pos314 : (0:ℤ) < 70 := by decide +kernel
private theorem cp314 : (⟨(3/10),0,0,(1/70)⟩ : CertField) = scaled n314 70 := by decide +kernel
private def n315 : IntField := ⟨2615,0,0,(-1)⟩
private theorem pos315 : (0:ℤ) < 7138 := by decide +kernel
private theorem cp315 : (⟨(2615/7138),0,0,(-1/7138)⟩ : CertField) = scaled n315 7138 := by decide +kernel
private def n316 : IntField := ⟨4949,0,0,(-451)⟩
private theorem pos316 : (0:ℤ) < 2150 := by decide +kernel
private theorem cp316 : (⟨(4949/2150),0,0,(-451/2150)⟩ : CertField) = scaled n316 2150 := by decide +kernel
private def n317 : IntField := ⟨7833,0,0,(-187)⟩
private theorem pos317 : (0:ℤ) < 7770 := by decide +kernel
private theorem cp317 : (⟨(373/370),0,0,(-187/7770)⟩ : CertField) = scaled n317 7770 := by decide +kernel
private def n318 : IntField := ⟨3510339,(-1718470),0,0⟩
private theorem pos318 : (0:ℤ) < 2796719 := by decide +kernel
private theorem cp318 : (⟨(3510339/2796719),(-1718470/2796719),0,0⟩ : CertField) = scaled n318 2796719 := by decide +kernel
private def n319 : IntField := ⟨2747,(-1),0,0⟩
private theorem pos319 : (0:ℤ) < 7501 := by decide +kernel
private theorem cp319 : (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = scaled n319 7501 := by decide +kernel
private def n320 : IntField := ⟨789249,0,0,121589⟩
private theorem pos320 : (0:ℤ) < 1841406 := by decide +kernel
private theorem cp320 : (⟨(263083/613802),0,0,(121589/1841406)⟩ : CertField) = scaled n320 1841406 := by decide +kernel
private def n321 : IntField := ⟨30157521,(-14005655),0,0⟩
private theorem pos321 : (0:ℤ) < 33907254 := by decide +kernel
private theorem cp321 : (⟨(10052507/11302418),(-14005655/33907254),0,0⟩ : CertField) = scaled n321 33907254 := by decide +kernel
private def n322 : IntField := ⟨303972265,(-127591766),0,0⟩
private theorem pos322 : (0:ℤ) < 465908181 := by decide +kernel
private theorem cp322 : (⟨(303972265/465908181),(-127591766/465908181),0,0⟩ : CertField) = scaled n322 465908181 := by decide +kernel
private def n323 : IntField := ⟨338003377,(-141533453),0,0⟩
private theorem pos323 : (0:ℤ) < 473628142 := by decide +kernel
private theorem cp323 : (⟨(338003377/473628142),(-141533453/473628142),0,0⟩ : CertField) = scaled n323 473628142 := by decide +kernel
private def n324 : IntField := ⟨5524743,0,0,851123⟩
private theorem pos324 : (0:ℤ) < 6576450 := by decide +kernel
private theorem cp324 : (⟨(1841581/2192150),0,0,(851123/6576450)⟩ : CertField) = scaled n324 6576450 := by decide +kernel
private def n325 : IntField := ⟨2103,0,0,(-329)⟩
private theorem pos325 : (0:ℤ) < 510 := by decide +kernel
private theorem cp325 : (⟨(701/170),0,0,(-329/510)⟩ : CertField) = scaled n325 510 := by decide +kernel
private def n326 : IntField := ⟨30853093,(-13656585),0,0⟩
private theorem pos326 : (0:ℤ) < 36565583 := by decide +kernel
private theorem cp326 : (⟨(30853093/36565583),(-13656585/36565583),0,0⟩ : CertField) = scaled n326 36565583 := by decide +kernel
private def n327 : IntField := ⟨245288306,(-86222743),0,0⟩
private theorem pos327 : (0:ℤ) < 476340838 := by decide +kernel
private theorem cp327 : (⟨(122644153/238170419),(-86222743/476340838),0,0⟩ : CertField) = scaled n327 476340838 := by decide +kernel
private def n328 : IntField := ⟨59241606,(-19341618),0,0⟩
private theorem pos328 : (0:ℤ) < 117867829 := by decide +kernel
private theorem cp328 : (⟨(59241606/117867829),(-19341618/117867829),0,0⟩ : CertField) = scaled n328 117867829 := by decide +kernel
private def n329 : IntField := ⟨1385355,3126197,0,0⟩
private theorem pos329 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp329 : (⟨(1385355/10727197),(3126197/10727197),0,0⟩ : CertField) = scaled n329 10727197 := by decide +kernel
private def n330 : IntField := ⟨341,0,0,(-43)⟩
private theorem pos330 : (0:ℤ) < 170 := by decide +kernel
private theorem cp330 : (⟨(341/170),0,0,(-43/170)⟩ : CertField) = scaled n330 170 := by decide +kernel
private def n331 : IntField := ⟨295575,0,0,(-45425)⟩
private theorem pos331 : (0:ℤ) < 349762 := by decide +kernel
private theorem cp331 : (⟨(42225/49966),0,0,(-45425/349762)⟩ : CertField) = scaled n331 349762 := by decide +kernel
private def n332 : IntField := ⟨35662395,(-15351928),0,0⟩
private theorem pos332 : (0:ℤ) < 32359620 := by decide +kernel
private theorem cp332 : (⟨(2377493/2157308),(-3837982/8089905),0,0⟩ : CertField) = scaled n332 32359620 := by decide +kernel
private def n333 : IntField := ⟨11823,0,0,(-1817)⟩
private theorem pos333 : (0:ℤ) < 7138 := by decide +kernel
private theorem cp333 : (⟨(11823/7138),0,0,(-1817/7138)⟩ : CertField) = scaled n333 7138 := by decide +kernel
private def n334 : IntField := ⟨(-5855080),4134061,0,0⟩
private theorem pos334 : (0:ℤ) < 5135331 := by decide +kernel
private theorem cp334 : (⟨(-5855080/5135331),(4134061/5135331),0,0⟩ : CertField) = scaled n334 5135331 := by decide +kernel
private def n335 : IntField := ⟨(-178397697),138588056,0,0⟩
private theorem pos335 : (0:ℤ) < 215196189 := by decide +kernel
private theorem cp335 : (⟨(-59465899/71732063),(138588056/215196189),0,0⟩ : CertField) = scaled n335 215196189 := by decide +kernel
private def n336 : IntField := ⟨2317,0,0,(-53)⟩
private theorem pos336 : (0:ℤ) < 2590 := by decide +kernel
private theorem cp336 : (⟨(331/370),0,0,(-53/2590)⟩ : CertField) = scaled n336 2590 := by decide +kernel
private def n337 : IntField := ⟨194397,139809,0,0⟩
private theorem pos337 : (0:ℤ) < 163774 := by decide +kernel
private theorem cp337 : (⟨(194397/163774),(139809/163774),0,0⟩ : CertField) = scaled n337 163774 := by decide +kernel
private def n338 : IntField := ⟨164975997,132610256,0,0⟩
private theorem pos338 : (0:ℤ) < 167131367 := by decide +kernel
private theorem cp338 : (⟨(164975997/167131367),(132610256/167131367),0,0⟩ : CertField) = scaled n338 167131367 := by decide +kernel
private def n339 : IntField := ⟨179334165,76652585,0,0⟩
private theorem pos339 : (0:ℤ) < 128644477 := by decide +kernel
private theorem cp339 : (⟨(179334165/128644477),(76652585/128644477),0,0⟩ : CertField) = scaled n339 128644477 := by decide +kernel
private def n340 : IntField := ⟨113317,(-58057),0,0⟩
private theorem pos340 : (0:ℤ) < 39923 := by decide +kernel
private theorem cp340 : (⟨(113317/39923),(-58057/39923),0,0⟩ : CertField) = scaled n340 39923 := by decide +kernel
private def n341 : IntField := ⟨859250,(-397911),0,0⟩
private theorem pos341 : (0:ℤ) < 520078 := by decide +kernel
private theorem cp341 : (⟨(429625/260039),(-397911/520078),0,0⟩ : CertField) = scaled n341 520078 := by decide +kernel
private def n342 : IntField := ⟨22927,0,0,121⟩
private theorem pos342 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp342 : (⟨(22927/12314),0,0,(121/12314)⟩ : CertField) = scaled n342 12314 := by decide +kernel
private def n343 : IntField := ⟨143862,(-68665),0,0⟩
private theorem pos343 : (0:ℤ) < 68783 := by decide +kernel
private theorem cp343 : (⟨(143862/68783),(-68665/68783),0,0⟩ : CertField) = scaled n343 68783 := by decide +kernel
private def n344 : IntField := ⟨182571,0,0,25714⟩
private theorem pos344 : (0:ℤ) < 229215 := by decide +kernel
private theorem cp344 : (⟨(60857/76405),0,0,(25714/229215)⟩ : CertField) = scaled n344 229215 := by decide +kernel
private def n345 : IntField := ⟨16084572,(-7364405),0,0⟩
private theorem pos345 : (0:ℤ) < 10141521 := by decide +kernel
private theorem cp345 : (⟨(5361524/3380507),(-7364405/10141521),0,0⟩ : CertField) = scaled n345 10141521 := by decide +kernel
private def n346 : IntField := ⟨325056155,(-133599949),0,0⟩
private theorem pos346 : (0:ℤ) < 278702463 := by decide +kernel
private theorem cp346 : (⟨(325056155/278702463),(-133599949/278702463),0,0⟩ : CertField) = scaled n346 278702463 := by decide +kernel
private def n347 : IntField := ⟨1075417,(-428303),0,0⟩
private theorem pos347 : (0:ℤ) < 896038 := by decide +kernel
private theorem cp347 : (⟨(1075417/896038),(-428303/896038),0,0⟩ : CertField) = scaled n347 896038 := by decide +kernel
private def n348 : IntField := ⟨1277997,0,0,179998⟩
private theorem pos348 : (0:ℤ) < 818625 := by decide +kernel
private theorem cp348 : (⟨(425999/272875),0,0,(179998/818625)⟩ : CertField) = scaled n348 818625 := by decide +kernel
private def n349 : IntField := ⟨6531,0,0,286⟩
private theorem pos349 : (0:ℤ) < 3885 := by decide +kernel
private theorem cp349 : (⟨(311/185),0,0,(286/3885)⟩ : CertField) = scaled n349 3885 := by decide +kernel
private def n350 : IntField := ⟨8166794,(-3688227),0,0⟩
private theorem pos350 : (0:ℤ) < 4824541 := by decide +kernel
private theorem cp350 : (⟨(8166794/4824541),(-3688227/4824541),0,0⟩ : CertField) = scaled n350 4824541 := by decide +kernel
private def n351 : IntField := ⟨129082073,(-47154571),0,0⟩
private theorem pos351 : (0:ℤ) < 125698852 := by decide +kernel
private theorem cp351 : (⟨(129082073/125698852),(-47154571/125698852),0,0⟩ : CertField) = scaled n351 125698852 := by decide +kernel
private def n352 : IntField := ⟨102212817,(-33339399),0,0⟩
private theorem pos352 : (0:ℤ) < 108058093 := by decide +kernel
private theorem cp352 : (⟨(102212817/108058093),(-33339399/108058093),0,0⟩ : CertField) = scaled n352 108058093 := by decide +kernel
private def n353 : IntField := ⟨1474639,754191,0,0⟩
private theorem pos353 : (0:ℤ) < 1510223 := by decide +kernel
private theorem cp353 : (⟨(1474639/1510223),(754191/1510223),0,0⟩ : CertField) = scaled n353 1510223 := by decide +kernel
private def n354 : IntField := ⟨16314613,7455368,0,0⟩
private theorem pos354 : (0:ℤ) < 18238847 := by decide +kernel
private theorem cp354 : (⟨(16314613/18238847),(7455368/18238847),0,0⟩ : CertField) = scaled n354 18238847 := by decide +kernel
private def n355 : IntField := ⟨4877310,2214722,0,0⟩
private theorem pos355 : (0:ℤ) < 4868149 := by decide +kernel
private theorem cp355 : (⟨(4877310/4868149),(2214722/4868149),0,0⟩ : CertField) = scaled n355 4868149 := by decide +kernel
private def n356 : IntField := ⟨48731319,22981565,0,0⟩
private theorem pos356 : (0:ℤ) < 54716541 := by decide +kernel
private theorem cp356 : (⟨(16243773/18238847),(22981565/54716541),0,0⟩ : CertField) = scaled n356 54716541 := by decide +kernel
private def n357 : IntField := ⟨68144518,22261037,0,0⟩
private theorem pos357 : (0:ℤ) < 74581782 := by decide +kernel
private theorem cp357 : (⟨(34072259/37290891),(22261037/74581782),0,0⟩ : CertField) = scaled n357 74581782 := by decide +kernel
private def n358 : IntField := ⟨720674542,277946054,0,0⟩
private theorem pos358 : (0:ℤ) < 764299393 := by decide +kernel
private theorem cp358 : (⟨(720674542/764299393),(277946054/764299393),0,0⟩ : CertField) = scaled n358 764299393 := by decide +kernel
private def n359 : IntField := ⟨2667,0,0,(-253)⟩
private theorem pos359 : (0:ℤ) < 4690 := by decide +kernel
private theorem cp359 : (⟨(381/670),0,0,(-253/4690)⟩ : CertField) = scaled n359 4690 := by decide +kernel
private def n360 : IntField := ⟨251,0,0,(-1)⟩
private theorem pos360 : (0:ℤ) < 670 := by decide +kernel
private theorem cp360 : (⟨(251/670),0,0,(-1/670)⟩ : CertField) = scaled n360 670 := by decide +kernel
private def n361 : IntField := ⟨22700866,10519166,0,0⟩
private theorem pos361 : (0:ℤ) < 22704539 := by decide +kernel
private theorem cp361 : (⟨(22700866/22704539),(10519166/22704539),0,0⟩ : CertField) = scaled n361 22704539 := by decide +kernel
private def n362 : IntField := ⟨260311300,98013814,0,0⟩
private theorem pos362 : (0:ℤ) < 274200971 := by decide +kernel
private theorem cp362 : (⟨(260311300/274200971),(98013814/274200971),0,0⟩ : CertField) = scaled n362 274200971 := by decide +kernel
private def n363 : IntField := ⟨75037587,30655035,0,0⟩
private theorem pos363 : (0:ℤ) < 73187257 := by decide +kernel
private theorem cp363 : (⟨(75037587/73187257),(30655035/73187257),0,0⟩ : CertField) = scaled n363 73187257 := by decide +kernel
private def n364 : IntField := ⟨671227,499219,0,0⟩
private theorem pos364 : (0:ℤ) < 1541891 := by decide +kernel
private theorem cp364 : (⟨(671227/1541891),(499219/1541891),0,0⟩ : CertField) = scaled n364 1541891 := by decide +kernel
private def n365 : IntField := ⟨570051,0,0,(-65341)⟩
private theorem pos365 : (0:ℤ) < 2693670 := by decide +kernel
private theorem cp365 : (⟨(190017/897890),0,0,(-65341/2693670)⟩ : CertField) = scaled n365 2693670 := by decide +kernel
private def n366 : IntField := ⟨7389,0,0,1⟩
private theorem pos366 : (0:ℤ) < 19050 := by decide +kernel
private theorem cp366 : (⟨(2463/6350),0,0,(1/19050)⟩ : CertField) = scaled n366 19050 := by decide +kernel
private def n367 : IntField := ⟨6116773,5788260,0,0⟩
private theorem pos367 : (0:ℤ) < 18621299 := by decide +kernel
private theorem cp367 : (⟨(6116773/18621299),(5788260/18621299),0,0⟩ : CertField) = scaled n367 18621299 := by decide +kernel
private def n368 : IntField := ⟨17121447,7927814,0,0⟩
private theorem pos368 : (0:ℤ) < 34534643 := by decide +kernel
private theorem cp368 : (⟨(17121447/34534643),(7927814/34534643),0,0⟩ : CertField) = scaled n368 34534643 := by decide +kernel
private def n369 : IntField := ⟨19320603,17076737,0,0⟩
private theorem pos369 : (0:ℤ) < 55863897 := by decide +kernel
private theorem cp369 : (⟨(6440201/18621299),(17076737/55863897),0,0⟩ : CertField) = scaled n369 55863897 := by decide +kernel
private def n370 : IntField := ⟨40953,0,0,(-3667)⟩
private theorem pos370 : (0:ℤ) < 178770 := by decide +kernel
private theorem cp370 : (⟨(13651/59590),0,0,(-3667/178770)⟩ : CertField) = scaled n370 178770 := by decide +kernel
private def n371 : IntField := ⟨12465754,26826693,0,0⟩
private theorem pos371 : (0:ℤ) < 76145694 := by decide +kernel
private theorem cp371 : (⟨(6232877/38072847),(8942231/25381898),0,0⟩ : CertField) = scaled n371 76145694 := by decide +kernel
private def n372 : IntField := ⟨258195,0,0,(-21175)⟩
private theorem pos372 : (0:ℤ) < 165722 := by decide +kernel
private theorem cp372 : (⟨(258195/165722),0,0,(-21175/165722)⟩ : CertField) = scaled n372 165722 := by decide +kernel
private def n373 : IntField := ⟨193668946,77221239,0,0⟩
private theorem pos373 : (0:ℤ) < 417072227 := by decide +kernel
private theorem cp373 : (⟨(193668946/417072227),(77221239/417072227),0,0⟩ : CertField) = scaled n373 417072227 := by decide +kernel
private def n374 : IntField := ⟨22564,15573,0,0⟩
private theorem pos374 : (0:ℤ) < 50713 := by decide +kernel
private theorem cp374 : (⟨(22564/50713),(15573/50713),0,0⟩ : CertField) = scaled n374 50713 := by decide +kernel
private def n375 : IntField := ⟨3990357,0,0,(-457387)⟩
private theorem pos375 : (0:ℤ) < 9620250 := by decide +kernel
private theorem cp375 : (⟨(1330119/3206750),0,0,(-457387/9620250)⟩ : CertField) = scaled n375 9620250 := by decide +kernel
private def n376 : IntField := ⟨30639607,24993995,0,0⟩
private theorem pos376 : (0:ℤ) < 86968894 := by decide +kernel
private theorem cp376 : (⟨(30639607/86968894),(24993995/86968894),0,0⟩ : CertField) = scaled n376 86968894 := by decide +kernel
private def n377 : IntField := ⟨574040,241790,0,0⟩
private theorem pos377 : (0:ℤ) < 1135849 := by decide +kernel
private theorem cp377 : (⟨(574040/1135849),(241790/1135849),0,0⟩ : CertField) = scaled n377 1135849 := by decide +kernel
private def n378 : IntField := ⟨530634,(-271739),0,0⟩
private theorem pos378 : (0:ℤ) < 495541 := by decide +kernel
private theorem cp378 : (⟨(530634/495541),(-271739/495541),0,0⟩ : CertField) = scaled n378 495541 := by decide +kernel
private def n379 : IntField := ⟨3143105,0,0,311040⟩
private theorem pos379 : (0:ℤ) < 7881307 := by decide +kernel
private theorem cp379 : (⟨(64145/160843),0,0,(311040/7881307)⟩ : CertField) = scaled n379 7881307 := by decide +kernel
private def n380 : IntField := ⟨8048625,(-3724019),0,0⟩
private theorem pos380 : (0:ℤ) < 12910852 := by decide +kernel
private theorem cp380 : (⟨(8048625/12910852),(-3724019/12910852),0,0⟩ : CertField) = scaled n380 12910852 := by decide +kernel
private def n381 : IntField := ⟨11762541,(-5322545),0,0⟩
private theorem pos381 : (0:ℤ) < 18234599 := by decide +kernel
private theorem cp381 : (⟨(11762541/18234599),(-5322545/18234599),0,0⟩ : CertField) = scaled n381 18234599 := by decide +kernel
private def n382 : IntField := ⟨3863267,(-1767205),0,0⟩
private theorem pos382 : (0:ℤ) < 6455426 := by decide +kernel
private theorem cp382 : (⟨(3863267/6455426),(-1767205/6455426),0,0⟩ : CertField) = scaled n382 6455426 := by decide +kernel
private def n383 : IntField := ⟨117128745,(-48075646),0,0⟩
private theorem pos383 : (0:ℤ) < 266105517 := by decide +kernel
private theorem cp383 : (⟨(39042915/88701839),(-48075646/266105517),0,0⟩ : CertField) = scaled n383 266105517 := by decide +kernel
private def n384 : IntField := ⟨44781028,(-16029627),0,0⟩
private theorem pos384 : (0:ℤ) < 118771307 := by decide +kernel
private theorem cp384 : (⟨(44781028/118771307),(-16029627/118771307),0,0⟩ : CertField) = scaled n384 118771307 := by decide +kernel
private def n385 : IntField := ⟨5839677,(-2780866),0,0⟩
private theorem pos385 : (0:ℤ) < 7449913 := by decide +kernel
private theorem cp385 : (⟨(5839677/7449913),(-2780866/7449913),0,0⟩ : CertField) = scaled n385 7449913 := by decide +kernel
private def n386 : IntField := ⟨90786309,(-36671293),0,0⟩
private theorem pos386 : (0:ℤ) < 194100436 := by decide +kernel
private theorem cp386 : (⟨(90786309/194100436),(-36671293/194100436),0,0⟩ : CertField) = scaled n386 194100436 := by decide +kernel
private def n387 : IntField := ⟨98170698,(-32019006),0,0⟩
private theorem pos387 : (0:ℤ) < 274137107 := by decide +kernel
private theorem cp387 : (⟨(98170698/274137107),(-32019006/274137107),0,0⟩ : CertField) = scaled n387 274137107 := by decide +kernel
private def n388 : IntField := ⟨14759,27704,0,0⟩
private theorem pos388 : (0:ℤ) < 63661 := by decide +kernel
private theorem cp388 : (⟨(14759/63661),(27704/63661),0,0⟩ : CertField) = scaled n388 63661 := by decide +kernel
private def n389 : IntField := ⟨566107,0,0,39413⟩
private theorem pos389 : (0:ℤ) < 1696450 := by decide +kernel
private theorem cp389 : (⟨(566107/1696450),0,0,(39413/1696450)⟩ : CertField) = scaled n389 1696450 := by decide +kernel
private def n390 : IntField := ⟨1099455,0,0,(-119990)⟩
private theorem pos390 : (0:ℤ) < 580027 := by decide +kernel
private theorem cp390 : (⟨(157065/82861),0,0,(-119990/580027)⟩ : CertField) = scaled n390 580027 := by decide +kernel
private def n391 : IntField := ⟨1539237,0,0,(-167986)⟩
private theorem pos391 : (0:ℤ) < 414305 := by decide +kernel
private theorem cp391 : (⟨(1539237/414305),0,0,(-167986/414305)⟩ : CertField) = scaled n391 414305 := by decide +kernel
private def n392 : IntField := ⟨5115,0,0,494⟩
private theorem pos392 : (0:ℤ) < 6157 := by decide +kernel
private theorem cp392 : (⟨(5115/6157),0,0,(494/6157)⟩ : CertField) = scaled n392 6157 := by decide +kernel
private def n393 : IntField := ⟨207759,1042741,0,0⟩
private theorem pos393 : (0:ℤ) < 2306487 := by decide +kernel
private theorem cp393 : (⟨(69253/768829),(1042741/2306487),0,0⟩ : CertField) = scaled n393 2306487 := by decide +kernel
private def n394 : IntField := ⟨262658,348954,0,0⟩
private theorem pos394 : (0:ℤ) < 957073 := by decide +kernel
private theorem cp394 : (⟨(262658/957073),(348954/957073),0,0⟩ : CertField) = scaled n394 957073 := by decide +kernel
private def n395 : IntField := ⟨(-24396960),17468351,0,0⟩
private theorem pos395 : (0:ℤ) < 32263737 := by decide +kernel
private theorem cp395 : (⟨(-8132320/10754579),(17468351/32263737),0,0⟩ : CertField) = scaled n395 32263737 := by decide +kernel
private def n396 : IntField := ⟨50354195,(-21235216),0,0⟩
private theorem pos396 : (0:ℤ) < 67768580 := by decide +kernel
private theorem cp396 : (⟨(10070839/13553716),(-5308804/16942145),0,0⟩ : CertField) = scaled n396 67768580 := by decide +kernel
private def n397 : IntField := ⟨(-448345431),402336023,0,0⟩
private theorem pos397 : (0:ℤ) < 1187220243 := by decide +kernel
private theorem cp397 : (⟨(-149448477/395740081),(402336023/1187220243),0,0⟩ : CertField) = scaled n397 1187220243 := by decide +kernel
private def n398 : IntField := ⟨1378579,1010248,0,0⟩
private theorem pos398 : (0:ℤ) < 1541891 := by decide +kernel
private theorem cp398 : (⟨(1378579/1541891),(1010248/1541891),0,0⟩ : CertField) = scaled n398 1541891 := by decide +kernel
private def n399 : IntField := ⟨341361,0,0,(-10376)⟩
private theorem pos399 : (0:ℤ) < 1346835 := by decide +kernel
private theorem cp399 : (⟨(113787/448945),0,0,(-10376/1346835)⟩ : CertField) = scaled n399 1346835 := by decide +kernel
private def n400 : IntField := ⟨11910457,11928891,0,0⟩
private theorem pos400 : (0:ℤ) < 18621299 := by decide +kernel
private theorem cp400 : (⟨(11910457/18621299),(11928891/18621299),0,0⟩ : CertField) = scaled n400 18621299 := by decide +kernel
private def n401 : IntField := ⟨69347763,32526001,0,0⟩
private theorem pos401 : (0:ℤ) < 69069286 := by decide +kernel
private theorem cp401 : (⟨(69347763/69069286),(32526001/69069286),0,0⟩ : CertField) = scaled n401 69069286 := by decide +kernel
private def n402 : IntField := ⟨41275851,34140713,0,0⟩
private theorem pos402 : (0:ℤ) < 55863897 := by decide +kernel
private theorem cp402 : (⟨(13758617/18621299),(34140713/55863897),0,0⟩ : CertField) = scaled n402 55863897 := by decide +kernel
private def n403 : IntField := ⟨12705500,27270561,0,0⟩
private theorem pos403 : (0:ℤ) < 38072847 := by decide +kernel
private theorem cp403 : (⟨(12705500/38072847),(9090187/12690949),0,0⟩ : CertField) = scaled n403 38072847 := by decide +kernel
private def n404 : IntField := ⟨388324822,163972491,0,0⟩
private theorem pos404 : (0:ℤ) < 417072227 := by decide +kernel
private theorem cp404 : (⟨(388324822/417072227),(163972491/417072227),0,0⟩ : CertField) = scaled n404 417072227 := by decide +kernel
private def n405 : IntField := ⟨6563101,4482897,0,0⟩
private theorem pos405 : (0:ℤ) < 7201246 := by decide +kernel
private theorem cp405 : (⟨(6563101/7201246),(4482897/7201246),0,0⟩ : CertField) = scaled n405 7201246 := by decide +kernel
private def n406 : IntField := ⟨2389527,0,0,(-72632)⟩
private theorem pos406 : (0:ℤ) < 4810125 := by decide +kernel
private theorem cp406 : (⟨(796509/1603375),0,0,(-72632/4810125)⟩ : CertField) = scaled n406 4810125 := by decide +kernel
private def n407 : IntField := ⟨30213209,25619932,0,0⟩
private theorem pos407 : (0:ℤ) < 43484447 := by decide +kernel
private theorem cp407 : (⟨(30213209/43484447),(25619932/43484447),0,0⟩ : CertField) = scaled n407 43484447 := by decide +kernel
private def n408 : IntField := ⟨82365655,35341555,0,0⟩
private theorem pos408 : (0:ℤ) < 80645279 := by decide +kernel
private theorem cp408 : (⟨(82365655/80645279),(35341555/80645279),0,0⟩ : CertField) = scaled n408 80645279 := by decide +kernel
private def n409 : IntField := ⟨2177375,0,0,83125⟩
private theorem pos409 : (0:ℤ) < 21903658 := by decide +kernel
private theorem cp409 : (⟨(2177375/21903658),0,0,(11875/3129094)⟩ : CertField) = scaled n409 21903658 := by decide +kernel
private def n410 : IntField := ⟨6769,0,0,(-1121)⟩
private theorem pos410 : (0:ℤ) < 9478 := by decide +kernel
private theorem cp410 : (⟨(967/1354),0,0,(-1121/9478)⟩ : CertField) = scaled n410 9478 := by decide +kernel
private def n411 : IntField := ⟨(-784719),1774045,0,0⟩
private theorem pos411 : (0:ℤ) < 11144771 := by decide +kernel
private theorem cp411 : (⟨(-784719/11144771),(1774045/11144771),0,0⟩ : CertField) = scaled n411 11144771 := by decide +kernel
private def n412 : IntField := ⟨(-3305591),5323257,0,0⟩
private theorem pos412 : (0:ℤ) < 26342186 := by decide +kernel
private theorem cp412 : (⟨(-3305591/26342186),(5323257/26342186),0,0⟩ : CertField) = scaled n412 26342186 := by decide +kernel
private def n413 : IntField := ⟨609665,0,0,23275⟩
private theorem pos413 : (0:ℤ) < 3129094 := by decide +kernel
private theorem cp413 : (⟨(609665/3129094),0,0,(23275/3129094)⟩ : CertField) = scaled n413 3129094 := by decide +kernel
private def n414 : IntField := ⟨(-6088),52493,0,0⟩
private theorem pos414 : (0:ℤ) < 366553 := by decide +kernel
private theorem cp414 : (⟨(-6088/366553),(52493/366553),0,0⟩ : CertField) = scaled n414 366553 := by decide +kernel
private def n415 : IntField := ⟨89059389,63877233,0,0⟩
private theorem pos415 : (0:ℤ) < 200296174 := by decide +kernel
private theorem cp415 : (⟨(89059389/200296174),(63877233/200296174),0,0⟩ : CertField) = scaled n415 200296174 := by decide +kernel
private def n416 : IntField := ⟨392627001,373531548,0,0⟩
private theorem pos416 : (0:ℤ) < 1209480743 := by decide +kernel
private theorem cp416 : (⟨(392627001/1209480743),(373531548/1209480743),0,0⟩ : CertField) = scaled n416 1209480743 := by decide +kernel
private def n417 : IntField := ⟨1920033810,820805110,0,0⟩
private theorem pos417 : (0:ℤ) < 3685184893 := by decide +kernel
private theorem cp417 : (⟨(1920033810/3685184893),(820805110/3685184893),0,0⟩ : CertField) = scaled n417 3685184893 := by decide +kernel
private def n418 : IntField := ⟨(-94037445),66451517,0,0⟩
private theorem pos418 : (0:ℤ) < 221882259 := by decide +kernel
private theorem cp418 : (⟨(-31345815/73960753),(66451517/221882259),0,0⟩ : CertField) = scaled n418 221882259 := by decide +kernel
private def n419 : IntField := ⟨191109065,(-82168347),0,0⟩
private theorem pos419 : (0:ℤ) < 466054060 := by decide +kernel
private theorem cp419 : (⟨(38221813/93210812),(-82168347/466054060),0,0⟩ : CertField) = scaled n419 466054060 := by decide +kernel
private def n420 : IntField := ⟨(-138472771),129224168,0,0⟩
private theorem pos420 : (0:ℤ) < 773927823 := by decide +kernel
private theorem cp420 : (⟨(-138472771/773927823),(129224168/773927823),0,0⟩ : CertField) = scaled n420 773927823 := by decide +kernel
private def n421 : IntField := ⟨(-576131),424264,0,0⟩
private theorem pos421 : (0:ℤ) < 539327 := by decide +kernel
private theorem cp421 : (⟨(-576131/539327),(424264/539327),0,0⟩ : CertField) = scaled n421 539327 := by decide +kernel
private def n422 : IntField := ⟨2569,0,0,(-176)⟩
private theorem pos422 : (0:ℤ) < 2345 := by decide +kernel
private theorem cp422 : (⟨(367/335),0,0,(-176/2345)⟩ : CertField) = scaled n422 2345 := by decide +kernel
private def n423 : IntField := ⟨443751,0,0,4831⟩
private theorem pos423 : (0:ℤ) < 349762 := by decide +kernel
private theorem cp423 : (⟨(63393/49966),0,0,(4831/349762)⟩ : CertField) = scaled n423 349762 := by decide +kernel
private def n424 : IntField := ⟨(-5445979),3737807,0,0⟩
private theorem pos424 : (0:ℤ) < 3423554 := by decide +kernel
private theorem cp424 : (⟨(-5445979/3423554),(3737807/3423554),0,0⟩ : CertField) = scaled n424 3423554 := by decide +kernel
private def n425 : IntField := ⟨3573,0,0,(-1)⟩
private theorem pos425 : (0:ℤ) < 13326 := by decide +kernel
private theorem cp425 : (⟨(1191/4442),0,0,(-1/13326)⟩ : CertField) = scaled n425 13326 := by decide +kernel
private def n426 : IntField := ⟨3753,(-1),0,0⟩
private theorem pos426 : (0:ℤ) < 14001 := by decide +kernel
private theorem cp426 : (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) = scaled n426 14001 := by decide +kernel
private def n427 : IntField := ⟨443751,0,0,4831⟩
private theorem pos427 : (0:ℤ) < 178450 := by decide +kernel
private theorem cp427 : (⟨(443751/178450),0,0,(4831/178450)⟩ : CertField) = scaled n427 178450 := by decide +kernel
private def n428 : IntField := ⟨8379,0,0,83⟩
private theorem pos428 : (0:ℤ) < 4690 := by decide +kernel
private theorem cp428 : (⟨(1197/670),0,0,(83/4690)⟩ : CertField) = scaled n428 4690 := by decide +kernel
private def n429 : IntField := ⟨(-17325864),14330533,0,0⟩
private theorem pos429 : (0:ℤ) < 22600513 := by decide +kernel
private theorem cp429 : (⟨(-17325864/22600513),(14330533/22600513),0,0⟩ : CertField) = scaled n429 22600513 := by decide +kernel
private def n430 : IntField := ⟨345,0,0,(-1)⟩
private theorem pos430 : (0:ℤ) < 1266 := by decide +kernel
private theorem cp430 : (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = scaled n430 1266 := by decide +kernel
private def n431 : IntField := ⟨30258120,(-14268851),0,0⟩
private theorem pos431 : (0:ℤ) < 16953627 := by decide +kernel
private theorem cp431 : (⟨(10086040/5651209),(-14268851/16953627),0,0⟩ : CertField) = scaled n431 16953627 := by decide +kernel
private def n432 : IntField := ⟨14271245,(-6156758),0,0⟩
private theorem pos432 : (0:ℤ) < 10786540 := by decide +kernel
private theorem cp432 : (⟨(2854249/2157308),(-3078379/5393270),0,0⟩ : CertField) = scaled n432 10786540 := by decide +kernel
private def n433 : IntField := ⟨338188789,(-144869352),0,0⟩
private theorem pos433 : (0:ℤ) < 236814071 := by decide +kernel
private theorem cp433 : (⟨(338188789/236814071),(-144869352/236814071),0,0⟩ : CertField) = scaled n433 236814071 := by decide +kernel
private def n434 : IntField := ⟨3078201,0,0,275471⟩
private theorem pos434 : (0:ℤ) < 6576450 := by decide +kernel
private theorem cp434 : (⟨(1026067/2192150),0,0,(275471/6576450)⟩ : CertField) = scaled n434 6576450 := by decide +kernel
private def n435 : IntField := ⟨1635,0,0,(-299)⟩
private theorem pos435 : (0:ℤ) < 510 := by decide +kernel
private theorem cp435 : (⟨(109/34),0,0,(-299/510)⟩ : CertField) = scaled n435 510 := by decide +kernel
private def n436 : IntField := ⟨(-9733651),10108657,0,0⟩
private theorem pos436 : (0:ℤ) < 22729957 := by decide +kernel
private theorem cp436 : (⟨(-9733651/22729957),(10108657/22729957),0,0⟩ : CertField) = scaled n436 22729957 := by decide +kernel
private def n437 : IntField := ⟨(-49334341),43021876,0,0⟩
private theorem pos437 : (0:ℤ) < 72142907 := by decide +kernel
private theorem cp437 : (⟨(-49334341/72142907),(43021876/72142907),0,0⟩ : CertField) = scaled n437 72142907 := by decide +kernel
private def n438 : IntField := ⟨(-120589494),278276430,0,0⟩
private theorem pos438 : (0:ℤ) < 952499483 := by decide +kernel
private theorem cp438 : (⟨(-120589494/952499483),(278276430/952499483),0,0⟩ : CertField) = scaled n438 952499483 := by decide +kernel
private def n439 : IntField := ⟨71202757,32270063,0,0⟩
private theorem pos439 : (0:ℤ) < 53963533 := by decide +kernel
private theorem cp439 : (⟨(71202757/53963533),(32270063/53963533),0,0⟩ : CertField) = scaled n439 53963533 := by decide +kernel
private def n440 : IntField := ⟨589435,0,0,(-43875)⟩
private theorem pos440 : (0:ℤ) < 1807526 := by decide +kernel
private theorem cp440 : (⟨(84205/258218),0,0,(-43875/1807526)⟩ : CertField) = scaled n440 1807526 := by decide +kernel
private def n441 : IntField := ⟨7081,0,0,1⟩
private theorem pos441 : (0:ℤ) < 19270 := by decide +kernel
private theorem cp441 : (⟨(7081/19270),0,0,(1/19270)⟩ : CertField) = scaled n441 19270 := by decide +kernel
private def n442 : IntField := ⟨483,1,0,0⟩
private theorem pos442 : (0:ℤ) < 1318 := by decide +kernel
private theorem cp442 : (⟨(483/1318),(1/1318),0,0⟩ : CertField) = scaled n442 1318 := by decide +kernel
private def n443 : IntField := ⟨831164429,287756229,0,0⟩
private theorem pos443 : (0:ℤ) < 651713437 := by decide +kernel
private theorem cp443 : (⟨(831164429/651713437),(287756229/651713437),0,0⟩ : CertField) = scaled n443 651713437 := by decide +kernel
private def n444 : IntField := ⟨20875,0,0,621⟩
private theorem pos444 : (0:ℤ) < 84286 := by decide +kernel
private theorem cp444 : (⟨(20875/84286),0,0,(621/84286)⟩ : CertField) = scaled n444 84286 := by decide +kernel
private def n445 : IntField := ⟨457,0,0,1⟩
private theorem pos445 : (0:ℤ) < 1258 := by decide +kernel
private theorem cp445 : (⟨(457/1258),0,0,(1/1258)⟩ : CertField) = scaled n445 1258 := by decide +kernel
private def n446 : IntField := ⟨14049,0,0,109⟩
private theorem pos446 : (0:ℤ) < 29526 := by decide +kernel
private theorem cp446 : (⟨(669/1406),0,0,(109/29526)⟩ : CertField) = scaled n446 29526 := by decide +kernel
private def n447 : IntField := ⟨2246128119,925182554,0,0⟩
private theorem pos447 : (0:ℤ) < 1666646111 := by decide +kernel
private theorem cp447 : (⟨(2246128119/1666646111),(925182554/1666646111),0,0⟩ : CertField) = scaled n447 1666646111 := by decide +kernel
private def n448 : IntField := ⟨825209,0,0,(-61425)⟩
private theorem pos448 : (0:ℤ) < 1291090 := by decide +kernel
private theorem cp448 : (⟨(825209/1291090),0,0,(-12285/258218)⟩ : CertField) = scaled n448 1291090 := by decide +kernel
private def n449 : IntField := ⟨7480,1,0,0⟩
private theorem pos449 : (0:ℤ) < 20353 := by decide +kernel
private theorem cp449 : (⟨(7480/20353),(1/20353),0,0⟩ : CertField) = scaled n449 20353 := by decide +kernel
private def n450 : IntField := ⟨643800,1183231,0,0⟩
private theorem pos450 : (0:ℤ) < 4600479 := by decide +kernel
private theorem cp450 : (⟨(214600/1533493),(1183231/4600479),0,0⟩ : CertField) = scaled n450 4600479 := by decide +kernel
private def n451 : IntField := ⟨(-1188771),16952696,0,0⟩
private theorem pos451 : (0:ℤ) < 55559631 := by decide +kernel
private theorem cp451 : (⟨(-396257/18519877),(16952696/55559631),0,0⟩ : CertField) = scaled n451 55559631 := by decide +kernel
private def n452 : IntField := ⟨23895000,30450956,0,0⟩
private theorem pos452 : (0:ℤ) < 142084293 := by decide +kernel
private theorem cp452 : (⟨(7965000/47361431),(30450956/142084293),0,0⟩ : CertField) = scaled n452 142084293 := by decide +kernel
private def n453 : IntField := ⟨14049,0,0,109⟩
private theorem pos453 : (0:ℤ) < 7770 := by decide +kernel
private theorem cp453 : (⟨(669/370),0,0,(109/7770)⟩ : CertField) = scaled n453 7770 := by decide +kernel
private def n454 : IntField := ⟨1523676,1105007,0,0⟩
private theorem pos454 : (0:ℤ) < 1064531 := by decide +kernel
private theorem cp454 : (⟨(1523676/1064531),(1105007/1064531),0,0⟩ : CertField) = scaled n454 1064531 := by decide +kernel
private def n455 : IntField := ⟨178613577,166787020,0,0⟩
private theorem pos455 : (0:ℤ) < 167131367 := by decide +kernel
private theorem cp455 : (⟨(178613577/167131367),(166787020/167131367),0,0⟩ : CertField) = scaled n455 167131367 := by decide +kernel
private def n456 : IntField := ⟨218317480,92246870,0,0⟩
private theorem pos456 : (0:ℤ) < 128644477 := by decide +kernel
private theorem cp456 : (⟨(218317480/128644477),(92246870/128644477),0,0⟩ : CertField) = scaled n456 128644477 := by decide +kernel
private def n457 : IntField := ⟨22851,63275,0,0⟩
private theorem pos457 : (0:ℤ) < 90753 := by decide +kernel
private theorem cp457 : (⟨(7617/30251),(63275/90753),0,0⟩ : CertField) = scaled n457 90753 := by decide +kernel
private def n458 : IntField := ⟨(-291543),10761892,0,0⟩
private theorem pos458 : (0:ℤ) < 14248221 := by decide +kernel
private theorem cp458 : (⟨(-97181/4749407),(10761892/14248221),0,0⟩ : CertField) = scaled n458 14248221 := by decide +kernel
private def n459 : IntField := ⟨30400,57452,0,0⟩
private theorem pos459 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp459 : (⟨(30400/97513),(57452/97513),0,0⟩ : CertField) = scaled n459 97513 := by decide +kernel
private def n460 : IntField := ⟨124803,0,0,(-373)⟩
private theorem pos460 : (0:ℤ) < 91686 := by decide +kernel
private theorem cp460 : (⟨(5943/4366),0,0,(-373/91686)⟩ : CertField) = scaled n460 91686 := by decide +kernel
private def n461 : IntField := ⟨873621,0,0,(-2611)⟩
private theorem pos461 : (0:ℤ) < 327450 := by decide +kernel
private theorem cp461 : (⟨(291207/109150),0,0,(-2611/327450)⟩ : CertField) = scaled n461 327450 := by decide +kernel
private def n462 : IntField := ⟨74197,152797,0,0⟩
private theorem pos462 : (0:ℤ) < 700271 := by decide +kernel
private theorem cp462 : (⟨(74197/700271),(152797/700271),0,0⟩ : CertField) = scaled n462 700271 := by decide +kernel
private def n463 : IntField := ⟨1361824,1917252,0,0⟩
private theorem pos463 : (0:ℤ) < 10527803 := by decide +kernel
private theorem cp463 : (⟨(1361824/10527803),(1917252/10527803),0,0⟩ : CertField) = scaled n463 10527803 := by decide +kernel
private def n464 : IntField := ⟨4995615,15493577,0,0⟩
private theorem pos464 : (0:ℤ) < 51991484 := by decide +kernel
private theorem cp464 : (⟨(4995615/51991484),(15493577/51991484),0,0⟩ : CertField) = scaled n464 51991484 := by decide +kernel
private def n465 : IntField := ⟨5,0,0,0⟩
private theorem pos465 : (0:ℤ) < 7 := by decide +kernel
private theorem cp465 : (⟨(5/7),0,0,0⟩ : CertField) = scaled n465 7 := by decide +kernel
private def n466 : IntField := ⟨30007,160632,0,0⟩
private theorem pos466 : (0:ℤ) < 547307 := by decide +kernel
private theorem cp466 : (⟨(30007/547307),(160632/547307),0,0⟩ : CertField) = scaled n466 547307 := by decide +kernel
private def n467 : IntField := ⟨13014575,0,0,(-858600)⟩
private theorem pos467 : (0:ℤ) < 72486589 := by decide +kernel
private theorem cp467 : (⟨(1859225/10355227),0,0,(-858600/72486589)⟩ : CertField) = scaled n467 72486589 := by decide +kernel
private def n468 : IntField := ⟨11835,0,0,1⟩
private theorem pos468 : (0:ℤ) < 32926 := by decide +kernel
private theorem cp468 : (⟨(11835/32926),0,0,(1/32926)⟩ : CertField) = scaled n468 32926 := by decide +kernel
private def n469 : IntField := ⟨457,0,0,(-1)⟩
private theorem pos469 : (0:ℤ) < 1258 := by decide +kernel
private theorem cp469 : (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = scaled n469 1258 := by decide +kernel
private def n470 : IntField := ⟨3389547,0,0,533170⟩
private theorem pos470 : (0:ℤ) < 10028555 := by decide +kernel
private theorem cp470 : (⟨(3389547/10028555),0,0,(106634/2005711)⟩ : CertField) = scaled n470 10028555 := by decide +kernel
private def n471 : IntField := ⟨665,0,0,1⟩
private theorem pos471 : (0:ℤ) < 1858 := by decide +kernel
private theorem cp471 : (⟨(665/1858),0,0,(1/1858)⟩ : CertField) = scaled n471 1858 := by decide +kernel
private def n472 : IntField := ⟨10899,0,0,(-1)⟩
private theorem pos472 : (0:ℤ) < 30226 := by decide +kernel
private theorem cp472 : (⟨(1557/4318),0,0,(-1/30226)⟩ : CertField) = scaled n472 30226 := by decide +kernel
private def n473 : IntField := ⟨159387,0,0,16720⟩
private theorem pos473 : (0:ℤ) < 523027 := by decide +kernel
private theorem cp473 : (⟨(159387/523027),0,0,(16720/523027)⟩ : CertField) = scaled n473 523027 := by decide +kernel
private def n474 : IntField := ⟨411,0,0,(-1)⟩
private theorem pos474 : (0:ℤ) < 1126 := by decide +kernel
private theorem cp474 : (⟨(411/1126),0,0,(-1/1126)⟩ : CertField) = scaled n474 1126 := by decide +kernel
private def n475 : IntField := ⟨91003,0,0,3078⟩
private theorem pos475 : (0:ℤ) < 637177 := by decide +kernel
private theorem cp475 : (⟨(91003/637177),0,0,(3078/637177)⟩ : CertField) = scaled n475 637177 := by decide +kernel
private def n476 : IntField := ⟨723,0,0,1⟩
private theorem pos476 : (0:ℤ) < 2026 := by decide +kernel
private theorem cp476 : (⟨(723/2026),0,0,(1/2026)⟩ : CertField) = scaled n476 2026 := by decide +kernel
private def n477 : IntField := ⟨164831,0,0,5481⟩
private theorem pos477 : (0:ℤ) < 1046054 := by decide +kernel
private theorem cp477 : (⟨(164831/1046054),0,0,(5481/1046054)⟩ : CertField) = scaled n477 1046054 := by decide +kernel
private def n478 : IntField := ⟨(-1325497),3996240,0,0⟩
private theorem pos478 : (0:ℤ) < 22549813 := by decide +kernel
private theorem cp478 : (⟨(-1325497/22549813),(3996240/22549813),0,0⟩ : CertField) = scaled n478 22549813 := by decide +kernel
private def n479 : IntField := ⟨797,1,0,0⟩
private theorem pos479 : (0:ℤ) < 2221 := by decide +kernel
private theorem cp479 : (⟨(797/2221),(1/2221),0,0⟩ : CertField) = scaled n479 2221 := by decide +kernel
private def n480 : IntField := ⟨667,(-1),0,0⟩
private theorem pos480 : (0:ℤ) < 1846 := by decide +kernel
private theorem cp480 : (⟨(667/1846),(-1/1846),0,0⟩ : CertField) = scaled n480 1846 := by decide +kernel
private def n481 : IntField := ⟨(-11689311),23486732,0,0⟩
private theorem pos481 : (0:ℤ) < 106599116 := by decide +kernel
private theorem cp481 : (⟨(-11689311/106599116),(5871683/26649779),0,0⟩ : CertField) = scaled n481 106599116 := by decide +kernel
private def n482 : IntField := ⟨24985871,114593233,0,0⟩
private theorem pos482 : (0:ℤ) < 784259531 := by decide +kernel
private theorem cp482 : (⟨(24985871/784259531),(114593233/784259531),0,0⟩ : CertField) = scaled n482 784259531 := by decide +kernel
private def n483 : IntField := ⟨11574,(-1),0,0⟩
private theorem pos483 : (0:ℤ) < 32101 := by decide +kernel
private theorem cp483 : (⟨(11574/32101),(-1/32101),0,0⟩ : CertField) = scaled n483 32101 := by decide +kernel
private def n484 : IntField := ⟨3644081,0,0,(-240408)⟩
private theorem pos484 : (0:ℤ) < 10355227 := by decide +kernel
private theorem cp484 : (⟨(3644081/10355227),0,0,(-240408/10355227)⟩ : CertField) = scaled n484 10355227 := by decide +kernel
private def n485 : IntField := ⟨5981,0,0,(-1183)⟩
private theorem pos485 : (0:ℤ) < 1258 := by decide +kernel
private theorem cp485 : (⟨(5981/1258),0,0,(-1183/1258)⟩ : CertField) = scaled n485 1258 := by decide +kernel
private def n486 : IntField := ⟨8564475,21645893,0,0⟩
private theorem pos486 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp486 : (⟨(8564475/10727197),(21645893/10727197),0,0⟩ : CertField) = scaled n486 10727197 := by decide +kernel
private def n487 : IntField := ⟨660,1,0,0⟩
private theorem pos487 : (0:ℤ) < 2461 := by decide +kernel
private theorem cp487 : (⟨(660/2461),(1/2461),0,0⟩ : CertField) = scaled n487 2461 := by decide +kernel
private def n488 : IntField := ⟨525,(-1),0,0⟩
private theorem pos488 : (0:ℤ) < 1941 := by decide +kernel
private theorem cp488 : (⟨(175/647),(-1/1941),0,0⟩ : CertField) = scaled n488 1941 := by decide +kernel
private def n489 : IntField := ⟨19599,0,0,(-3569)⟩
private theorem pos489 : (0:ℤ) < 510 := by decide +kernel
private theorem cp489 : (⟨(6533/170),0,0,(-3569/510)⟩ : CertField) = scaled n489 510 := by decide +kernel
private def n490 : IntField := ⟨561,0,0,1⟩
private theorem pos490 : (0:ℤ) < 2098 := by decide +kernel
private theorem cp490 : (⟨(561/2098),0,0,(1/2098)⟩ : CertField) = scaled n490 2098 := by decide +kernel
private def n491 : IntField := ⟨299,0,0,(-1)⟩
private theorem pos491 : (0:ℤ) < 1090 := by decide +kernel
private theorem cp491 : (⟨(299/1090),0,0,(-1/1090)⟩ : CertField) = scaled n491 1090 := by decide +kernel
private def n492 : IntField := ⟨2012539,0,0,184759⟩
private theorem pos492 : (0:ℤ) < 613802 := by decide +kernel
private theorem cp492 : (⟨(2012539/613802),0,0,(184759/613802)⟩ : CertField) = scaled n492 613802 := by decide +kernel
private def n493 : IntField := ⟨9683,0,0,1⟩
private theorem pos493 : (0:ℤ) < 36034 := by decide +kernel
private theorem cp493 : (⟨(9683/36034),0,0,(1/36034)⟩ : CertField) = scaled n493 36034 := by decide +kernel
private def n494 : IntField := ⟨14087773,0,0,1293313⟩
private theorem pos494 : (0:ℤ) < 2192150 := by decide +kernel
private theorem cp494 : (⟨(14087773/2192150),0,0,(1293313/2192150)⟩ : CertField) = scaled n494 2192150 := by decide +kernel
private def n495 : IntField := ⟨7469,0,0,(-1363)⟩
private theorem pos495 : (0:ℤ) < 170 := by decide +kernel
private theorem cp495 : (⟨(7469/170),0,0,(-1363/170)⟩ : CertField) = scaled n495 170 := by decide +kernel
private def n496 : IntField := ⟨623,0,0,1⟩
private theorem pos496 : (0:ℤ) < 2338 := by decide +kernel
private theorem cp496 : (⟨(89/334),0,0,(1/2338)⟩ : CertField) = scaled n496 2338 := by decide +kernel
private def n497 : IntField := ⟨3979975,0,0,22280⟩
private theorem pos497 : (0:ℤ) < 72486589 := by decide +kernel
private theorem cp497 : (⟨(3979975/72486589),0,0,(22280/72486589)⟩ : CertField) = scaled n497 72486589 := by decide +kernel
private def n498 : IntField := ⟨49859,0,0,118⟩
private theorem pos498 : (0:ℤ) < 637177 := by decide +kernel
private theorem cp498 : (⟨(49859/637177),0,0,(118/637177)⟩ : CertField) = scaled n498 637177 := by decide +kernel
private def n499 : IntField := ⟨90343,0,0,161⟩
private theorem pos499 : (0:ℤ) < 1046054 := by decide +kernel
private theorem cp499 : (⟨(90343/1046054),0,0,(161/1046054)⟩ : CertField) = scaled n499 1046054 := by decide +kernel
private def n500 : IntField := ⟨(-967545),2108488,0,0⟩
private theorem pos500 : (0:ℤ) < 22549813 := by decide +kernel
private theorem cp500 : (⟨(-967545/22549813),(2108488/22549813),0,0⟩ : CertField) = scaled n500 22549813 := by decide +kernel
private def n501 : IntField := ⟨(-8792967),13057964,0,0⟩
private theorem pos501 : (0:ℤ) < 106599116 := by decide +kernel
private theorem cp501 : (⟨(-8792967/106599116),(3264491/26649779),0,0⟩ : CertField) = scaled n501 106599116 := by decide +kernel
private def n502 : IntField := ⟨5007399,58998601,0,0⟩
private theorem pos502 : (0:ℤ) < 784259531 := by decide +kernel
private theorem cp502 : (⟨(5007399/784259531),(58998601/784259531),0,0⟩ : CertField) = scaled n502 784259531 := by decide +kernel
private def n503 : IntField := ⟨5571965,0,0,31192⟩
private theorem pos503 : (0:ℤ) < 51776135 := by decide +kernel
private theorem cp503 : (⟨(1114393/10355227),0,0,(31192/51776135)⟩ : CertField) = scaled n503 51776135 := by decide +kernel
private def n504 : IntField := ⟨4177235,10328301,0,0⟩
private theorem pos504 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp504 : (⟨(4177235/10727197),(10328301/10727197),0,0⟩ : CertField) = scaled n504 10727197 := by decide +kernel
private def n505 : IntField := ⟨2717,0,0,(-483)⟩
private theorem pos505 : (0:ℤ) < 170 := by decide +kernel
private theorem cp505 : (⟨(2717/170),0,0,(-483/170)⟩ : CertField) = scaled n505 170 := by decide +kernel
private def n506 : IntField := ⟨935011,0,0,100031⟩
private theorem pos506 : (0:ℤ) < 613802 := by decide +kernel
private theorem cp506 : (⟨(133573/87686),0,0,(100031/613802)⟩ : CertField) = scaled n506 613802 := by decide +kernel
private def n507 : IntField := ⟨6545077,0,0,700217⟩
private theorem pos507 : (0:ℤ) < 2192150 := by decide +kernel
private theorem cp507 : (⟨(6545077/2192150),0,0,(700217/2192150)⟩ : CertField) = scaled n507 2192150 := by decide +kernel
private def n508 : IntField := ⟨3365,0,0,(-603)⟩
private theorem pos508 : (0:ℤ) < 170 := by decide +kernel
private theorem cp508 : (⟨(673/34),0,0,(-603/170)⟩ : CertField) = scaled n508 170 := by decide +kernel
private def n509 : IntField := ⟨177731,0,0,(-683)⟩
private theorem pos509 : (0:ℤ) < 1807526 := by decide +kernel
private theorem cp509 : (⟨(177731/1807526),0,0,(-683/1807526)⟩ : CertField) = scaled n509 1807526 := by decide +kernel
private def n510 : IntField := ⟨17885273,0,0,1618785⟩
private theorem pos510 : (0:ℤ) < 48468670 := by decide +kernel
private theorem cp510 : (⟨(17885273/48468670),0,0,(323757/9693734)⟩ : CertField) = scaled n510 48468670 := by decide +kernel
private def n511 : IntField := ⟨411,0,0,1⟩
private theorem pos511 : (0:ℤ) < 1126 := by decide +kernel
private theorem cp511 : (⟨(411/1126),0,0,(1/1126)⟩ : CertField) = scaled n511 1126 := by decide +kernel
private def n512 : IntField := ⟨6361,0,0,(-1)⟩
private theorem pos512 : (0:ℤ) < 17218 := by decide +kernel
private theorem cp512 : (⟨(6361/17218),0,0,(-1/17218)⟩ : CertField) = scaled n512 17218 := by decide +kernel
private def n513 : IntField := ⟨57343,0,0,(-103)⟩
private theorem pos513 : (0:ℤ) < 421430 := by decide +kernel
private theorem cp513 : (⟨(57343/421430),0,0,(-103/421430)⟩ : CertField) = scaled n513 421430 := by decide +kernel
private def n514 : IntField := ⟨25109,0,0,(-80)⟩
private theorem pos514 : (0:ℤ) < 161581 := by decide +kernel
private theorem cp514 : (⟨(3587/23083),0,0,(-80/161581)⟩ : CertField) = scaled n514 161581 := by decide +kernel
private def n515 : IntField := ⟨217,0,0,(-1)⟩
private theorem pos515 : (0:ℤ) < 574 := by decide +kernel
private theorem cp515 : (⟨(31/82),0,0,(-1/574)⟩ : CertField) = scaled n515 574 := by decide +kernel
private def n516 : IntField := ⟨(-562140),1215739,0,0⟩
private theorem pos516 : (0:ℤ) < 7488217 := by decide +kernel
private theorem cp516 : (⟨(-562140/7488217),(1215739/7488217),0,0⟩ : CertField) = scaled n516 7488217 := by decide +kernel
private def n517 : IntField := ⟨383,(-1),0,0⟩
private theorem pos517 : (0:ℤ) < 1033 := by decide +kernel
private theorem cp517 : (⟨(383/1033),(-1/1033),0,0⟩ : CertField) = scaled n517 1033 := by decide +kernel
private def n518 : IntField := ⟨(-5095416),7531157,0,0⟩
private theorem pos518 : (0:ℤ) < 35398844 := by decide +kernel
private theorem cp518 : (⟨(-1273854/8849711),(7531157/35398844),0,0⟩ : CertField) = scaled n518 35398844 := by decide +kernel
private def n519 : IntField := ⟨1707987,17165996,0,0⟩
private theorem pos519 : (0:ℤ) < 132663949 := by decide +kernel
private theorem cp519 : (⟨(1707987/132663949),(17165996/132663949),0,0⟩ : CertField) = scaled n519 132663949 := by decide +kernel
private def n520 : IntField := ⟨6760,(-1),0,0⟩
private theorem pos520 : (0:ℤ) < 18301 := by decide +kernel
private theorem cp520 : (⟨(6760/18301),(-1/18301),0,0⟩ : CertField) = scaled n520 18301 := by decide +kernel
private def n521 : IntField := ⟨1244117,0,0,(-4781)⟩
private theorem pos521 : (0:ℤ) < 6455450 := by decide +kernel
private theorem cp521 : (⟨(1244117/6455450),0,0,(-4781/6455450)⟩ : CertField) = scaled n521 6455450 := by decide +kernel
private def n522 : IntField := ⟨59979,170200,0,0⟩
private theorem pos522 : (0:ℤ) < 90753 := by decide +kernel
private theorem cp522 : (⟨(19993/30251),(170200/90753),0,0⟩ : CertField) = scaled n522 90753 := by decide +kernel
private def n523 : IntField := ⟨(-2681441),10850397,0,0⟩
private theorem pos523 : (0:ℤ) < 4749407 := by decide +kernel
private theorem cp523 : (⟨(-2681441/4749407),(10850397/4749407),0,0⟩ : CertField) = scaled n523 4749407 := by decide +kernel
private def n524 : IntField := ⟨80450,154458,0,0⟩
private theorem pos524 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp524 : (⟨(80450/97513),(154458/97513),0,0⟩ : CertField) = scaled n524 97513 := by decide +kernel
private def n525 : IntField := ⟨6881,0,0,(-54)⟩
private theorem pos525 : (0:ℤ) < 1295 := by decide +kernel
private theorem cp525 : (⟨(983/185),0,0,(-54/1295)⟩ : CertField) = scaled n525 1295 := by decide +kernel
private def n526 : IntField := ⟨221921,0,0,19414⟩
private theorem pos526 : (0:ℤ) < 76405 := by decide +kernel
private theorem cp526 : (⟨(31703/10915),0,0,(19414/76405)⟩ : CertField) = scaled n526 76405 := by decide +kernel
private def n527 : IntField := ⟨1553447,0,0,135898⟩
private theorem pos527 : (0:ℤ) < 272875 := by decide +kernel
private theorem cp527 : (⟨(1553447/272875),0,0,(135898/272875)⟩ : CertField) = scaled n527 272875 := by decide +kernel
private def n528 : IntField := ⟨8393,0,0,(-102)⟩
private theorem pos528 : (0:ℤ) < 1295 := by decide +kernel
private theorem cp528 : (⟨(1199/185),0,0,(-102/1295)⟩ : CertField) = scaled n528 1295 := by decide +kernel
private def n529 : IntField := ⟨5562375,0,0,(-19750)⟩
private theorem pos529 : (0:ℤ) < 98279839 := by decide +kernel
private theorem cp529 : (⟨(794625/14039977),0,0,(-19750/98279839)⟩ : CertField) = scaled n529 98279839 := by decide +kernel
private def n530 : IntField := ⟨40107,0,0,112⟩
private theorem pos530 : (0:ℤ) < 523027 := by decide +kernel
private theorem cp530 : (⟨(40107/523027),0,0,(112/523027)⟩ : CertField) = scaled n530 523027 := by decide +kernel
private def n531 : IntField := ⟨(-51396),135985,0,0⟩
private theorem pos531 : (0:ℤ) < 1734601 := by decide +kernel
private theorem cp531 : (⟨(-51396/1734601),(135985/1734601),0,0⟩ : CertField) = scaled n531 1734601 := by decide +kernel
private def n532 : IntField := ⟨222495,0,0,(-790)⟩
private theorem pos532 : (0:ℤ) < 2005711 := by decide +kernel
private theorem cp532 : (⟨(222495/2005711),0,0,(-790/2005711)⟩ : CertField) = scaled n532 2005711 := by decide +kernel
private def n533 : IntField := ⟨(-2962082),5282779,0,0⟩
private theorem pos533 : (0:ℤ) < 53299558 := by decide +kernel
private theorem cp533 : (⟨(-1481041/26649779),(5282779/53299558),0,0⟩ : CertField) = scaled n533 53299558 := by decide +kernel
private def n534 : IntField := ⟨121599,1826912,0,0⟩
private theorem pos534 : (0:ℤ) < 27179581 := by decide +kernel
private theorem cp534 : (⟨(121599/27179581),(1826912/27179581),0,0⟩ : CertField) = scaled n534 27179581 := by decide +kernel
private def n535 : IntField := ⟨12510,1,0,0⟩
private theorem pos535 : (0:ℤ) < 34801 := by decide +kernel
private theorem cp535 : (⟨(12510/34801),(1/34801),0,0⟩ : CertField) = scaled n535 34801 := by decide +kernel
private def n536 : IntField := ⟨3680200,9241922,0,0⟩
private theorem pos536 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp536 : (⟨(3680200/10727197),(9241922/10727197),0,0⟩ : CertField) = scaled n536 10727197 := by decide +kernel
private def n537 : IntField := ⟨1458747,0,0,50102⟩
private theorem pos537 : (0:ℤ) < 920703 := by decide +kernel
private theorem cp537 : (⟨(486249/306901),0,0,(50102/920703)⟩ : CertField) = scaled n537 920703 := by decide +kernel
private def n538 : IntField := ⟨10211229,0,0,350714⟩
private theorem pos538 : (0:ℤ) < 3288225 := by decide +kernel
private theorem cp538 : (⟨(3403743/1096075),0,0,(350714/3288225)⟩ : CertField) = scaled n538 3288225 := by decide +kernel
private def n539 : IntField := ⟨4023,0,0,(-728)⟩
private theorem pos539 : (0:ℤ) < 255 := by decide +kernel
private theorem cp539 : (⟨(1341/85),0,0,(-728/255)⟩ : CertField) = scaled n539 255 := by decide +kernel
private def n540 : IntField := ⟨3592515,0,0,(-132425)⟩
private theorem pos540 : (0:ℤ) < 28079954 := by decide +kernel
private theorem cp540 : (⟨(3592515/28079954),0,0,(-132425/28079954)⟩ : CertField) = scaled n540 28079954 := by decide +kernel
private def n541 : IntField := ⟨98331,0,0,10955⟩
private theorem pos541 : (0:ℤ) < 1046054 := by decide +kernel
private theorem cp541 : (⟨(98331/1046054),0,0,(10955/1046054)⟩ : CertField) = scaled n541 1046054 := by decide +kernel
private def n542 : IntField := ⟨(-7420123),17398874,0,0⟩
private theorem pos542 : (0:ℤ) < 106599116 := by decide +kernel
private theorem cp542 : (⟨(-7420123/106599116),(8699437/53299558),0,0⟩ : CertField) = scaled n542 106599116 := by decide +kernel
private def n543 : IntField := ⟨5029521,0,0,(-185395)⟩
private theorem pos543 : (0:ℤ) < 20057110 := by decide +kernel
private theorem cp543 : (⟨(5029521/20057110),0,0,(-37079/4011422)⟩ : CertField) = scaled n543 20057110 := by decide +kernel
private def n544 : IntField := ⟨6671500,16958462,0,0⟩
private theorem pos544 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp544 : (⟨(6671500/10727197),(16958462/10727197),0,0⟩ : CertField) = scaled n544 10727197 := by decide +kernel
private def n545 : IntField := ⟨5262903,0,0,216193⟩
private theorem pos545 : (0:ℤ) < 1841406 := by decide +kernel
private theorem cp545 : (⟨(1754301/613802),0,0,(216193/1841406)⟩ : CertField) = scaled n545 1841406 := by decide +kernel
private def n546 : IntField := ⟨7739,0,0,1⟩
private theorem pos546 : (0:ℤ) < 25486 := by decide +kernel
private theorem cp546 : (⟨(7739/25486),0,0,(1/25486)⟩ : CertField) = scaled n546 25486 := by decide +kernel
private def n547 : IntField := ⟨36840321,0,0,1513351⟩
private theorem pos547 : (0:ℤ) < 6576450 := by decide +kernel
private theorem cp547 : (⟨(12280107/2192150),0,0,(1513351/6576450)⟩ : CertField) = scaled n547 6576450 := by decide +kernel
private def n548 : IntField := ⟨15903,0,0,(-2911)⟩
private theorem pos548 : (0:ℤ) < 510 := by decide +kernel
private theorem cp548 : (⟨(5301/170),0,0,(-2911/510)⟩ : CertField) = scaled n548 510 := by decide +kernel
private def n549 : IntField := ⟨6535875,0,0,14875⟩
private theorem pos549 : (0:ℤ) < 67856138 := by decide +kernel
private theorem cp549 : (⟨(6535875/67856138),0,0,(2125/9693734)⟩ : CertField) = scaled n549 67856138 := by decide +kernel
private def n550 : IntField := ⟨44583,0,0,(-97)⟩
private theorem pos550 : (0:ℤ) < 323162 := by decide +kernel
private theorem cp550 : (⟨(6369/46166),0,0,(-97/323162)⟩ : CertField) = scaled n550 323162 := by decide +kernel
private def n551 : IntField := ⟨(-388869),1019200,0,0⟩
private theorem pos551 : (0:ℤ) < 7488217 := by decide +kernel
private theorem cp551 : (⟨(-388869/7488217),(1019200/7488217),0,0⟩ : CertField) = scaled n551 7488217 := by decide +kernel
private def n552 : IntField := ⟨1830045,0,0,4165⟩
private theorem pos552 : (0:ℤ) < 9693734 := by decide +kernel
private theorem cp552 : (⟨(1830045/9693734),0,0,(4165/9693734)⟩ : CertField) = scaled n552 9693734 := by decide +kernel
private def n553 : IntField := ⟨(-1718411),3046402,0,0⟩
private theorem pos553 : (0:ℤ) < 17699422 := by decide +kernel
private theorem cp553 : (⟨(-1718411/17699422),(1523201/8849711),0,0⟩ : CertField) = scaled n553 17699422 := by decide +kernel
private def n554 : IntField := ⟨1305027,27163759,0,0⟩
private theorem pos554 : (0:ℤ) < 231271139 := by decide +kernel
private theorem cp554 : (⟨(1305027/231271139),(27163759/231271139),0,0⟩ : CertField) = scaled n554 231271139 := by decide +kernel
private def n555 : IntField := ⟨52713,152315,0,0⟩
private theorem pos555 : (0:ℤ) < 90753 := by decide +kernel
private theorem cp555 : (⟨(17571/30251),(152315/90753),0,0⟩ : CertField) = scaled n555 90753 := by decide +kernel
private def n556 : IntField := ⟨(-12201),156391,0,0⟩
private theorem pos556 : (0:ℤ) < 84309 := by decide +kernel
private theorem cp556 : (⟨(-4067/28103),(156391/84309),0,0⟩ : CertField) = scaled n556 84309 := by decide +kernel
private def n557 : IntField := ⟨71140,138176,0,0⟩
private theorem pos557 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp557 : (⟨(71140/97513),(138176/97513),0,0⟩ : CertField) = scaled n557 97513 := by decide +kernel
private def n558 : IntField := ⟨287829,0,0,2951⟩
private theorem pos558 : (0:ℤ) < 91686 := by decide +kernel
private theorem cp558 : (⟨(95943/30562),0,0,(2951/91686)⟩ : CertField) = scaled n558 91686 := by decide +kernel
private def n559 : IntField := ⟨2014803,0,0,20657⟩
private theorem pos559 : (0:ℤ) < 327450 := by decide +kernel
private theorem cp559 : (⟨(671601/109150),0,0,(20657/327450)⟩ : CertField) = scaled n559 327450 := by decide +kernel
private def n560 : IntField := ⟨7875,0,0,(-139)⟩
private theorem pos560 : (0:ℤ) < 1554 := by decide +kernel
private theorem cp560 : (⟨(375/74),0,0,(-139/1554)⟩ : CertField) = scaled n560 1554 := by decide +kernel
private def n561 : IntField := ⟨721239,0,0,48244⟩
private theorem pos561 : (0:ℤ) < 10790913 := by decide +kernel
private theorem cp561 : (⟨(240413/3596971),0,0,(6892/1541559)⟩ : CertField) = scaled n561 10790913 := by decide +kernel
private def n562 : IntField := ⟨7761,0,0,1⟩
private theorem pos562 : (0:ℤ) < 20418 := by decide +kernel
private theorem cp562 : (⟨(2587/6806),0,0,(1/20418)⟩ : CertField) = scaled n562 20418 := by decide +kernel
private def n563 : IntField := ⟨579,0,0,(-1)⟩
private theorem pos563 : (0:ℤ) < 1510 := by decide +kernel
private theorem cp563 : (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) = scaled n563 1510 := by decide +kernel
private def n564 : IntField := ⟨5505,0,0,(-112)⟩
private theorem pos564 : (0:ℤ) < 38505 := by decide +kernel
private theorem cp564 : (⟨(367/2567),0,0,(-112/38505)⟩ : CertField) = scaled n564 38505 := by decide +kernel
private def n565 : IntField := ⟨189,0,0,1⟩
private theorem pos565 : (0:ℤ) < 510 := by decide +kernel
private theorem cp565 : (⟨(63/170),0,0,(1/510)⟩ : CertField) = scaled n565 510 := by decide +kernel
private def n566 : IntField := ⟨(-698820),1477331,0,0⟩
private theorem pos566 : (0:ℤ) < 11017897 := by decide +kernel
private theorem cp566 : (⟨(-698820/11017897),(1477331/11017897),0,0⟩ : CertField) = scaled n566 11017897 := by decide +kernel
private def n567 : IntField := ⟨446,1,0,0⟩
private theorem pos567 : (0:ℤ) < 1177 := by decide +kernel
private theorem cp567 : (⟨(446/1177),(1/1177),0,0⟩ : CertField) = scaled n567 1177 := by decide +kernel
private def n568 : IntField := ⟨651,(-1),0,0⟩
private theorem pos568 : (0:ℤ) < 1702 := by decide +kernel
private theorem cp568 : (⟨(651/1702),(-1/1702),0,0⟩ : CertField) = scaled n568 1702 := by decide +kernel
private def n569 : IntField := ⟨(-6285744),9159133,0,0⟩
private theorem pos569 : (0:ℤ) < 52084604 := by decide +kernel
private theorem cp569 : (⟨(-1571436/13021151),(9159133/52084604),0,0⟩ : CertField) = scaled n569 52084604 := by decide +kernel
private def n570 : IntField := ⟨(-1011781),12763133,0,0⟩
private theorem pos570 : (0:ℤ) < 110140129 := by decide +kernel
private theorem cp570 : (⟨(-1011781/110140129),(12763133/110140129),0,0⟩ : CertField) = scaled n570 110140129 := by decide +kernel
private def n571 : IntField := ⟨9741,(-1),0,0⟩
private theorem pos571 : (0:ℤ) < 25521 := by decide +kernel
private theorem cp571 : (⟨(3247/8507),(-1/25521),0,0⟩ : CertField) = scaled n571 25521 := by decide +kernel
private def n572 : IntField := ⟨5048673,0,0,337708⟩
private theorem pos572 : (0:ℤ) < 38538975 := by decide +kernel
private theorem cp572 : (⟨(1682891/12846325),0,0,(337708/38538975)⟩ : CertField) = scaled n572 38538975 := by decide +kernel
private def n573 : IntField := ⟨1493871,3016696,0,0⟩
private theorem pos573 : (0:ℤ) < 2100813 := by decide +kernel
private theorem cp573 : (⟨(497957/700271),(3016696/2100813),0,0⟩ : CertField) = scaled n573 2100813 := by decide +kernel
private def n574 : IntField := ⟨3216375,0,0,(-294950)⟩
private theorem pos574 : (0:ℤ) < 580027 := by decide +kernel
private theorem cp574 : (⟨(3216375/580027),0,0,(-294950/580027)⟩ : CertField) = scaled n574 580027 := by decide +kernel
private def n575 : IntField := ⟨900585,0,0,(-82586)⟩
private theorem pos575 : (0:ℤ) < 82861 := by decide +kernel
private theorem cp575 : (⟨(900585/82861),0,0,(-82586/82861)⟩ : CertField) = scaled n575 82861 := by decide +kernel
private def n576 : IntField := ⟨25971,0,0,(-34)⟩
private theorem pos576 : (0:ℤ) < 6157 := by decide +kernel
private theorem cp576 : (⟨(25971/6157),0,0,(-34/6157)⟩ : CertField) = scaled n576 6157 := by decide +kernel
private def n577 : IntField := ⟨1269727,13024501,0,0⟩
private theorem pos577 : (0:ℤ) < 8457119 := by decide +kernel
private theorem cp577 : (⟨(1269727/8457119),(13024501/8457119),0,0⟩ : CertField) = scaled n577 8457119 := by decide +kernel
private def n578 : IntField := ⟨27236082,37882186,0,0⟩
private theorem pos578 : (0:ℤ) < 31583409 := by decide +kernel
private theorem cp578 : (⟨(9078694/10527803),(37882186/31583409),0,0⟩ : CertField) = scaled n578 31583409 := by decide +kernel
private def n579 : IntField := ⟨3006563,0,0,170973⟩
private theorem pos579 : (0:ℤ) < 96454246 := by decide +kernel
private theorem cp579 : (⟨(429509/13779178),0,0,(170973/96454246)⟩ : CertField) = scaled n579 96454246 := by decide +kernel
private def n580 : IntField := ⟨17703,0,0,1⟩
private theorem pos580 : (0:ℤ) < 45778 := by decide +kernel
private theorem cp580 : (⟨(17703/45778),0,0,(1/45778)⟩ : CertField) = scaled n580 45778 := by decide +kernel
private def n581 : IntField := ⟨26635,0,0,(-99)⟩
private theorem pos581 : (0:ℤ) < 454510 := by decide +kernel
private theorem cp581 : (⟨(761/12986),0,0,(-99/454510)⟩ : CertField) = scaled n581 454510 := by decide +kernel
private def n582 : IntField := ⟨(-499115),1078592,0,0⟩
private theorem pos582 : (0:ℤ) < 17679959 := by decide +kernel
private theorem cp582 : (⟨(-499115/17679959),(1078592/17679959),0,0⟩ : CertField) = scaled n582 17679959 := by decide +kernel
private def n583 : IntField := ⟨(-4522933),6681756,0,0⟩
private theorem pos583 : (0:ℤ) < 83577988 := by decide +kernel
private theorem cp583 : (⟨(-4522933/83577988),(1670439/20894497),0,0⟩ : CertField) = scaled n583 83577988 := by decide +kernel
private def n584 : IntField := ⟨(-561788),14188809,0,0⟩
private theorem pos584 : (0:ℤ) < 272669507 := by decide +kernel
private theorem cp584 : (⟨(-561788/272669507),(14188809/272669507),0,0⟩ : CertField) = scaled n584 272669507 := by decide +kernel
private def n585 : IntField := ⟨21015,(-1),0,0⟩
private theorem pos585 : (0:ℤ) < 54241 := by decide +kernel
private theorem cp585 : (⟨(21015/54241),(-1/54241),0,0⟩ : CertField) = scaled n585 54241 := by decide +kernel
private def n586 : IntField := ⟨3006563,0,0,170973⟩
private theorem pos586 : (0:ℤ) < 49211350 := by decide +kernel
private theorem cp586 : (⟨(3006563/49211350),0,0,(170973/49211350)⟩ : CertField) = scaled n586 49211350 := by decide +kernel
private def n587 : IntField := ⟨2128591,5921041,0,0⟩
private theorem pos587 : (0:ℤ) < 8433958 := by decide +kernel
private theorem cp587 : (⟨(2128591/8433958),(5921041/8433958),0,0⟩ : CertField) = scaled n587 8433958 := by decide +kernel
private def n588 : IntField := ⟨21517125,0,0,25225⟩
private theorem pos588 : (0:ℤ) < 15762614 := by decide +kernel
private theorem cp588 : (⟨(439125/321686),0,0,(25225/15762614)⟩ : CertField) = scaled n588 15762614 := by decide +kernel
private def n589 : IntField := ⟨860685,0,0,1009⟩
private theorem pos589 : (0:ℤ) < 321686 := by decide +kernel
private theorem cp589 : (⟨(860685/321686),0,0,(1009/321686)⟩ : CertField) = scaled n589 321686 := by decide +kernel
private def n590 : IntField := ⟨112707,0,0,(-253)⟩
private theorem pos590 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp590 : (⟨(16101/8282),0,0,(-253/57974)⟩ : CertField) = scaled n590 57974 := by decide +kernel
private def n591 : IntField := ⟨(-1837512),39097169,0,0⟩
private theorem pos591 : (0:ℤ) < 50928131 := by decide +kernel
private theorem cp591 : (⟨(-1837512/50928131),(39097169/50928131),0,0⟩ : CertField) = scaled n591 50928131 := by decide +kernel
private def n592 : IntField := ⟨9287043,17507389,0,0⟩
private theorem pos592 : (0:ℤ) < 29542461 := by decide +kernel
private theorem cp592 : (⟨(3095681/9847487),(17507389/29542461),0,0⟩ : CertField) = scaled n592 29542461 := by decide +kernel
private def n593 : IntField := ⟨213575,0,0,(-16800)⟩
private theorem pos593 : (0:ℤ) < 1891477 := by decide +kernel
private theorem cp593 : (⟨(213575/1891477),0,0,(-2400/270211)⟩ : CertField) = scaled n593 1891477 := by decide +kernel
private def n594 : IntField := ⟨9237,0,0,(-1)⟩
private theorem pos594 : (0:ℤ) < 24198 := by decide +kernel
private theorem cp594 : (⟨(3079/8066),0,0,(-1/24198)⟩ : CertField) = scaled n594 24198 := by decide +kernel
private def n595 : IntField := ⟨2017,0,0,(-28)⟩
private theorem pos595 : (0:ℤ) < 19765 := by decide +kernel
private theorem cp595 : (⟨(2017/19765),0,0,(-28/19765)⟩ : CertField) = scaled n595 19765 := by decide +kernel
private def n596 : IntField := ⟨681,0,0,(-1)⟩
private theorem pos596 : (0:ℤ) < 1770 := by decide +kernel
private theorem cp596 : (⟨(227/590),0,0,(-1/1770)⟩ : CertField) = scaled n596 1770 := by decide +kernel
private def n597 : IntField := ⟨3257,0,0,(-63)⟩
private theorem pos597 : (0:ℤ) < 25670 := by decide +kernel
private theorem cp597 : (⟨(3257/25670),0,0,(-63/25670)⟩ : CertField) = scaled n597 25670 := by decide +kernel
private def n598 : IntField := ⟨(-485901),1238120,0,0⟩
private theorem pos598 : (0:ℤ) < 11017897 := by decide +kernel
private theorem cp598 : (⟨(-485901/11017897),(1238120/11017897),0,0⟩ : CertField) = scaled n598 11017897 := by decide +kernel
private def n599 : IntField := ⟨59801,0,0,(-4704)⟩
private theorem pos599 : (0:ℤ) < 270211 := by decide +kernel
private theorem cp599 : (⟨(59801/270211),0,0,(-4704/270211)⟩ : CertField) = scaled n599 270211 := by decide +kernel
private def n600 : IntField := ⟨(-2126899),3703338,0,0⟩
private theorem pos600 : (0:ℤ) < 26042302 := by decide +kernel
private theorem cp600 : (⟨(-2126899/26042302),(1851669/13021151),0,0⟩ : CertField) = scaled n600 26042302 := by decide +kernel
private def n601 : IntField := ⟨1295416,6050211,0,0⟩
private theorem pos601 : (0:ℤ) < 67839167 := by decide +kernel
private theorem cp601 : (⟨(1295416/67839167),(6050211/67839167),0,0⟩ : CertField) = scaled n601 67839167 := by decide +kernel
private def n602 : IntField := ⟨8265,1,0,0⟩
private theorem pos602 : (0:ℤ) < 21741 := by decide +kernel
private theorem cp602 : (⟨(2755/7247),(1/21741),0,0⟩ : CertField) = scaled n602 21741 := by decide +kernel
private def n603 : IntField := ⟨1320117,2698847,0,0⟩
private theorem pos603 : (0:ℤ) < 2100813 := by decide +kernel
private theorem cp603 : (⟨(440039/700271),(2698847/2100813),0,0⟩ : CertField) = scaled n603 2100813 := by decide +kernel
private def n604 : IntField := ⟨4086635,0,0,(-89725)⟩
private theorem pos604 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp604 : (⟨(583805/165722),0,0,(-89725/1160054)⟩ : CertField) = scaled n604 1160054 := by decide +kernel
private def n605 : IntField := ⟨5721289,0,0,(-125615)⟩
private theorem pos605 : (0:ℤ) < 828610 := by decide +kernel
private theorem cp605 : (⟨(5721289/828610),0,0,(-25123/165722)⟩ : CertField) = scaled n605 828610 := by decide +kernel
private def n606 : IntField := ⟨57529,0,0,(-755)⟩
private theorem pos606 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp606 : (⟨(57529/12314),0,0,(-755/12314)⟩ : CertField) = scaled n606 12314 := by decide +kernel
private def n607 : IntField := ⟨(-3042309),38088568,0,0⟩
private theorem pos607 : (0:ℤ) < 25371357 := by decide +kernel
private theorem cp607 : (⟨(-1014103/8457119),(38088568/25371357),0,0⟩ : CertField) = scaled n607 25371357 := by decide +kernel
private def n608 : IntField := ⟨24169284,33874112,0,0⟩
private theorem pos608 : (0:ℤ) < 31583409 := by decide +kernel
private theorem cp608 : (⟨(8056428/10527803),(33874112/31583409),0,0⟩ : CertField) = scaled n608 31583409 := by decide +kernel
private def n609 : IntField := ⟨49471,0,0,(-551)⟩
private theorem pos609 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp609 : (⟨(49471/12314),0,0,(-551/12314)⟩ : CertField) = scaled n609 12314 := by decide +kernel
private def n610 : IntField := ⟨15169,0,0,(-1611)⟩
private theorem pos610 : (0:ℤ) < 56462 := by decide +kernel
private theorem cp610 : (⟨(2167/8066),0,0,(-1611/56462)⟩ : CertField) = scaled n610 56462 := by decide +kernel
private def n611 : IntField := ⟨71,0,0,7⟩
private theorem pos611 : (0:ℤ) < 590 := by decide +kernel
private theorem cp611 : (⟨(71/590),0,0,(7/590)⟩ : CertField) = scaled n611 590 := by decide +kernel
private def n612 : IntField := ⟨223,0,0,21⟩
private theorem pos612 : (0:ℤ) < 1510 := by decide +kernel
private theorem cp612 : (⟨(223/1510),0,0,(21/1510)⟩ : CertField) = scaled n612 1510 := by decide +kernel
private def n613 : IntField := ⟨411,0,0,41⟩
private theorem pos613 : (0:ℤ) < 1310 := by decide +kernel
private theorem cp613 : (⟨(411/1310),0,0,(41/1310)⟩ : CertField) = scaled n613 1310 := by decide +kernel
private def n614 : IntField := ⟨(-5372366),12188673,0,0⟩
private theorem pos614 : (0:ℤ) < 52084604 := by decide +kernel
private theorem cp614 : (⟨(-2686183/26042302),(12188673/52084604),0,0⟩ : CertField) = scaled n614 52084604 := by decide +kernel
private def n615 : IntField := ⟨106183,0,0,(-11277)⟩
private theorem pos615 : (0:ℤ) < 201650 := by decide +kernel
private theorem cp615 : (⟨(106183/201650),0,0,(-11277/201650)⟩ : CertField) = scaled n615 201650 := by decide +kernel
private def n616 : IntField := ⟨2398857,4951487,0,0⟩
private theorem pos616 : (0:ℤ) < 2100813 := by decide +kernel
private theorem cp616 : (⟨(799619/700271),(4951487/2100813),0,0⟩ : CertField) = scaled n616 2100813 := by decide +kernel
private def n617 : IntField := ⟨7863965,0,0,(-264385)⟩
private theorem pos617 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp617 : (⟨(7863965/1160054),0,0,(-264385/1160054)⟩ : CertField) = scaled n617 1160054 := by decide +kernel
private def n618 : IntField := ⟨11009551,0,0,(-370139)⟩
private theorem pos618 : (0:ℤ) < 828610 := by decide +kernel
private theorem cp618 : (⟨(11009551/828610),0,0,(-370139/828610)⟩ : CertField) = scaled n618 828610 := by decide +kernel
private def n619 : IntField := ⟨106351,0,0,(-1991)⟩
private theorem pos619 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp619 : (⟨(106351/12314),0,0,(-1991/12314)⟩ : CertField) = scaled n619 12314 := by decide +kernel
private def n620 : IntField := ⟨(-4304901),69110935,0,0⟩
private theorem pos620 : (0:ℤ) < 25371357 := by decide +kernel
private theorem cp620 : (⟨(-1434967/8457119),(69110935/25371357),0,0⟩ : CertField) = scaled n620 25371357 := by decide +kernel
private def n621 : IntField := ⟨44063964,62124152,0,0⟩
private theorem pos621 : (0:ℤ) < 31583409 := by decide +kernel
private theorem cp621 : (⟨(14687988/10527803),(62124152/31583409),0,0⟩ : CertField) = scaled n621 31583409 := by decide +kernel
private def n622 : IntField := ⟨95449,0,0,(-1715)⟩
private theorem pos622 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp622 : (⟨(95449/12314),0,0,(-1715/12314)⟩ : CertField) = scaled n622 12314 := by decide +kernel
private def n623 : IntField := ⟨979525,0,0,(-57475)⟩
private theorem pos623 : (0:ℤ) < 21210854 := by decide +kernel
private theorem cp623 : (⟨(979525/21210854),0,0,(-57475/21210854)⟩ : CertField) = scaled n623 21210854 := by decide +kernel
private def n624 : IntField := ⟨9029,0,0,(-11)⟩
private theorem pos624 : (0:ℤ) < 198830 := by decide +kernel
private theorem cp624 : (⟨(9029/198830),0,0,(-11/198830)⟩ : CertField) = scaled n624 198830 := by decide +kernel
private def n625 : IntField := ⟨11823,0,0,(-32)⟩
private theorem pos625 : (0:ℤ) < 227255 := by decide +kernel
private theorem cp625 : (⟨(1689/32465),0,0,(-32/227255)⟩ : CertField) = scaled n625 227255 := by decide +kernel
private def n626 : IntField := ⟨(-345332),904215,0,0⟩
private theorem pos626 : (0:ℤ) < 17679959 := by decide +kernel
private theorem cp626 : (⟨(-345332/17679959),(904215/17679959),0,0⟩ : CertField) = scaled n626 17679959 := by decide +kernel
private def n627 : IntField := ⟨274267,0,0,(-16093)⟩
private theorem pos627 : (0:ℤ) < 3030122 := by decide +kernel
private theorem cp627 : (⟨(274267/3030122),0,0,(-16093/3030122)⟩ : CertField) = scaled n627 3030122 := by decide +kernel
private def n628 : IntField := ⟨(-4576554),8108323,0,0⟩
private theorem pos628 : (0:ℤ) < 125366982 := by decide +kernel
private theorem cp628 : (⟨(-762759/20894497),(8108323/125366982),0,0⟩ : CertField) = scaled n628 125366982 := by decide +kernel
private def n629 : IntField := ⟨14504541,77921561,0,0⟩
private theorem pos629 : (0:ℤ) < 1882548107 := by decide +kernel
private theorem cp629 : (⟨(14504541/1882548107),(77921561/1882548107),0,0⟩ : CertField) = scaled n629 1882548107 := by decide +kernel
private def n630 : IntField := ⟨18819,1,0,0⟩
private theorem pos630 : (0:ℤ) < 48661 := by decide +kernel
private theorem cp630 : (⟨(18819/48661),(1/48661),0,0⟩ : CertField) = scaled n630 48661 := by decide +kernel
private def n631 : IntField := ⟨935716,2649381,0,0⟩
private theorem pos631 : (0:ℤ) < 4216979 := by decide +kernel
private theorem cp631 : (⟨(935716/4216979),(2649381/4216979),0,0⟩ : CertField) = scaled n631 4216979 := by decide +kernel
private def n632 : IntField := ⟨971349,0,0,(-147649)⟩
private theorem pos632 : (0:ℤ) < 538734 := by decide +kernel
private theorem cp632 : (⟨(323783/179578),0,0,(-147649/538734)⟩ : CertField) = scaled n632 538734 := by decide +kernel
private def n633 : IntField := ⟨2275405,0,0,168075⟩
private theorem pos633 : (0:ℤ) < 2251802 := by decide +kernel
private theorem cp633 : (⟨(2275405/2251802),0,0,(168075/2251802)⟩ : CertField) = scaled n633 2251802 := by decide +kernel
private def n634 : IntField := ⟨3185567,0,0,235305⟩
private theorem pos634 : (0:ℤ) < 1608430 := by decide +kernel
private theorem cp634 : (⟨(3185567/1608430),0,0,(47061/321686)⟩ : CertField) = scaled n634 1608430 := by decide +kernel
private def n635 : IntField := ⟨124859,0,0,(-1755)⟩
private theorem pos635 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp635 : (⟨(17837/8282),0,0,(-1755/57974)⟩ : CertField) = scaled n635 57974 := by decide +kernel
private def n636 : IntField := ⟨(-17165189),76876453,0,0⟩
private theorem pos636 : (0:ℤ) < 101856262 := by decide +kernel
private theorem cp636 : (⟨(-17165189/101856262),(76876453/101856262),0,0⟩ : CertField) = scaled n636 101856262 := by decide +kernel
private def n637 : IntField := ⟨8214216,15661538,0,0⟩
private theorem pos637 : (0:ℤ) < 29542461 := by decide +kernel
private theorem cp637 : (⟨(2738072/9847487),(15661538/29542461),0,0⟩ : CertField) = scaled n637 29542461 := by decide +kernel
private def n638 : IntField := ⟨53683,0,0,(-648)⟩
private theorem pos638 : (0:ℤ) < 28987 := by decide +kernel
private theorem cp638 : (⟨(7669/4141),0,0,(-648/28987)⟩ : CertField) = scaled n638 28987 := by decide +kernel
private def n639 : IntField := ⟨2633475,0,0,(-130150)⟩
private theorem pos639 : (0:ℤ) < 104524931 := by decide +kernel
private theorem cp639 : (⟨(2633475/104524931),0,0,(-130150/104524931)⟩ : CertField) = scaled n639 104524931 := by decide +kernel
private def n640 : IntField := ⟨23811,0,0,76⟩
private theorem pos640 : (0:ℤ) < 921695 := by decide +kernel
private theorem cp640 : (⟨(23811/921695),0,0,(76/921695)⟩ : CertField) = scaled n640 921695 := by decide +kernel
private def n641 : IntField := ⟨14357,0,0,37⟩
private theorem pos641 : (0:ℤ) < 502670 := by decide +kernel
private theorem cp641 : (⟨(2051/71810),0,0,(37/502670)⟩ : CertField) = scaled n641 502670 := by decide +kernel
private def n642 : IntField := ⟨(-599222),1584765,0,0⟩
private theorem pos642 : (0:ℤ) < 54363419 := by decide +kernel
private theorem cp642 : (⟨(-599222/54363419),(1584765/54363419),0,0⟩ : CertField) = scaled n642 54363419 := by decide +kernel
private def n643 : IntField := ⟨737373,0,0,(-36442)⟩
private theorem pos643 : (0:ℤ) < 14932133 := by decide +kernel
private theorem cp643 : (⟨(737373/14932133),0,0,(-36442/14932133)⟩ : CertField) = scaled n643 14932133 := by decide +kernel
private def n644 : IntField := ⟨(-7968384),14207533,0,0⟩
private theorem pos644 : (0:ℤ) < 385486062 := by decide +kernel
private theorem cp644 : (⟨(-1328064/64247677),(14207533/385486062),0,0⟩ : CertField) = scaled n644 385486062 := by decide +kernel
private def n645 : IntField := ⟨296587,1733302,0,0⟩
private theorem pos645 : (0:ℤ) < 72787979 := by decide +kernel
private theorem cp645 : (⟨(296587/72787979),(1733302/72787979),0,0⟩ : CertField) = scaled n645 72787979 := by decide +kernel
private def n646 : IntField := ⟨33653,1,0,0⟩
private theorem pos646 : (0:ℤ) < 86281 := by decide +kernel
private theorem cp646 : (⟨(33653/86281),(1/86281),0,0⟩ : CertField) = scaled n646 86281 := by decide +kernel
private def n647 : IntField := ⟨40426244,99902592,0,0⟩
private theorem pos647 : (0:ℤ) < 312797329 := by decide +kernel
private theorem cp647 : (⟨(40426244/312797329),(99902592/312797329),0,0⟩ : CertField) = scaled n647 312797329 := by decide +kernel
private def n648 : IntField := ⟨15225,0,0,(-1976)⟩
private theorem pos648 : (0:ℤ) < 14217 := by decide +kernel
private theorem cp648 : (⟨(725/677),0,0,(-1976/14217)⟩ : CertField) = scaled n648 14217 := by decide +kernel
private def n649 : IntField := ⟨34058535,0,0,3262775⟩
private theorem pos649 : (0:ℤ) < 65710974 := by decide +kernel
private theorem cp649 : (⟨(1621835/3129094),0,0,(3262775/65710974)⟩ : CertField) = scaled n649 65710974 := by decide +kernel
private def n650 : IntField := ⟨47681949,0,0,4567885⟩
private theorem pos650 : (0:ℤ) < 46936410 := by decide +kernel
private theorem cp650 : (⟨(15893983/15645470),0,0,(913577/9387282)⟩ : CertField) = scaled n650 46936410 := by decide +kernel
private def n651 : IntField := ⟨132489,0,0,(-21755)⟩
private theorem pos651 : (0:ℤ) < 28434 := by decide +kernel
private theorem cp651 : (⟨(6309/1354),0,0,(-21755/28434)⟩ : CertField) = scaled n651 28434 := by decide +kernel
private def n652 : IntField := ⟨113211,0,0,(-18491)⟩
private theorem pos652 : (0:ℤ) < 28434 := by decide +kernel
private theorem cp652 : (⟨(5391/1354),0,0,(-18491/28434)⟩ : CertField) = scaled n652 28434 := by decide +kernel
private def n653 : IntField := ⟨20305875,0,0,3249835⟩
private theorem pos653 : (0:ℤ) < 67856138 := by decide +kernel
private theorem cp653 : (⟨(20305875/67856138),0,0,(3249835/67856138)⟩ : CertField) = scaled n653 67856138 := by decide +kernel
private def n654 : IntField := ⟨28428225,0,0,4549769⟩
private theorem pos654 : (0:ℤ) < 48468670 := by decide +kernel
private theorem cp654 : (⟨(5685645/9693734),0,0,(4549769/48468670)⟩ : CertField) = scaled n654 48468670 := by decide +kernel
private def n655 : IntField := ⟨175287,0,0,17711⟩
private theorem pos655 : (0:ℤ) < 323162 := by decide +kernel
private theorem cp655 : (⟨(25041/46166),0,0,(17711/323162)⟩ : CertField) = scaled n655 323162 := by decide +kernel
private def n656 : IntField := ⟨45661,0,0,1296⟩
private theorem pos656 : (0:ℤ) < 161581 := by decide +kernel
private theorem cp656 : (⟨(6523/23083),0,0,(1296/161581)⟩ : CertField) = scaled n656 161581 := by decide +kernel
private def n657 : IntField := ⟨(-772516),2303835,0,0⟩
private theorem pos657 : (0:ℤ) < 7488217 := by decide +kernel
private theorem cp657 : (⟨(-772516/7488217),(2303835/7488217),0,0⟩ : CertField) = scaled n657 7488217 := by decide +kernel
private def n658 : IntField := ⟨(-6787128),13542941,0,0⟩
private theorem pos658 : (0:ℤ) < 35398844 := by decide +kernel
private theorem cp658 : (⟨(-1696782/8849711),(13542941/35398844),0,0⟩ : CertField) = scaled n658 35398844 := by decide +kernel
private def n659 : IntField := ⟨7755571,33363284,0,0⟩
private theorem pos659 : (0:ℤ) < 132663949 := by decide +kernel
private theorem cp659 : (⟨(7755571/132663949),(33363284/132663949),0,0⟩ : CertField) = scaled n659 132663949 := by decide +kernel
private def n660 : IntField := ⟨40849,118920,0,0⟩
private theorem pos660 : (0:ℤ) < 30251 := by decide +kernel
private theorem cp660 : (⟨(40849/30251),(118920/30251),0,0⟩ : CertField) = scaled n660 30251 := by decide +kernel
private def n661 : IntField := ⟨(-14877963),66978287,0,0⟩
private theorem pos661 : (0:ℤ) < 14248221 := by decide +kernel
private theorem cp661 : (⟨(-4959321/4749407),(66978287/14248221),0,0⟩ : CertField) = scaled n661 14248221 := by decide +kernel
private def n662 : IntField := ⟨9257,(-1),0,0⟩
private theorem pos662 : (0:ℤ) < 34318 := by decide +kernel
private theorem cp662 : (⟨(9257/34318),(-1/34318),0,0⟩ : CertField) = scaled n662 34318 := by decide +kernel
private def n663 : IntField := ⟨165810,323594,0,0⟩
private theorem pos663 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp663 : (⟨(165810/97513),(323594/97513),0,0⟩ : CertField) = scaled n663 97513 := by decide +kernel
private def n664 : IntField := ⟨9471,0,0,(-202)⟩
private theorem pos664 : (0:ℤ) < 777 := by decide +kernel
private theorem cp664 : (⟨(451/37),0,0,(-202/777)⟩ : CertField) = scaled n664 777 := by decide +kernel
private def n665 : IntField := ⟨481577,0,0,34118⟩
private theorem pos665 : (0:ℤ) < 76405 := by decide +kernel
private theorem cp665 : (⟨(481577/76405),0,0,(4874/10915)⟩ : CertField) = scaled n665 76405 := by decide +kernel
private def n666 : IntField := ⟨3371039,0,0,238826⟩
private theorem pos666 : (0:ℤ) < 272875 := by decide +kernel
private theorem cp666 : (⟨(3371039/272875),0,0,(238826/272875)⟩ : CertField) = scaled n666 272875 := by decide +kernel
private def n667 : IntField := ⟨2567,0,0,(-58)⟩
private theorem pos667 : (0:ℤ) < 185 := by decide +kernel
private theorem cp667 : (⟨(2567/185),0,0,(-58/185)⟩ : CertField) = scaled n667 185 := by decide +kernel
private def n668 : IntField := ⟨6303825,0,0,(-4975)⟩
private theorem pos668 : (0:ℤ) < 65508114 := by decide +kernel
private theorem cp668 : (⟨(2101275/21836038),0,0,(-4975/65508114)⟩ : CertField) = scaled n668 65508114 := by decide +kernel
private def n669 : IntField := ⟨15099,0,0,1⟩
private theorem pos669 : (0:ℤ) < 41226 := by decide +kernel
private theorem cp669 : (⟨(5033/13742),0,0,(1/41226)⟩ : CertField) = scaled n669 41226 := by decide +kernel
private def n670 : IntField := ⟨1169,0,0,(-1)⟩
private theorem pos670 : (0:ℤ) < 3178 := by decide +kernel
private theorem cp670 : (⟨(167/454),0,0,(-1/3178)⟩ : CertField) = scaled n670 3178 := by decide +kernel
private def n671 : IntField := ⟨191121,0,0,421⟩
private theorem pos671 : (0:ℤ) < 1439634 := by decide +kernel
private theorem cp671 : (⟨(9101/68554),0,0,(421/1439634)⟩ : CertField) = scaled n671 1439634 := by decide +kernel
private def n672 : IntField := ⟨327,0,0,1⟩
private theorem pos672 : (0:ℤ) < 906 := by decide +kernel
private theorem cp672 : (⟨(109/302),0,0,(1/906)⟩ : CertField) = scaled n672 906 := by decide +kernel
private def n673 : IntField := ⟨(-4002949),11391205,0,0⟩
private theorem pos673 : (0:ℤ) < 91184291 := by decide +kernel
private theorem cp673 : (⟨(-4002949/91184291),(11391205/91184291),0,0⟩ : CertField) = scaled n673 91184291 := by decide +kernel
private def n674 : IntField := ⟨856,1,0,0⟩
private theorem pos674 : (0:ℤ) < 2341 := by decide +kernel
private theorem cp674 : (⟨(856/2341),(1/2341),0,0⟩ : CertField) = scaled n674 2341 := by decide +kernel
private def n675 : IntField := ⟨1301,(-1),0,0⟩
private theorem pos675 : (0:ℤ) < 3541 := by decide +kernel
private theorem cp675 : (⟨(1301/3541),(-1/3541),0,0⟩ : CertField) = scaled n675 3541 := by decide +kernel
private def n676 : IntField := ⟨(-34615287),67024319,0,0⟩
private theorem pos676 : (0:ℤ) < 431053012 := by decide +kernel
private theorem cp676 : (⟨(-34615287/431053012),(67024319/431053012),0,0⟩ : CertField) = scaled n676 431053012 := by decide +kernel
private def n677 : IntField := ⟨2942763,74695124,0,0⟩
private theorem pos677 : (0:ℤ) < 676813533 := by decide +kernel
private theorem cp677 : (⟨(980921/225604511),(74695124/676813533),0,0⟩ : CertField) = scaled n677 676813533 := by decide +kernel
private def n678 : IntField := ⟨19293,(-1),0,0⟩
private theorem pos678 : (0:ℤ) < 52566 := by decide +kernel
private theorem cp678 : (⟨(6431/17522),(-1/52566),0,0⟩ : CertField) = scaled n678 52566 := by decide +kernel
private def n679 : IntField := ⟨9352415,0,0,950325⟩
private theorem pos679 : (0:ℤ) < 73186666 := by decide +kernel
private theorem cp679 : (⟨(9352415/73186666),0,0,(950325/73186666)⟩ : CertField) = scaled n679 73186666 := by decide +kernel
private def n680 : IntField := ⟨18303,0,0,(-1)⟩
private theorem pos680 : (0:ℤ) < 49866 := by decide +kernel
private theorem cp680 : (⟨(6101/16622),0,0,(-1/49866)⟩ : CertField) = scaled n680 49866 := by decide +kernel
private def n681 : IntField := ⟨1765071,0,0,(-1393)⟩
private theorem pos681 : (0:ℤ) < 9358302 := by decide +kernel
private theorem cp681 : (⟨(588357/3119434),0,0,(-1393/9358302)⟩ : CertField) = scaled n681 9358302 := by decide +kernel
private def n682 : IntField := ⟨2343295,4442563,0,0⟩
private theorem pos682 : (0:ℤ) < 3066986 := by decide +kernel
private theorem cp682 : (⟨(2343295/3066986),(4442563/3066986),0,0⟩ : CertField) = scaled n682 3066986 := by decide +kernel
private def n683 : IntField := ⟨4119731,0,0,(-636579)⟩
private theorem pos683 : (0:ℤ) < 349762 := by decide +kernel
private theorem cp683 : (⟨(588533/49966),0,0,(-636579/349762)⟩ : CertField) = scaled n683 349762 := by decide +kernel
private def n684 : IntField := ⟨8711,0,0,(-1)⟩
private theorem pos684 : (0:ℤ) < 32290 := by decide +kernel
private theorem cp684 : (⟨(8711/32290),0,0,(-1/32290)⟩ : CertField) = scaled n684 32290 := by decide +kernel
private def n685 : IntField := ⟨4119731,0,0,(-636579)⟩
private theorem pos685 : (0:ℤ) < 178450 := by decide +kernel
private theorem cp685 : (⟨(4119731/178450),0,0,(-636579/178450)⟩ : CertField) = scaled n685 178450 := by decide +kernel
private def n686 : IntField := ⟨36253,0,0,(-3393)⟩
private theorem pos686 : (0:ℤ) < 4690 := by decide +kernel
private theorem cp686 : (⟨(5179/670),0,0,(-3393/4690)⟩ : CertField) = scaled n686 4690 := by decide +kernel
private def n687 : IntField := ⟨3102587,28971396,0,0⟩
private theorem pos687 : (0:ℤ) < 18519877 := by decide +kernel
private theorem cp687 : (⟨(3102587/18519877),(28971396/18519877),0,0⟩ : CertField) = scaled n687 18519877 := by decide +kernel
private def n688 : IntField := ⟨10229,1,0,0⟩
private theorem pos688 : (0:ℤ) < 38062 := by decide +kernel
private theorem cp688 : (⟨(10229/38062),(1/38062),0,0⟩ : CertField) = scaled n688 38062 := by decide +kernel
private def n689 : IntField := ⟨43953010,57080994,0,0⟩
private theorem pos689 : (0:ℤ) < 47361431 := by decide +kernel
private theorem cp689 : (⟨(43953010/47361431),(57080994/47361431),0,0⟩ : CertField) = scaled n689 47361431 := by decide +kernel
private def ivec1 : Fin 3 → IntField := fun j => blendN 100 tE tF n3 n4 6846 454 j
private def dvec1 : Fin 3 → ℤ := fun _ => 100*6846*454
private def vec1 : Fin 3 → CertField := fun j => scaled (ivec1 j) (dvec1 j)
private theorem dpos1 : ∀ j, (0:ℤ) < dvec1 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos4
private theorem vp1 : productBlend (1/2) (4/5) (⟨(135/326),0,0,(1/6846)⟩ : CertField) (⟨(193/454),0,0,(-1/454)⟩ : CertField) = vec1 := by
  rw [cp3, cp4]
  exact t_blend_scaled n3 n4 6846 454 pos3 pos4
private def ivec2 : Fin 3 → IntField := fun j => blendN 400 sE sF n5 n6 39 13 j
private def dvec2 : Fin 3 → ℤ := fun _ => 400*39*13
private def vec2 : Fin 3 → CertField := fun j => scaled (ivec2 j) (dvec2 j)
private theorem dpos2 : ∀ j, (0:ℤ) < dvec2 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos5) pos6
private theorem vp2 : productBlend (3/4) (4/5) (⟨(3/13),(1/39),0,0⟩ : CertField) (⟨(4/13),(1/13),0,0⟩ : CertField) = vec2 := by
  rw [cp5, cp6]
  exact s_blend_scaled n5 n6 39 13 pos5 pos6
private def ivec3 : Fin 3 → IntField := fun j => blendN 100 tE tF n7 n8 69 11 j
private def dvec3 : Fin 3 → ℤ := fun _ => 100*69*11
private def vec3 : Fin 3 → CertField := fun j => scaled (ivec3 j) (dvec3 j)
private theorem dpos3 : ∀ j, (0:ℤ) < dvec3 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos7) pos8
private theorem vp3 : productBlend (1/2) (4/5) (⟨(10/23),(-1/69),0,0⟩ : CertField) (⟨(5/11),(-1/11),0,0⟩ : CertField) = vec3 := by
  rw [cp7, cp8]
  exact t_blend_scaled n7 n8 69 11 pos7 pos8
private def ivec4 : Fin 3 → IntField := fun j => blendN 400 sE sF n9 n10 2602 94 j
private def dvec4 : Fin 3 → ℤ := fun _ => 400*2602*94
private def vec4 : Fin 3 → CertField := fun j => scaled (ivec4 j) (dvec4 j)
private theorem dpos4 : ∀ j, (0:ℤ) < dvec4 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos9) pos10
private theorem vp4 : productBlend (3/4) (4/5) (⟨(725/2602),0,0,(1/2602)⟩ : CertField) (⟨(31/94),0,0,(-1/94)⟩ : CertField) = vec4 := by
  rw [cp9, cp10]
  exact s_blend_scaled n9 n10 2602 94 pos9 pos10
private def ivec5 : Fin 3 → IntField := fun j => blendN 400 sE sF n12 n13 166 6718 j
private def dvec5 : Fin 3 → ℤ := fun _ => 400*166*6718
private def vec5 : Fin 3 → CertField := fun j => scaled (ivec5 j) (dvec5 j)
private theorem dpos5 : ∀ j, (0:ℤ) < dvec5 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos12) pos13
private theorem vp5 : productBlend (3/4) (4/5) (⟨(41/166),0,0,(1/166)⟩ : CertField) (⟨(1851/6718),0,0,(-1/6718)⟩ : CertField) = vec5 := by
  rw [cp12, cp13]
  exact s_blend_scaled n12 n13 166 6718 pos12 pos13
private def ivec6 : Fin 3 → IntField := fun j => blendN 100 tE tF n14 n15 262 7710 j
private def dvec6 : Fin 3 → ℤ := fun _ => 100*262*7710
private def vec6 : Fin 3 → CertField := fun j => scaled (ivec6 j) (dvec6 j)
private theorem dpos6 : ∀ j, (0:ℤ) < dvec6 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos14) pos15
private theorem vp6 : productBlend (1/2) (4/5) (⟨(105/262),0,0,(1/262)⟩ : CertField) (⟨(1077/2570),0,0,(-1/7710)⟩ : CertField) = vec6 := by
  rw [cp14, cp15]
  exact t_blend_scaled n14 n15 262 7710 pos14 pos15
private def ivec7 : Fin 3 → IntField := fun j => blendN 400 sE sF n12 n10 166 94 j
private def dvec7 : Fin 3 → ℤ := fun _ => 400*166*94
private def vec7 : Fin 3 → CertField := fun j => scaled (ivec7 j) (dvec7 j)
private theorem dpos7 : ∀ j, (0:ℤ) < dvec7 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos12) pos10
private theorem vp7 : productBlend (3/4) (4/5) (⟨(41/166),0,0,(1/166)⟩ : CertField) (⟨(31/94),0,0,(-1/94)⟩ : CertField) = vec7 := by
  rw [cp12, cp10]
  exact s_blend_scaled n12 n10 166 94 pos12 pos10
private def ivec8 : Fin 3 → IntField := fun j => blendN 100 tE tF n14 n17 262 34 j
private def dvec8 : Fin 3 → ℤ := fun _ => 100*262*34
private def vec8 : Fin 3 → CertField := fun j => scaled (ivec8 j) (dvec8 j)
private theorem dpos8 : ∀ j, (0:ℤ) < dvec8 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos14) pos17
private theorem vp8 : productBlend (1/2) (4/5) (⟨(105/262),0,0,(1/262)⟩ : CertField) (⟨(19/34),0,0,(-1/34)⟩ : CertField) = vec8 := by
  rw [cp14, cp17]
  exact t_blend_scaled n14 n17 262 34 pos14 pos17
private def ivec9 : Fin 3 → IntField := fun j => blendN 100 tE tF n19 n4 222 454 j
private def dvec9 : Fin 3 → ℤ := fun _ => 100*222*454
private def vec9 : Fin 3 → CertField := fun j => scaled (ivec9 j) (dvec9 j)
private theorem dpos9 : ∀ j, (0:ℤ) < dvec9 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos19) pos4
private theorem vp9 : productBlend (1/2) (4/5) (⟨(29/74),0,0,(1/222)⟩ : CertField) (⟨(193/454),0,0,(-1/454)⟩ : CertField) = vec9 := by
  rw [cp19, cp4]
  exact t_blend_scaled n19 n4 222 454 pos19 pos4
private def ivec10 : Fin 3 → IntField := fun j => blendN 100 tE tF n21 n22 409 529 j
private def dvec10 : Fin 3 → ℤ := fun _ => 100*409*529
private def vec10 : Fin 3 → CertField := fun j => scaled (ivec10 j) (dvec10 j)
private theorem dpos10 : ∀ j, (0:ℤ) < dvec10 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos21) pos22
private theorem vp10 : productBlend (1/2) (4/5) (⟨(168/409),(1/409),0,0⟩ : CertField) (⟨(223/529),(-1/529),0,0⟩ : CertField) = vec10 := by
  rw [cp21, cp22]
  exact t_blend_scaled n21 n22 409 529 pos21 pos22
private def ivec11 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n24 177 478 j
private def dvec11 : Fin 3 → ℤ := fun _ => 400*177*478
private def vec11 : Fin 3 → CertField := fun j => scaled (ivec11 j) (dvec11 j)
private theorem dpos11 : ∀ j, (0:ℤ) < dvec11 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos24
private theorem vp11 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(133/478),(-1/478),0,0⟩ : CertField) = vec11 := by
  rw [cp23, cp24]
  exact s_blend_scaled n23 n24 177 478 pos23 pos24
private def ivec12 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n26 177 7081 j
private def dvec12 : Fin 3 → ℤ := fun _ => 400*177*7081
private def vec12 : Fin 3 → CertField := fun j => scaled (ivec12 j) (dvec12 j)
private theorem dpos12 : ∀ j, (0:ℤ) < dvec12 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos26
private theorem vp12 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) = vec12 := by
  rw [cp23, cp26]
  exact s_blend_scaled n23 n26 177 7081 pos23 pos26
private def ivec13 : Fin 3 → IntField := fun j => blendN 100 tE tF n21 n28 409 8142 j
private def dvec13 : Fin 3 → ℤ := fun _ => 100*409*8142
private def vec13 : Fin 3 → CertField := fun j => scaled (ivec13 j) (dvec13 j)
private theorem dpos13 : ∀ j, (0:ℤ) < dvec13 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos21) pos28
private theorem vp13 : productBlend (1/2) (4/5) (⟨(168/409),(1/409),0,0⟩ : CertField) (⟨(1137/2714),(-1/8142),0,0⟩ : CertField) = vec13 := by
  rw [cp21, cp28]
  exact t_blend_scaled n21 n28 409 8142 pos21 pos28
private def ivec14 : Fin 3 → IntField := fun j => blendN 100 tE tF n32 n6 2 13 j
private def dvec14 : Fin 3 → ℤ := fun _ => 100*2*13
private def vec14 : Fin 3 → CertField := fun j => scaled (ivec14 j) (dvec14 j)
private theorem dpos14 : ∀ j, (0:ℤ) < dvec14 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos32) pos6
private theorem vp14 : productBlend (1/2) (4/5) (⟨(-1/2),(1/2),0,0⟩ : CertField) (⟨(4/13),(1/13),0,0⟩ : CertField) = vec14 := by
  rw [cp32, cp6]
  exact t_blend_scaled n32 n6 2 13 pos32 pos6
private def ivec15 : Fin 3 → IntField := fun j => blendN 400 sE sF n33 n34 1237 877 j
private def dvec15 : Fin 3 → ℤ := fun _ => 400*1237*877
private def vec15 : Fin 3 → CertField := fun j => scaled (ivec15 j) (dvec15 j)
private theorem dpos15 : ∀ j, (0:ℤ) < dvec15 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos33) pos34
private theorem vp15 : productBlend (3/4) (4/5) (⟨(341/1237),(1/1237),0,0⟩ : CertField) (⟨(246/877),(-1/877),0,0⟩ : CertField) = vec15 := by
  rw [cp33, cp34]
  exact s_blend_scaled n33 n34 1237 877 pos33 pos34
private def ivec16 : Fin 3 → IntField := fun j => blendN 100 tE tF n35 n7 214 69 j
private def dvec16 : Fin 3 → ℤ := fun _ => 100*214*69
private def vec16 : Fin 3 → CertField := fun j => scaled (ivec16 j) (dvec16 j)
private theorem dpos16 : ∀ j, (0:ℤ) < dvec16 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos35) pos7
private theorem vp16 : productBlend (1/2) (4/5) (⟨(89/214),(1/214),0,0⟩ : CertField) (⟨(10/23),(-1/69),0,0⟩ : CertField) = vec16 := by
  rw [cp35, cp7]
  exact t_blend_scaled n35 n7 214 69 pos35 pos7
private def ivec17 : Fin 3 → IntField := fun j => blendN 400 sE sF n6 n36 13 13 j
private def dvec17 : Fin 3 → ℤ := fun _ => 400*13*13
private def vec17 : Fin 3 → CertField := fun j => scaled (ivec17 j) (dvec17 j)
private theorem dpos17 : ∀ j, (0:ℤ) < dvec17 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos6) pos36
private theorem vp17 : productBlend (3/4) (4/5) (⟨(4/13),(1/13),0,0⟩ : CertField) (⟨(9/13),(-1/13),0,0⟩ : CertField) = vec17 := by
  rw [cp6, cp36]
  exact s_blend_scaled n6 n36 13 13 pos6 pos36
private def ivec18 : Fin 3 → IntField := fun j => blendN 400 sE sF n38 n39 1090 15090 j
private def dvec18 : Fin 3 → ℤ := fun _ => 400*1090*15090
private def vec18 : Fin 3 → CertField := fun j => scaled (ivec18 j) (dvec18 j)
private theorem dpos18 : ∀ j, (0:ℤ) < dvec18 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos38) pos39
private theorem vp18 : productBlend (3/4) (4/5) (⟨(299/1090),0,0,(1/1090)⟩ : CertField) (⟨(1403/5030),0,0,(-1/15090)⟩ : CertField) = vec18 := by
  rw [cp38, cp39]
  exact s_blend_scaled n38 n39 1090 15090 pos38 pos39
private def ivec19 : Fin 3 → IntField := fun j => blendN 100 tE tF n40 n41 82 1174 j
private def dvec19 : Fin 3 → ℤ := fun _ => 100*82*1174
private def vec19 : Fin 3 → CertField := fun j => scaled (ivec19 j) (dvec19 j)
private theorem dpos19 : ∀ j, (0:ℤ) < dvec19 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos40) pos41
private theorem vp19 : productBlend (1/2) (4/5) (⟨(29/82),0,0,(1/82)⟩ : CertField) (⟨(487/1174),0,0,(-1/1174)⟩ : CertField) = vec19 := by
  rw [cp40, cp41]
  exact t_blend_scaled n40 n41 82 1174 pos40 pos41
private def ivec20 : Fin 3 → IntField := fun j => blendN 400 sE sF n38 n44 1090 402 j
private def dvec20 : Fin 3 → ℤ := fun _ => 400*1090*402
private def vec20 : Fin 3 → CertField := fun j => scaled (ivec20 j) (dvec20 j)
private theorem dpos20 : ∀ j, (0:ℤ) < dvec20 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos38) pos44
private theorem vp20 : productBlend (3/4) (4/5) (⟨(299/1090),0,0,(1/1090)⟩ : CertField) (⟨(39/134),0,0,(-1/402)⟩ : CertField) = vec20 := by
  rw [cp38, cp44]
  exact s_blend_scaled n38 n44 1090 402 pos38 pos44
private def ivec21 : Fin 3 → IntField := fun j => blendN 100 tE tF n40 n17 82 34 j
private def dvec21 : Fin 3 → ℤ := fun _ => 100*82*34
private def vec21 : Fin 3 → CertField := fun j => scaled (ivec21 j) (dvec21 j)
private theorem dpos21 : ∀ j, (0:ℤ) < dvec21 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos40) pos17
private theorem vp21 : productBlend (1/2) (4/5) (⟨(29/82),0,0,(1/82)⟩ : CertField) (⟨(19/34),0,0,(-1/34)⟩ : CertField) = vec21 := by
  rw [cp40, cp17]
  exact t_blend_scaled n40 n17 82 34 pos40 pos17
private def ivec22 : Fin 3 → IntField := fun j => blendN 400 sE sF n46 n34 18654 877 j
private def dvec22 : Fin 3 → ℤ := fun _ => 400*18654*877
private def vec22 : Fin 3 → CertField := fun j => scaled (ivec22 j) (dvec22 j)
private theorem dpos22 : ∀ j, (0:ℤ) < dvec22 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos46) pos34
private theorem vp22 : productBlend (3/4) (4/5) (⟨(1721/6218),(1/18654),0,0⟩ : CertField) (⟨(246/877),(-1/877),0,0⟩ : CertField) = vec22 := by
  rw [cp46, cp34]
  exact s_blend_scaled n46 n34 18654 877 pos46 pos34
private def ivec23 : Fin 3 → IntField := fun j => blendN 100 tE tF n48 n7 3013 69 j
private def dvec23 : Fin 3 → ℤ := fun _ => 100*3013*69
private def vec23 : Fin 3 → CertField := fun j => scaled (ivec23 j) (dvec23 j)
private theorem dpos23 : ∀ j, (0:ℤ) < dvec23 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos48) pos7
private theorem vp23 : productBlend (1/2) (4/5) (⟨(1272/3013),(1/3013),0,0⟩ : CertField) (⟨(10/23),(-1/69),0,0⟩ : CertField) = vec23 := by
  rw [cp48, cp7]
  exact t_blend_scaled n48 n7 3013 69 pos48 pos7
private def ivec24 : Fin 3 → IntField := fun j => blendN 400 sE sF n50 n51 150 2350 j
private def dvec24 : Fin 3 → ℤ := fun _ => 400*150*2350
private def vec24 : Fin 3 → CertField := fun j => scaled (ivec24 j) (dvec24 j)
private theorem dpos24 : ∀ j, (0:ℤ) < dvec24 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos50) pos51
private theorem vp24 : productBlend (3/4) (4/5) (⟨(13/50),0,0,(1/150)⟩ : CertField) (⟨(689/2350),0,0,(-1/2350)⟩ : CertField) = vec24 := by
  rw [cp50, cp51]
  exact s_blend_scaled n50 n51 150 2350 pos50 pos51
private def ivec25 : Fin 3 → IntField := fun j => blendN 100 tE tF n14 n53 262 510 j
private def dvec25 : Fin 3 → ℤ := fun _ => 100*262*510
private def vec25 : Fin 3 → CertField := fun j => scaled (ivec25 j) (dvec25 j)
private theorem dpos25 : ∀ j, (0:ℤ) < dvec25 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos14) pos53
private theorem vp25 : productBlend (1/2) (4/5) (⟨(105/262),0,0,(1/262)⟩ : CertField) (⟨(73/170),0,0,(-1/510)⟩ : CertField) = vec25 := by
  rw [cp14, cp53]
  exact t_blend_scaled n14 n53 262 510 pos14 pos53
private def ivec26 : Fin 3 → IntField := fun j => blendN 400 sE sF n50 n54 150 82 j
private def dvec26 : Fin 3 → ℤ := fun _ => 400*150*82
private def vec26 : Fin 3 → CertField := fun j => scaled (ivec26 j) (dvec26 j)
private theorem dpos26 : ∀ j, (0:ℤ) < dvec26 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos50) pos54
private theorem vp26 : productBlend (3/4) (4/5) (⟨(13/50),0,0,(1/150)⟩ : CertField) (⟨(29/82),0,0,(-1/82)⟩ : CertField) = vec26 := by
  rw [cp50, cp54]
  exact s_blend_scaled n50 n54 150 82 pos50 pos54
private def ivec27 : Fin 3 → IntField := fun j => blendN 400 sE sF n58 n59 429 142 j
private def dvec27 : Fin 3 → ℤ := fun _ => 400*429*142
private def vec27 : Fin 3 → CertField := fun j => scaled (ivec27 j) (dvec27 j)
private theorem dpos27 : ∀ j, (0:ℤ) < dvec27 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos59
private theorem vp27 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec27 := by
  rw [cp58, cp59]
  exact s_blend_scaled n58 n59 429 142 pos58 pos59
private def ivec28 : Fin 3 → IntField := fun j => blendN 400 sE sF n62 n59 6094 142 j
private def dvec28 : Fin 3 → ℤ := fun _ => 400*6094*142
private def vec28 : Fin 3 → CertField := fun j => scaled (ivec28 j) (dvec28 j)
private theorem dpos28 : ∀ j, (0:ℤ) < dvec28 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos62) pos59
private theorem vp28 : productBlend (3/4) (4/5) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec28 := by
  rw [cp62, cp59]
  exact s_blend_scaled n62 n59 6094 142 pos62 pos59
private def ivec29 : Fin 3 → IntField := fun j => blendN 400 sE sF n64 n54 5794 82 j
private def dvec29 : Fin 3 → ℤ := fun _ => 400*5794*82
private def vec29 : Fin 3 → CertField := fun j => scaled (ivec29 j) (dvec29 j)
private theorem dpos29 : ∀ j, (0:ℤ) < dvec29 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos64) pos54
private theorem vp29 : productBlend (3/4) (4/5) (⟨(1719/5794),0,0,(1/5794)⟩ : CertField) (⟨(29/82),0,0,(-1/82)⟩ : CertField) = vec29 := by
  rw [cp64, cp54]
  exact s_blend_scaled n64 n54 5794 82 pos64 pos54
private def ivec30 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n54 514 82 j
private def dvec30 : Fin 3 → ℤ := fun _ => 400*514*82
private def vec30 : Fin 3 → CertField := fun j => scaled (ivec30 j) (dvec30 j)
private theorem dpos30 : ∀ j, (0:ℤ) < dvec30 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos54
private theorem vp30 : productBlend (3/4) (4/5) (⟨(147/514),0,0,(1/514)⟩ : CertField) (⟨(29/82),0,0,(-1/82)⟩ : CertField) = vec30 := by
  rw [cp66, cp54]
  exact s_blend_scaled n66 n54 514 82 pos66 pos54
private def ivec31 : Fin 3 → IntField := fun j => blendN 100 tE tF n68 n22 7278 529 j
private def dvec31 : Fin 3 → ℤ := fun _ => 100*7278*529
private def vec31 : Fin 3 → CertField := fun j => scaled (ivec31 j) (dvec31 j)
private theorem dpos31 : ∀ j, (0:ℤ) < dvec31 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos68) pos22
private theorem vp31 : productBlend (1/2) (4/5) (⟨(1005/2426),(1/7278),0,0⟩ : CertField) (⟨(223/529),(-1/529),0,0⟩ : CertField) = vec31 := by
  rw [cp68, cp22]
  exact t_blend_scaled n68 n22 7278 529 pos68 pos22
private def ivec32 : Fin 3 → IntField := fun j => blendN 400 sE sF n70 n71 814 1069 j
private def dvec32 : Fin 3 → ℤ := fun _ => 400*814*1069
private def vec32 : Fin 3 → CertField := fun j => scaled (ivec32 j) (dvec32 j)
private theorem dpos32 : ∀ j, (0:ℤ) < dvec32 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos70) pos71
private theorem vp32 : productBlend (3/4) (4/5) (⟨(237/814),(1/814),0,0⟩ : CertField) (⟨(317/1069),(-1/1069),0,0⟩ : CertField) = vec32 := by
  rw [cp70, cp71]
  exact s_blend_scaled n70 n71 814 1069 pos70 pos71
private def ivec33 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n73 514 15526 j
private def dvec33 : Fin 3 → ℤ := fun _ => 400*514*15526
private def vec33 : Fin 3 → CertField := fun j => scaled (ivec33 j) (dvec33 j)
private theorem dpos33 : ∀ j, (0:ℤ) < dvec33 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos73
private theorem vp33 : productBlend (3/4) (4/5) (⟨(147/514),0,0,(1/514)⟩ : CertField) (⟨(655/2218),0,0,(-1/15526)⟩ : CertField) = vec33 := by
  rw [cp66, cp73]
  exact s_blend_scaled n66 n73 514 15526 pos66 pos73
private def ivec34 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n76 514 1042 j
private def dvec34 : Fin 3 → ℤ := fun _ => 400*514*1042
private def vec34 : Fin 3 → CertField := fun j => scaled (ivec34 j) (dvec34 j)
private theorem dpos34 : ∀ j, (0:ℤ) < dvec34 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos76
private theorem vp34 : productBlend (3/4) (4/5) (⟨(147/514),0,0,(1/514)⟩ : CertField) (⟨(313/1042),0,0,(-1/1042)⟩ : CertField) = vec34 := by
  rw [cp66, cp76]
  exact s_blend_scaled n66 n76 514 1042 pos66 pos76
private def ivec35 : Fin 3 → IntField := fun j => blendN 400 sE sF n78 n71 14557 1069 j
private def dvec35 : Fin 3 → ℤ := fun _ => 400*14557*1069
private def vec35 : Fin 3 → CertField := fun j => scaled (ivec35 j) (dvec35 j)
private theorem dpos35 : ∀ j, (0:ℤ) < dvec35 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos78) pos71
private theorem vp35 : productBlend (3/4) (4/5) (⟨(4264/14557),(1/14557),0,0⟩ : CertField) (⟨(317/1069),(-1/1069),0,0⟩ : CertField) = vec35 := by
  rw [cp78, cp71]
  exact s_blend_scaled n78 n71 14557 1069 pos78 pos71
private def ivec36 : Fin 3 → IntField := fun j => blendN 400 sE sF n81 n82 430 922 j
private def dvec36 : Fin 3 → ℤ := fun _ => 400*430*922
private def vec36 : Fin 3 → CertField := fun j => scaled (ivec36 j) (dvec36 j)
private theorem dpos36 : ∀ j, (0:ℤ) < dvec36 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos81) pos82
private theorem vp36 : productBlend (3/4) (4/5) (⟨(121/430),0,0,(1/430)⟩ : CertField) (⟨(275/922),0,0,(-1/922)⟩ : CertField) = vec36 := by
  rw [cp81, cp82]
  exact s_blend_scaled n81 n82 430 922 pos81 pos82
private def ivec37 : Fin 3 → IntField := fun j => blendN 100 tE tF n84 n85 402 34 j
private def dvec37 : Fin 3 → ℤ := fun _ => 100*402*34
private def vec37 : Fin 3 → CertField := fun j => scaled (ivec37 j) (dvec37 j)
private theorem dpos37 : ∀ j, (0:ℤ) < dvec37 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos85
private theorem vp37 : productBlend (1/2) (4/5) (⟨(39/134),0,0,(1/402)⟩ : CertField) (⟨(15/34),0,0,(-1/34)⟩ : CertField) = vec37 := by
  rw [cp84, cp85]
  exact t_blend_scaled n84 n85 402 34 pos84 pos85
private def ivec38 : Fin 3 → IntField := fun j => blendN 400 sE sF n86 n87 202 10 j
private def dvec38 : Fin 3 → ℤ := fun _ => 400*202*10
private def vec38 : Fin 3 → CertField := fun j => scaled (ivec38 j) (dvec38 j)
private theorem dpos38 : ∀ j, (0:ℤ) < dvec38 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos86) pos87
private theorem vp38 : productBlend (3/4) (4/5) (⟨(83/202),0,0,(1/202)⟩ : CertField) (⟨(9/10),0,0,(-1/10)⟩ : CertField) = vec38 := by
  rw [cp86, cp87]
  exact s_blend_scaled n86 n87 202 10 pos86 pos87
private def ivec39 : Fin 3 → IntField := fun j => blendN 400 sE sF n12 n92 166 514 j
private def dvec39 : Fin 3 → ℤ := fun _ => 400*166*514
private def vec39 : Fin 3 → CertField := fun j => scaled (ivec39 j) (dvec39 j)
private theorem dpos39 : ∀ j, (0:ℤ) < dvec39 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos12) pos92
private theorem vp39 : productBlend (3/4) (4/5) (⟨(41/166),0,0,(1/166)⟩ : CertField) (⟨(147/514),0,0,(-1/514)⟩ : CertField) = vec39 := by
  rw [cp12, cp92]
  exact s_blend_scaled n12 n92 166 514 pos12 pos92
private def ivec40 : Fin 3 → IntField := fun j => blendN 100 tE tF n94 n85 6 34 j
private def dvec40 : Fin 3 → ℤ := fun _ => 100*6*34
private def vec40 : Fin 3 → CertField := fun j => scaled (ivec40 j) (dvec40 j)
private theorem dpos40 : ∀ j, (0:ℤ) < dvec40 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos94) pos85
private theorem vp40 : productBlend (1/2) (4/5) (⟨(-1/2),0,0,(1/6)⟩ : CertField) (⟨(15/34),0,0,(-1/34)⟩ : CertField) = vec40 := by
  rw [cp94, cp85]
  exact t_blend_scaled n94 n85 6 34 pos94 pos85
private def ivec41 : Fin 3 → IntField := fun j => blendN 400 sE sF n95 n87 10 10 j
private def dvec41 : Fin 3 → ℤ := fun _ => 400*10*10
private def vec41 : Fin 3 → CertField := fun j => scaled (ivec41 j) (dvec41 j)
private theorem dpos41 : ∀ j, (0:ℤ) < dvec41 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos87
private theorem vp41 : productBlend (3/4) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(9/10),0,0,(-1/10)⟩ : CertField) = vec41 := by
  rw [cp95, cp87]
  exact s_blend_scaled n95 n87 10 10 pos95 pos87
private def ivec42 : Fin 3 → IntField := fun j => blendN 100 tE tF n98 n7 22 69 j
private def dvec42 : Fin 3 → ℤ := fun _ => 100*22*69
private def vec42 : Fin 3 → CertField := fun j => scaled (ivec42 j) (dvec42 j)
private theorem dpos42 : ∀ j, (0:ℤ) < dvec42 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos7
private theorem vp42 : productBlend (1/2) (4/5) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨(10/23),(-1/69),0,0⟩ : CertField) = vec42 := by
  rw [cp98, cp7]
  exact t_blend_scaled n98 n7 22 69 pos98 pos7
private def ivec43 : Fin 3 → IntField := fun j => blendN 400 sE sF n24 n6 478 13 j
private def dvec43 : Fin 3 → ℤ := fun _ => 400*478*13
private def vec43 : Fin 3 → CertField := fun j => scaled (ivec43 j) (dvec43 j)
private theorem dpos43 : ∀ j, (0:ℤ) < dvec43 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos24) pos6
private theorem vp43 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(4/13),(1/13),0,0⟩ : CertField) = vec43 := by
  rw [cp24, cp6]
  exact s_blend_scaled n24 n6 478 13 pos24 pos6
private def ivec44 : Fin 3 → IntField := fun j => blendN 400 sE sF n26 n6 7081 13 j
private def dvec44 : Fin 3 → ℤ := fun _ => 400*7081*13
private def vec44 : Fin 3 → CertField := fun j => scaled (ivec44 j) (dvec44 j)
private theorem dpos44 : ∀ j, (0:ℤ) < dvec44 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos26) pos6
private theorem vp44 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(4/13),(1/13),0,0⟩ : CertField) = vec44 := by
  rw [cp26, cp6]
  exact s_blend_scaled n26 n6 7081 13 pos26 pos6
private def ivec45 : Fin 3 → IntField := fun j => blendN 100 tE tF n98 n101 22 1249 j
private def dvec45 : Fin 3 → ℤ := fun _ => 100*22*1249
private def vec45 : Fin 3 → CertField := fun j => scaled (ivec45 j) (dvec45 j)
private theorem dpos45 : ∀ j, (0:ℤ) < dvec45 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos101
private theorem vp45 : productBlend (1/2) (4/5) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨(517/1249),(-1/1249),0,0⟩ : CertField) = vec45 := by
  rw [cp98, cp101]
  exact t_blend_scaled n98 n101 22 1249 pos98 pos101
private def ivec46 : Fin 3 → IntField := fun j => blendN 100 tE tF n58 n7 429 69 j
private def dvec46 : Fin 3 → ℤ := fun _ => 100*429*69
private def vec46 : Fin 3 → CertField := fun j => scaled (ivec46 j) (dvec46 j)
private theorem dpos46 : ∀ j, (0:ℤ) < dvec46 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos7
private theorem vp46 : productBlend (1/2) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(10/23),(-1/69),0,0⟩ : CertField) = vec46 := by
  rw [cp58, cp7]
  exact t_blend_scaled n58 n7 429 69 pos58 pos7
private def ivec47 : Fin 3 → IntField := fun j => blendN 100 tE tF n58 n101 429 1249 j
private def dvec47 : Fin 3 → ℤ := fun _ => 100*429*1249
private def vec47 : Fin 3 → CertField := fun j => scaled (ivec47 j) (dvec47 j)
private theorem dpos47 : ∀ j, (0:ℤ) < dvec47 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos101
private theorem vp47 : productBlend (1/2) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(517/1249),(-1/1249),0,0⟩ : CertField) = vec47 := by
  rw [cp58, cp101]
  exact t_blend_scaled n58 n101 429 1249 pos58 pos101
private def ivec48 : Fin 3 → IntField := fun j => blendN 100 tE tF n107 n17 2866 34 j
private def dvec48 : Fin 3 → ℤ := fun _ => 100*2866*34
private def vec48 : Fin 3 → CertField := fun j => scaled (ivec48 j) (dvec48 j)
private theorem dpos48 : ∀ j, (0:ℤ) < dvec48 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos107) pos17
private theorem vp48 : productBlend (1/2) (4/5) (⟨(1209/2866),0,0,(1/2866)⟩ : CertField) (⟨(19/34),0,0,(-1/34)⟩ : CertField) = vec48 := by
  rw [cp107, cp17]
  exact t_blend_scaled n107 n17 2866 34 pos107 pos17
private def ivec49 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n108 177 37 j
private def dvec49 : Fin 3 → ℤ := fun _ => 400*177*37
private def vec49 : Fin 3 → CertField := fun j => scaled (ivec49 j) (dvec49 j)
private theorem dpos49 : ∀ j, (0:ℤ) < dvec49 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos108
private theorem vp49 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec49 := by
  rw [cp23, cp108]
  exact s_blend_scaled n23 n108 177 37 pos23 pos108
private def ivec50 : Fin 3 → IntField := fun j => blendN 100 tE tF n109 n35 1006 214 j
private def dvec50 : Fin 3 → ℤ := fun _ => 100*1006*214
private def vec50 : Fin 3 → CertField := fun j => scaled (ivec50 j) (dvec50 j)
private theorem dpos50 : ∀ j, (0:ℤ) < dvec50 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos35
private theorem vp50 : productBlend (1/2) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec50 := by
  rw [cp109, cp35]
  exact t_blend_scaled n109 n35 1006 214 pos109 pos35
private def ivec51 : Fin 3 → IntField := fun j => blendN 400 sE sF n111 n108 2749 37 j
private def dvec51 : Fin 3 → ℤ := fun _ => 400*2749*37
private def vec51 : Fin 3 → CertField := fun j => scaled (ivec51 j) (dvec51 j)
private theorem dpos51 : ∀ j, (0:ℤ) < dvec51 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos111) pos108
private theorem vp51 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec51 := by
  rw [cp111, cp108]
  exact s_blend_scaled n111 n108 2749 37 pos111 pos108
private def ivec52 : Fin 3 → IntField := fun j => blendN 100 tE tF n109 n48 1006 3013 j
private def dvec52 : Fin 3 → ℤ := fun _ => 100*1006*3013
private def vec52 : Fin 3 → CertField := fun j => scaled (ivec52 j) (dvec52 j)
private theorem dpos52 : ∀ j, (0:ℤ) < dvec52 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos48
private theorem vp52 : productBlend (1/2) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(1272/3013),(1/3013),0,0⟩ : CertField) = vec52 := by
  rw [cp109, cp48]
  exact t_blend_scaled n109 n48 1006 3013 pos109 pos48
private def ivec53 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n59 177 142 j
private def dvec53 : Fin 3 → ℤ := fun _ => 400*177*142
private def vec53 : Fin 3 → CertField := fun j => scaled (ivec53 j) (dvec53 j)
private theorem dpos53 : ∀ j, (0:ℤ) < dvec53 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos59
private theorem vp53 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec53 := by
  rw [cp23, cp59]
  exact s_blend_scaled n23 n59 177 142 pos23 pos59
private def ivec54 : Fin 3 → IntField := fun j => blendN 400 sE sF n111 n59 2749 142 j
private def dvec54 : Fin 3 → ℤ := fun _ => 400*2749*142
private def vec54 : Fin 3 → CertField := fun j => scaled (ivec54 j) (dvec54 j)
private theorem dpos54 : ∀ j, (0:ℤ) < dvec54 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos111) pos59
private theorem vp54 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec54 := by
  rw [cp111, cp59]
  exact s_blend_scaled n111 n59 2749 142 pos111 pos59
private def ivec55 : Fin 3 → IntField := fun j => blendN 400 sE sF n58 n108 429 37 j
private def dvec55 : Fin 3 → ℤ := fun _ => 400*429*37
private def vec55 : Fin 3 → CertField := fun j => scaled (ivec55 j) (dvec55 j)
private theorem dpos55 : ∀ j, (0:ℤ) < dvec55 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos108
private theorem vp55 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec55 := by
  rw [cp58, cp108]
  exact s_blend_scaled n58 n108 429 37 pos58 pos108
private def ivec56 : Fin 3 → IntField := fun j => blendN 100 tE tF n108 n35 37 214 j
private def dvec56 : Fin 3 → ℤ := fun _ => 100*37*214
private def vec56 : Fin 3 → CertField := fun j => scaled (ivec56 j) (dvec56 j)
private theorem dpos56 : ∀ j, (0:ℤ) < dvec56 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos108) pos35
private theorem vp56 : productBlend (1/2) (4/5) (⟨(15/37),(-1/37),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec56 := by
  rw [cp108, cp35]
  exact t_blend_scaled n108 n35 37 214 pos108 pos35
private def ivec57 : Fin 3 → IntField := fun j => blendN 400 sE sF n58 n121 429 537 j
private def dvec57 : Fin 3 → ℤ := fun _ => 400*429*537
private def vec57 : Fin 3 → CertField := fun j => scaled (ivec57 j) (dvec57 j)
private theorem dpos57 : ∀ j, (0:ℤ) < dvec57 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos121
private theorem vp57 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec57 := by
  rw [cp58, cp121]
  exact s_blend_scaled n58 n121 429 537 pos58 pos121
private def ivec58 : Fin 3 → IntField := fun j => blendN 400 sE sF n95 n123 10 510 j
private def dvec58 : Fin 3 → ℤ := fun _ => 400*10*510
private def vec58 : Fin 3 → CertField := fun j => scaled (ivec58 j) (dvec58 j)
private theorem dpos58 : ∀ j, (0:ℤ) < dvec58 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos123
private theorem vp58 : productBlend (3/4) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(63/170),0,0,(-1/510)⟩ : CertField) = vec58 := by
  rw [cp95, cp123]
  exact s_blend_scaled n95 n123 10 510 pos95 pos123
private def ivec59 : Fin 3 → IntField := fun j => blendN 100 tE tF n95 n123 10 510 j
private def dvec59 : Fin 3 → ℤ := fun _ => 100*10*510
private def vec59 : Fin 3 → CertField := fun j => scaled (ivec59 j) (dvec59 j)
private theorem dpos59 : ∀ j, (0:ℤ) < dvec59 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos123
private theorem vp59 : productBlend (1/2) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(63/170),0,0,(-1/510)⟩ : CertField) = vec59 := by
  rw [cp95, cp123]
  exact t_blend_scaled n95 n123 10 510 pos95 pos123
private def ivec60 : Fin 3 → IntField := fun j => blendN 100 tE tF n95 n87 10 10 j
private def dvec60 : Fin 3 → ℤ := fun _ => 100*10*10
private def vec60 : Fin 3 → CertField := fun j => scaled (ivec60 j) (dvec60 j)
private theorem dpos60 : ∀ j, (0:ℤ) < dvec60 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos87
private theorem vp60 : productBlend (1/2) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(9/10),0,0,(-1/10)⟩ : CertField) = vec60 := by
  rw [cp95, cp87]
  exact t_blend_scaled n95 n87 10 10 pos95 pos87
private def ivec61 : Fin 3 → IntField := fun j => blendN 100 tE tF n129 n130 9250 262 j
private def dvec61 : Fin 3 → ℤ := fun _ => 100*9250*262
private def vec61 : Fin 3 → CertField := fun j => scaled (ivec61 j) (dvec61 j)
private theorem dpos61 : ∀ j, (0:ℤ) < dvec61 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos129) pos130
private theorem vp61 : productBlend (1/2) (4/5) (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) (⟨(105/262),0,0,(-1/262)⟩ : CertField) = vec61 := by
  rw [cp129, cp130]
  exact t_blend_scaled n129 n130 9250 262 pos129 pos130
private def ivec62 : Fin 3 → IntField := fun j => blendN 400 sE sF n95 n98 10 22 j
private def dvec62 : Fin 3 → ℤ := fun _ => 400*10*22
private def vec62 : Fin 3 → CertField := fun j => scaled (ivec62 j) (dvec62 j)
private theorem dpos62 : ∀ j, (0:ℤ) < dvec62 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos98
private theorem vp62 : productBlend (3/4) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(5/22),(1/22),0,0⟩ : CertField) = vec62 := by
  rw [cp95, cp98]
  exact s_blend_scaled n95 n98 10 22 pos95 pos98
private def ivec63 : Fin 3 → IntField := fun j => blendN 100 tE tF n95 n131 10 94 j
private def dvec63 : Fin 3 → ℤ := fun _ => 100*10*94
private def vec63 : Fin 3 → CertField := fun j => scaled (ivec63 j) (dvec63 j)
private theorem dpos63 : ∀ j, (0:ℤ) < dvec63 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos131
private theorem vp63 : productBlend (1/2) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(35/94),(1/94),0,0⟩ : CertField) = vec63 := by
  rw [cp95, cp131]
  exact t_blend_scaled n95 n131 10 94 pos95 pos131
private def ivec64 : Fin 3 → IntField := fun j => blendN 100 tE tF n133 n134 574 7846 j
private def dvec64 : Fin 3 → ℤ := fun _ => 100*574*7846
private def vec64 : Fin 3 → CertField := fun j => scaled (ivec64 j) (dvec64 j)
private theorem dpos64 : ∀ j, (0:ℤ) < dvec64 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos133) pos134
private theorem vp64 : productBlend (1/2) (4/5) (⟨(31/82),0,0,(1/574)⟩ : CertField) (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) = vec64 := by
  rw [cp133, cp134]
  exact t_blend_scaled n133 n134 574 7846 pos133 pos134
private def ivec65 : Fin 3 → IntField := fun j => blendN 100 tE tF n133 n136 574 202 j
private def dvec65 : Fin 3 → ℤ := fun _ => 100*574*202
private def vec65 : Fin 3 → CertField := fun j => scaled (ivec65 j) (dvec65 j)
private theorem dpos65 : ∀ j, (0:ℤ) < dvec65 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos133) pos136
private theorem vp65 : productBlend (1/2) (4/5) (⟨(31/82),0,0,(1/574)⟩ : CertField) (⟨(83/202),0,0,(-1/202)⟩ : CertField) = vec65 := by
  rw [cp133, cp136]
  exact t_blend_scaled n133 n136 574 202 pos133 pos136
private def ivec66 : Fin 3 → IntField := fun j => blendN 100 tE tF n138 n130 670 262 j
private def dvec66 : Fin 3 → ℤ := fun _ => 100*670*262
private def vec66 : Fin 3 → CertField := fun j => scaled (ivec66 j) (dvec66 j)
private theorem dpos66 : ∀ j, (0:ℤ) < dvec66 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos138) pos130
private theorem vp66 : productBlend (1/2) (4/5) (⟨(251/670),0,0,(1/670)⟩ : CertField) (⟨(105/262),0,0,(-1/262)⟩ : CertField) = vec66 := by
  rw [cp138, cp130]
  exact t_blend_scaled n138 n130 670 262 pos138 pos130
private def ivec67 : Fin 3 → IntField := fun j => blendN 100 tE tF n141 n142 649 454 j
private def dvec67 : Fin 3 → ℤ := fun _ => 100*649*454
private def vec67 : Fin 3 → CertField := fun j => scaled (ivec67 j) (dvec67 j)
private theorem dpos67 : ∀ j, (0:ℤ) < dvec67 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos141) pos142
private theorem vp67 : productBlend (1/2) (4/5) (⟨(247/649),(1/649),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec67 := by
  rw [cp141, cp142]
  exact t_blend_scaled n141 n142 649 454 pos141 pos142
private def ivec68 : Fin 3 → IntField := fun j => blendN 100 tE tF n141 n145 649 8353 j
private def dvec68 : Fin 3 → ℤ := fun _ => 100*649*8353
private def vec68 : Fin 3 → CertField := fun j => scaled (ivec68 j) (dvec68 j)
private theorem dpos68 : ∀ j, (0:ℤ) < dvec68 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos141) pos145
private theorem vp68 : productBlend (1/2) (4/5) (⟨(247/649),(1/649),0,0⟩ : CertField) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = vec68 := by
  rw [cp141, cp145]
  exact t_blend_scaled n141 n145 649 8353 pos141 pos145
private def ivec69 : Fin 3 → IntField := fun j => blendN 100 tE tF n148 n130 94 262 j
private def dvec69 : Fin 3 → ℤ := fun _ => 100*94*262
private def vec69 : Fin 3 → CertField := fun j => scaled (ivec69 j) (dvec69 j)
private theorem dpos69 : ∀ j, (0:ℤ) < dvec69 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos148) pos130
private theorem vp69 : productBlend (1/2) (4/5) (⟨(31/94),0,0,(1/94)⟩ : CertField) (⟨(105/262),0,0,(-1/262)⟩ : CertField) = vec69 := by
  rw [cp148, cp130]
  exact t_blend_scaled n148 n130 94 262 pos148 pos130
private def ivec70 : Fin 3 → IntField := fun j => blendN 100 tE tF n131 n150 94 249 j
private def dvec70 : Fin 3 → ℤ := fun _ => 100*94*249
private def vec70 : Fin 3 → CertField := fun j => scaled (ivec70 j) (dvec70 j)
private theorem dpos70 : ∀ j, (0:ℤ) < dvec70 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos131) pos150
private theorem vp70 : productBlend (1/2) (4/5) (⟨(35/94),(1/94),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec70 := by
  rw [cp131, cp150]
  exact t_blend_scaled n131 n150 94 249 pos131 pos150
private def ivec71 : Fin 3 → IntField := fun j => blendN 400 sE sF n33 n152 1237 16062 j
private def dvec71 : Fin 3 → ℤ := fun _ => 400*1237*16062
private def vec71 : Fin 3 → CertField := fun j => scaled (ivec71 j) (dvec71 j)
private theorem dpos71 : ∀ j, (0:ℤ) < dvec71 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos33) pos152
private theorem vp71 : productBlend (3/4) (4/5) (⟨(341/1237),(1/1237),0,0⟩ : CertField) (⟨(1493/5354),(-1/16062),0,0⟩ : CertField) = vec71 := by
  rw [cp33, cp152]
  exact s_blend_scaled n33 n152 1237 16062 pos33 pos152
private def ivec72 : Fin 3 → IntField := fun j => blendN 100 tE tF n131 n154 94 3718 j
private def dvec72 : Fin 3 → ℤ := fun _ => 100*94*3718
private def vec72 : Fin 3 → CertField := fun j => scaled (ivec72 j) (dvec72 j)
private theorem dpos72 : ∀ j, (0:ℤ) < dvec72 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos131) pos154
private theorem vp72 : productBlend (1/2) (4/5) (⟨(35/94),(1/94),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec72 := by
  rw [cp131, cp154]
  exact t_blend_scaled n131 n154 94 3718 pos131 pos154
private def ivec73 : Fin 3 → IntField := fun j => blendN 100 tE tF n148 n156 94 42 j
private def dvec73 : Fin 3 → ℤ := fun _ => 100*94*42
private def vec73 : Fin 3 → CertField := fun j => scaled (ivec73 j) (dvec73 j)
private theorem dpos73 : ∀ j, (0:ℤ) < dvec73 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos148) pos156
private theorem vp73 : productBlend (1/2) (4/5) (⟨(31/94),0,0,(1/94)⟩ : CertField) (⟨(1/2),0,0,(-1/42)⟩ : CertField) = vec73 := by
  rw [cp148, cp156]
  exact t_blend_scaled n148 n156 94 42 pos148 pos156
private def ivec74 : Fin 3 → IntField := fun j => blendN 400 sE sF n158 n92 17682 514 j
private def dvec74 : Fin 3 → ℤ := fun _ => 400*17682*514
private def vec74 : Fin 3 → CertField := fun j => scaled (ivec74 j) (dvec74 j)
private theorem dpos74 : ∀ j, (0:ℤ) < dvec74 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos158) pos92
private theorem vp74 : productBlend (3/4) (4/5) (⟨(233/842),0,0,(1/17682)⟩ : CertField) (⟨(147/514),0,0,(-1/514)⟩ : CertField) = vec74 := by
  rw [cp158, cp92]
  exact s_blend_scaled n158 n92 17682 514 pos158 pos92
private def ivec75 : Fin 3 → IntField := fun j => blendN 100 tE tF n159 n156 1354 42 j
private def dvec75 : Fin 3 → ℤ := fun _ => 100*1354*42
private def vec75 : Fin 3 → CertField := fun j => scaled (ivec75 j) (dvec75 j)
private theorem dpos75 : ∀ j, (0:ℤ) < dvec75 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos159) pos156
private theorem vp75 : productBlend (1/2) (4/5) (⟨(523/1354),0,0,(1/1354)⟩ : CertField) (⟨(1/2),0,0,(-1/42)⟩ : CertField) = vec75 := by
  rw [cp159, cp156]
  exact t_blend_scaled n159 n156 1354 42 pos159 pos156
private def ivec76 : Fin 3 → IntField := fun j => blendN 400 sE sF n162 n92 1266 514 j
private def dvec76 : Fin 3 → ℤ := fun _ => 400*1266*514
private def vec76 : Fin 3 → CertField := fun j => scaled (ivec76 j) (dvec76 j)
private theorem dpos76 : ∀ j, (0:ℤ) < dvec76 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos162) pos92
private theorem vp76 : productBlend (3/4) (4/5) (⟨(115/422),0,0,(1/1266)⟩ : CertField) (⟨(147/514),0,0,(-1/514)⟩ : CertField) = vec76 := by
  rw [cp162, cp92]
  exact s_blend_scaled n162 n92 1266 514 pos162 pos92
private def ivec77 : Fin 3 → IntField := fun j => blendN 100 tE tF n171 n142 9757 454 j
private def dvec77 : Fin 3 → ℤ := fun _ => 100*9757*454
private def vec77 : Fin 3 → CertField := fun j => scaled (ivec77 j) (dvec77 j)
private theorem dpos77 : ∀ j, (0:ℤ) < dvec77 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos142
private theorem vp77 : productBlend (1/2) (4/5) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec77 := by
  rw [cp171, cp142]
  exact t_blend_scaled n171 n142 9757 454 pos171 pos142
private def ivec78 : Fin 3 → IntField := fun j => blendN 400 sE sF n70 n174 814 16393 j
private def dvec78 : Fin 3 → ℤ := fun _ => 400*814*16393
private def vec78 : Fin 3 → CertField := fun j => scaled (ivec78 j) (dvec78 j)
private theorem dpos78 : ∀ j, (0:ℤ) < dvec78 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos70) pos174
private theorem vp78 : productBlend (3/4) (4/5) (⟨(237/814),(1/814),0,0⟩ : CertField) (⟨(4840/16393),(-1/16393),0,0⟩ : CertField) = vec78 := by
  rw [cp70, cp174]
  exact s_blend_scaled n70 n174 814 16393 pos70 pos174
private def ivec79 : Fin 3 → IntField := fun j => blendN 400 sE sF n177 n82 13690 922 j
private def dvec79 : Fin 3 → ℤ := fun _ => 400*13690*922
private def vec79 : Fin 3 → CertField := fun j => scaled (ivec79 j) (dvec79 j)
private theorem dpos79 : ∀ j, (0:ℤ) < dvec79 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos177) pos82
private theorem vp79 : productBlend (3/4) (4/5) (⟨(4009/13690),0,0,(1/13690)⟩ : CertField) (⟨(275/922),0,0,(-1/922)⟩ : CertField) = vec79 := by
  rw [cp177, cp82]
  exact s_blend_scaled n177 n82 13690 922 pos177 pos82
private def ivec80 : Fin 3 → IntField := fun j => blendN 100 tE tF n181 n182 1770 51358 j
private def dvec80 : Fin 3 → ℤ := fun _ => 100*1770*51358
private def vec80 : Fin 3 → CertField := fun j => scaled (ivec80 j) (dvec80 j)
private theorem dpos80 : ∀ j, (0:ℤ) < dvec80 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos181) pos182
private theorem vp80 : productBlend (1/2) (4/5) (⟨(227/590),0,0,(1/1770)⟩ : CertField) (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) = vec80 := by
  rw [cp181, cp182]
  exact t_blend_scaled n181 n182 1770 51358 pos181 pos182
private def ivec81 : Fin 3 → IntField := fun j => blendN 400 sE sF n84 n183 402 4354 j
private def dvec81 : Fin 3 → ℤ := fun _ => 400*402*4354
private def vec81 : Fin 3 → CertField := fun j => scaled (ivec81 j) (dvec81 j)
private theorem dpos81 : ∀ j, (0:ℤ) < dvec81 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos183
private theorem vp81 : productBlend (3/4) (4/5) (⟨(39/134),0,0,(1/402)⟩ : CertField) (⟨(189/622),0,0,(-1/4354)⟩ : CertField) = vec81 := by
  rw [cp84, cp183]
  exact s_blend_scaled n84 n183 402 4354 pos84 pos183
private def ivec82 : Fin 3 → IntField := fun j => blendN 100 tE tF n181 n185 1770 3370 j
private def dvec82 : Fin 3 → ℤ := fun _ => 100*1770*3370
private def vec82 : Fin 3 → CertField := fun j => scaled (ivec82 j) (dvec82 j)
private theorem dpos82 : ∀ j, (0:ℤ) < dvec82 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos181) pos185
private theorem vp82 : productBlend (1/2) (4/5) (⟨(227/590),0,0,(1/1770)⟩ : CertField) (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) = vec82 := by
  rw [cp181, cp185]
  exact t_blend_scaled n181 n185 1770 3370 pos181 pos185
private def ivec83 : Fin 3 → IntField := fun j => blendN 400 sE sF n84 n85 402 34 j
private def dvec83 : Fin 3 → ℤ := fun _ => 400*402*34
private def vec83 : Fin 3 → CertField := fun j => scaled (ivec83 j) (dvec83 j)
private theorem dpos83 : ∀ j, (0:ℤ) < dvec83 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos85
private theorem vp83 : productBlend (3/4) (4/5) (⟨(39/134),0,0,(1/402)⟩ : CertField) (⟨(15/34),0,0,(-1/34)⟩ : CertField) = vec83 := by
  rw [cp84, cp85]
  exact s_blend_scaled n84 n85 402 34 pos84 pos85
private def ivec84 : Fin 3 → IntField := fun j => blendN 100 tE tF n187 n188 1510 3010 j
private def dvec84 : Fin 3 → ℤ := fun _ => 100*1510*3010
private def vec84 : Fin 3 → CertField := fun j => scaled (ivec84 j) (dvec84 j)
private theorem dpos84 : ∀ j, (0:ℤ) < dvec84 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos187) pos188
private theorem vp84 : productBlend (1/2) (4/5) (⟨(579/1510),0,0,(1/1510)⟩ : CertField) (⟨(167/430),0,0,(-1/3010)⟩ : CertField) = vec84 := by
  rw [cp187, cp188]
  exact t_blend_scaled n187 n188 1510 3010 pos187 pos188
private def ivec85 : Fin 3 → IntField := fun j => blendN 100 tE tF n190 n191 2742 3517 j
private def dvec85 : Fin 3 → ℤ := fun _ => 100*2742*3517
private def vec85 : Fin 3 → CertField := fun j => scaled (ivec85 j) (dvec85 j)
private theorem dpos85 : ∀ j, (0:ℤ) < dvec85 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos190) pos191
private theorem vp85 : productBlend (1/2) (4/5) (⟨(353/914),(1/2742),0,0⟩ : CertField) (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) = vec85 := by
  rw [cp190, cp191]
  exact t_blend_scaled n190 n191 2742 3517 pos190 pos191
private def ivec86 : Fin 3 → IntField := fun j => blendN 400 sE sF n192 n193 10753 229 j
private def dvec86 : Fin 3 → ℤ := fun _ => 400*10753*229
private def vec86 : Fin 3 → CertField := fun j => scaled (ivec86 j) (dvec86 j)
private theorem dpos86 : ∀ j, (0:ℤ) < dvec86 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos192) pos193
private theorem vp86 : productBlend (3/4) (4/5) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec86 := by
  rw [cp192, cp193]
  exact s_blend_scaled n192 n193 10753 229 pos192 pos193
private def ivec87 : Fin 3 → IntField := fun j => blendN 400 sE sF n196 n197 1549 1894 j
private def dvec87 : Fin 3 → ℤ := fun _ => 400*1549*1894
private def vec87 : Fin 3 → CertField := fun j => scaled (ivec87 j) (dvec87 j)
private theorem dpos87 : ∀ j, (0:ℤ) < dvec87 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos196) pos197
private theorem vp87 : productBlend (3/4) (4/5) (⟨(469/1549),(1/1549),0,0⟩ : CertField) (⟨(579/1894),(-1/1894),0,0⟩ : CertField) = vec87 := by
  rw [cp196, cp197]
  exact s_blend_scaled n196 n197 1549 1894 pos196 pos197
private def ivec88 : Fin 3 → IntField := fun j => blendN 100 tE tF n198 n142 1429 454 j
private def dvec88 : Fin 3 → ℤ := fun _ => 100*1429*454
private def vec88 : Fin 3 → CertField := fun j => scaled (ivec88 j) (dvec88 j)
private theorem dpos88 : ∀ j, (0:ℤ) < dvec88 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos198) pos142
private theorem vp88 : productBlend (1/2) (4/5) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec88 := by
  rw [cp198, cp142]
  exact t_blend_scaled n198 n142 1429 454 pos198 pos142
private def ivec89 : Fin 3 → IntField := fun j => blendN 400 sE sF n200 n201 1042 27970 j
private def dvec89 : Fin 3 → ℤ := fun _ => 400*1042*27970
private def vec89 : Fin 3 → CertField := fun j => scaled (ivec89 j) (dvec89 j)
private theorem dpos89 : ∀ j, (0:ℤ) < dvec89 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos200) pos201
private theorem vp89 : productBlend (3/4) (4/5) (⟨(313/1042),0,0,(1/1042)⟩ : CertField) (⟨(8531/27970),0,0,(-1/27970)⟩ : CertField) = vec89 := by
  rw [cp200, cp201]
  exact s_blend_scaled n200 n201 1042 27970 pos200 pos201
private def ivec90 : Fin 3 → IntField := fun j => blendN 400 sE sF n200 n204 1042 1750 j
private def dvec90 : Fin 3 → ℤ := fun _ => 400*1042*1750
private def vec90 : Fin 3 → CertField := fun j => scaled (ivec90 j) (dvec90 j)
private theorem dpos90 : ∀ j, (0:ℤ) < dvec90 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos200) pos204
private theorem vp90 : productBlend (3/4) (4/5) (⟨(313/1042),0,0,(1/1042)⟩ : CertField) (⟨(77/250),0,0,(-1/1750)⟩ : CertField) = vec90 := by
  rw [cp200, cp204]
  exact s_blend_scaled n200 n204 1042 1750 pos200 pos204
private def ivec91 : Fin 3 → IntField := fun j => blendN 400 sE sF n206 n197 27073 1894 j
private def dvec91 : Fin 3 → ℤ := fun _ => 400*27073*1894
private def vec91 : Fin 3 → CertField := fun j => scaled (ivec91 j) (dvec91 j)
private theorem dpos91 : ∀ j, (0:ℤ) < dvec91 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos206) pos197
private theorem vp91 : productBlend (3/4) (4/5) (⟨(8222/27073),(1/27073),0,0⟩ : CertField) (⟨(579/1894),(-1/1894),0,0⟩ : CertField) = vec91 := by
  rw [cp206, cp197]
  exact s_blend_scaled n206 n197 27073 1894 pos206 pos197
private def ivec92 : Fin 3 → IntField := fun j => blendN 100 tE tF n208 n142 20022 454 j
private def dvec92 : Fin 3 → ℤ := fun _ => 100*20022*454
private def vec92 : Fin 3 → CertField := fun j => scaled (ivec92 j) (dvec92 j)
private theorem dpos92 : ∀ j, (0:ℤ) < dvec92 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos208) pos142
private theorem vp92 : productBlend (1/2) (4/5) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec92 := by
  rw [cp208, cp142]
  exact t_blend_scaled n208 n142 20022 454 pos208 pos142
private def ivec93 : Fin 3 → IntField := fun j => blendN 400 sE sF n210 n211 922 1594 j
private def dvec93 : Fin 3 → ℤ := fun _ => 400*922*1594
private def vec93 : Fin 3 → CertField := fun j => scaled (ivec93 j) (dvec93 j)
private theorem dpos93 : ∀ j, (0:ℤ) < dvec93 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos210) pos211
private theorem vp93 : productBlend (3/4) (4/5) (⟨(275/922),0,0,(1/922)⟩ : CertField) (⟨(489/1594),0,0,(-1/1594)⟩ : CertField) = vec93 := by
  rw [cp210, cp211]
  exact s_blend_scaled n210 n211 922 1594 pos210 pos211
private def ivec94 : Fin 3 → IntField := fun j => blendN 100 tE tF n213 n214 3370 88618 j
private def dvec94 : Fin 3 → ℤ := fun _ => 100*3370*88618
private def vec94 : Fin 3 → CertField := fun j => scaled (ivec94 j) (dvec94 j)
private theorem dpos94 : ∀ j, (0:ℤ) < dvec94 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos213) pos214
private theorem vp94 : productBlend (1/2) (4/5) (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) = vec94 := by
  rw [cp213, cp214]
  exact t_blend_scaled n213 n214 3370 88618 pos213 pos214
private def ivec95 : Fin 3 → IntField := fun j => blendN 100 tE tF n213 n216 3370 5470 j
private def dvec95 : Fin 3 → ℤ := fun _ => 100*3370*5470
private def vec95 : Fin 3 → CertField := fun j => scaled (ivec95 j) (dvec95 j)
private theorem dpos95 : ∀ j, (0:ℤ) < dvec95 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos213) pos216
private theorem vp95 : productBlend (1/2) (4/5) (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) = vec95 := by
  rw [cp213, cp216]
  exact t_blend_scaled n213 n216 3370 5470 pos213 pos216
private def ivec96 : Fin 3 → IntField := fun j => blendN 100 tE tF n218 n219 3010 5010 j
private def dvec96 : Fin 3 → ℤ := fun _ => 100*3010*5010
private def vec96 : Fin 3 → CertField := fun j => scaled (ivec96 j) (dvec96 j)
private theorem dpos96 : ∀ j, (0:ℤ) < dvec96 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos218) pos219
private theorem vp96 : productBlend (1/2) (4/5) (⟨(167/430),0,0,(1/3010)⟩ : CertField) (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) = vec96 := by
  rw [cp218, cp219]
  exact t_blend_scaled n218 n219 3010 5010 pos218 pos219
private def ivec97 : Fin 3 → IntField := fun j => blendN 100 tE tF n221 n222 4957 5982 j
private def dvec97 : Fin 3 → ℤ := fun _ => 100*4957*5982
private def vec97 : Fin 3 → CertField := fun j => scaled (ivec97 j) (dvec97 j)
private theorem dpos97 : ∀ j, (0:ℤ) < dvec97 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos221) pos222
private theorem vp97 : productBlend (1/2) (4/5) (⟨(1932/4957),(1/4957),0,0⟩ : CertField) (⟨(779/1994),(-1/5982),0,0⟩ : CertField) = vec97 := by
  rw [cp221, cp222]
  exact t_blend_scaled n221 n222 4957 5982 pos221 pos222
private def ivec98 : Fin 3 → IntField := fun j => blendN 100 tE tF n225 n226 33937 709 j
private def dvec98 : Fin 3 → ℤ := fun _ => 100*33937*709
private def vec98 : Fin 3 → CertField := fun j => scaled (ivec98 j) (dvec98 j)
private theorem dpos98 : ∀ j, (0:ℤ) < dvec98 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos225) pos226
private theorem vp98 : productBlend (1/2) (4/5) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) (⟨(278/709),(-1/709),0,0⟩ : CertField) = vec98 := by
  rw [cp225, cp226]
  exact t_blend_scaled n225 n226 33937 709 pos225 pos226
private def ivec99 : Fin 3 → IntField := fun j => blendN 100 tE tF n159 n228 1354 13866 j
private def dvec99 : Fin 3 → ℤ := fun _ => 100*1354*13866
private def vec99 : Fin 3 → CertField := fun j => scaled (ivec99 j) (dvec99 j)
private theorem dpos99 : ∀ j, (0:ℤ) < dvec99 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos159) pos228
private theorem vp99 : productBlend (1/2) (4/5) (⟨(523/1354),0,0,(1/1354)⟩ : CertField) (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) = vec99 := by
  rw [cp159, cp228]
  exact t_blend_scaled n159 n228 1354 13866 pos159 pos228
private def ivec100 : Fin 3 → IntField := fun j => blendN 100 tE tF n148 n233 94 3526 j
private def dvec100 : Fin 3 → ℤ := fun _ => 100*94*3526
private def vec100 : Fin 3 → CertField := fun j => scaled (ivec100 j) (dvec100 j)
private theorem dpos100 : ∀ j, (0:ℤ) < dvec100 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos148) pos233
private theorem vp100 : productBlend (1/2) (4/5) (⟨(31/94),0,0,(1/94)⟩ : CertField) (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) = vec100 := by
  rw [cp148, cp233]
  exact t_blend_scaled n148 n233 94 3526 pos148 pos233
private def ivec101 : Fin 3 → IntField := fun j => blendN 100 tE tF n98 n150 22 249 j
private def dvec101 : Fin 3 → ℤ := fun _ => 100*22*249
private def vec101 : Fin 3 → CertField := fun j => scaled (ivec101 j) (dvec101 j)
private theorem dpos101 : ∀ j, (0:ℤ) < dvec101 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos150
private theorem vp101 : productBlend (1/2) (4/5) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec101 := by
  rw [cp98, cp150]
  exact t_blend_scaled n98 n150 22 249 pos98 pos150
private def ivec102 : Fin 3 → IntField := fun j => blendN 400 sE sF n24 n35 478 214 j
private def dvec102 : Fin 3 → ℤ := fun _ => 400*478*214
private def vec102 : Fin 3 → CertField := fun j => scaled (ivec102 j) (dvec102 j)
private theorem dpos102 : ∀ j, (0:ℤ) < dvec102 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos24) pos35
private theorem vp102 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec102 := by
  rw [cp24, cp35]
  exact s_blend_scaled n24 n35 478 214 pos24 pos35
private def ivec103 : Fin 3 → IntField := fun j => blendN 400 sE sF n26 n35 7081 214 j
private def dvec103 : Fin 3 → ℤ := fun _ => 400*7081*214
private def vec103 : Fin 3 → CertField := fun j => scaled (ivec103 j) (dvec103 j)
private theorem dpos103 : ∀ j, (0:ℤ) < dvec103 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos26) pos35
private theorem vp103 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec103 := by
  rw [cp26, cp35]
  exact s_blend_scaled n26 n35 7081 214 pos26 pos35
private def ivec104 : Fin 3 → IntField := fun j => blendN 100 tE tF n98 n154 22 3718 j
private def dvec104 : Fin 3 → ℤ := fun _ => 100*22*3718
private def vec104 : Fin 3 → CertField := fun j => scaled (ivec104 j) (dvec104 j)
private theorem dpos104 : ∀ j, (0:ℤ) < dvec104 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos154
private theorem vp104 : productBlend (1/2) (4/5) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec104 := by
  rw [cp98, cp154]
  exact t_blend_scaled n98 n154 22 3718 pos98 pos154
private def ivec105 : Fin 3 → IntField := fun j => blendN 100 tE tF n58 n150 429 249 j
private def dvec105 : Fin 3 → ℤ := fun _ => 100*429*249
private def vec105 : Fin 3 → CertField := fun j => scaled (ivec105 j) (dvec105 j)
private theorem dpos105 : ∀ j, (0:ℤ) < dvec105 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos150
private theorem vp105 : productBlend (1/2) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec105 := by
  rw [cp58, cp150]
  exact t_blend_scaled n58 n150 429 249 pos58 pos150
private def ivec106 : Fin 3 → IntField := fun j => blendN 100 tE tF n58 n154 429 3718 j
private def dvec106 : Fin 3 → ℤ := fun _ => 100*429*3718
private def vec106 : Fin 3 → CertField := fun j => scaled (ivec106 j) (dvec106 j)
private theorem dpos106 : ∀ j, (0:ℤ) < dvec106 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos154
private theorem vp106 : productBlend (1/2) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec106 := by
  rw [cp58, cp154]
  exact t_blend_scaled n58 n154 429 3718 pos58 pos154
private def ivec107 : Fin 3 → IntField := fun j => blendN 100 tE tF n109 n131 1006 94 j
private def dvec107 : Fin 3 → ℤ := fun _ => 100*1006*94
private def vec107 : Fin 3 → CertField := fun j => scaled (ivec107 j) (dvec107 j)
private theorem dpos107 : ∀ j, (0:ℤ) < dvec107 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos131
private theorem vp107 : productBlend (1/2) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(35/94),(1/94),0,0⟩ : CertField) = vec107 := by
  rw [cp109, cp131]
  exact t_blend_scaled n109 n131 1006 94 pos109 pos131
private def ivec108 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n251 177 2497 j
private def dvec108 : Fin 3 → ℤ := fun _ => 400*177*2497
private def vec108 : Fin 3 → CertField := fun j => scaled (ivec108 j) (dvec108 j)
private theorem dpos108 : ∀ j, (0:ℤ) < dvec108 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos251
private theorem vp108 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(731/2497),(-1/2497),0,0⟩ : CertField) = vec108 := by
  rw [cp23, cp251]
  exact s_blend_scaled n23 n251 177 2497 pos23 pos251
private def ivec109 : Fin 3 → IntField := fun j => blendN 400 sE sF n58 n193 429 229 j
private def dvec109 : Fin 3 → ℤ := fun _ => 400*429*229
private def vec109 : Fin 3 → CertField := fun j => scaled (ivec109 j) (dvec109 j)
private theorem dpos109 : ∀ j, (0:ℤ) < dvec109 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos193
private theorem vp109 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec109 := by
  rw [cp58, cp193]
  exact s_blend_scaled n58 n193 429 229 pos58 pos193
private def ivec110 : Fin 3 → IntField := fun j => blendN 100 tE tF n131 n142 94 454 j
private def dvec110 : Fin 3 → ℤ := fun _ => 100*94*454
private def vec110 : Fin 3 → CertField := fun j => scaled (ivec110 j) (dvec110 j)
private theorem dpos110 : ∀ j, (0:ℤ) < dvec110 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos131) pos142
private theorem vp110 : productBlend (1/2) (4/5) (⟨(35/94),(1/94),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec110 := by
  rw [cp131, cp142]
  exact t_blend_scaled n131 n142 94 454 pos131 pos142
private def ivec111 : Fin 3 → IntField := fun j => blendN 400 sE sF n58 n259 429 4654 j
private def dvec111 : Fin 3 → ℤ := fun _ => 400*429*4654
private def vec111 : Fin 3 → CertField := fun j => scaled (ivec111 j) (dvec111 j)
private theorem dpos111 : ∀ j, (0:ℤ) < dvec111 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos259
private theorem vp111 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = vec111 := by
  rw [cp58, cp259]
  exact s_blend_scaled n58 n259 429 4654 pos58 pos259
private def ivec112 : Fin 3 → IntField := fun j => blendN 100 tE tF n131 n145 94 8353 j
private def dvec112 : Fin 3 → ℤ := fun _ => 100*94*8353
private def vec112 : Fin 3 → CertField := fun j => scaled (ivec112 j) (dvec112 j)
private theorem dpos112 : ∀ j, (0:ℤ) < dvec112 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos131) pos145
private theorem vp112 : productBlend (1/2) (4/5) (⟨(35/94),(1/94),0,0⟩ : CertField) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = vec112 := by
  rw [cp131, cp145]
  exact t_blend_scaled n131 n145 94 8353 pos131 pos145
private def ivec113 : Fin 3 → IntField := fun j => blendN 100 tE tF n198 n226 1429 709 j
private def dvec113 : Fin 3 → ℤ := fun _ => 100*1429*709
private def vec113 : Fin 3 → CertField := fun j => scaled (ivec113 j) (dvec113 j)
private theorem dpos113 : ∀ j, (0:ℤ) < dvec113 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos198) pos226
private theorem vp113 : productBlend (1/2) (4/5) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(278/709),(-1/709),0,0⟩ : CertField) = vec113 := by
  rw [cp198, cp226]
  exact t_blend_scaled n198 n226 1429 709 pos198 pos226
private def ivec114 : Fin 3 → IntField := fun j => blendN 100 tE tF n225 n7 33937 69 j
private def dvec114 : Fin 3 → ℤ := fun _ => 100*33937*69
private def vec114 : Fin 3 → CertField := fun j => scaled (ivec114 j) (dvec114 j)
private theorem dpos114 : ∀ j, (0:ℤ) < dvec114 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos225) pos7
private theorem vp114 : productBlend (1/2) (4/5) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) (⟨(10/23),(-1/69),0,0⟩ : CertField) = vec114 := by
  rw [cp225, cp7]
  exact t_blend_scaled n225 n7 33937 69 pos225 pos7
private def ivec115 : Fin 3 → IntField := fun j => blendN 400 sE sF n24 n192 478 10753 j
private def dvec115 : Fin 3 → ℤ := fun _ => 400*478*10753
private def vec115 : Fin 3 → CertField := fun j => scaled (ivec115 j) (dvec115 j)
private theorem dpos115 : ∀ j, (0:ℤ) < dvec115 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos24) pos192
private theorem vp115 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = vec115 := by
  rw [cp24, cp192]
  exact s_blend_scaled n24 n192 478 10753 pos24 pos192
private def ivec116 : Fin 3 → IntField := fun j => blendN 400 sE sF n26 n192 7081 10753 j
private def dvec116 : Fin 3 → ℤ := fun _ => 400*7081*10753
private def vec116 : Fin 3 → CertField := fun j => scaled (ivec116 j) (dvec116 j)
private theorem dpos116 : ∀ j, (0:ℤ) < dvec116 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos26) pos192
private theorem vp116 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = vec116 := by
  rw [cp26, cp192]
  exact s_blend_scaled n26 n192 7081 10753 pos26 pos192
private def ivec117 : Fin 3 → IntField := fun j => blendN 100 tE tF n225 n101 33937 1249 j
private def dvec117 : Fin 3 → ℤ := fun _ => 100*33937*1249
private def vec117 : Fin 3 → CertField := fun j => scaled (ivec117 j) (dvec117 j)
private theorem dpos117 : ∀ j, (0:ℤ) < dvec117 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos225) pos101
private theorem vp117 : productBlend (1/2) (4/5) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) (⟨(517/1249),(-1/1249),0,0⟩ : CertField) = vec117 := by
  rw [cp225, cp101]
  exact t_blend_scaled n225 n101 33937 1249 pos225 pos101
private def ivec118 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n193 177 229 j
private def dvec118 : Fin 3 → ℤ := fun _ => 400*177*229
private def vec118 : Fin 3 → CertField := fun j => scaled (ivec118 j) (dvec118 j)
private theorem dpos118 : ∀ j, (0:ℤ) < dvec118 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos193
private theorem vp118 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec118 := by
  rw [cp23, cp193]
  exact s_blend_scaled n23 n193 177 229 pos23 pos193
private def ivec119 : Fin 3 → IntField := fun j => blendN 100 tE tF n226 n35 709 214 j
private def dvec119 : Fin 3 → ℤ := fun _ => 100*709*214
private def vec119 : Fin 3 → CertField := fun j => scaled (ivec119 j) (dvec119 j)
private theorem dpos119 : ∀ j, (0:ℤ) < dvec119 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos226) pos35
private theorem vp119 : productBlend (1/2) (4/5) (⟨(278/709),(-1/709),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec119 := by
  rw [cp226, cp35]
  exact t_blend_scaled n226 n35 709 214 pos226 pos35
private def ivec120 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n259 177 4654 j
private def dvec120 : Fin 3 → ℤ := fun _ => 400*177*4654
private def vec120 : Fin 3 → CertField := fun j => scaled (ivec120 j) (dvec120 j)
private theorem dpos120 : ∀ j, (0:ℤ) < dvec120 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos259
private theorem vp120 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = vec120 := by
  rw [cp23, cp259]
  exact s_blend_scaled n23 n259 177 4654 pos23 pos259
private def ivec121 : Fin 3 → IntField := fun j => blendN 100 tE tF n274 n35 14838 214 j
private def dvec121 : Fin 3 → ℤ := fun _ => 100*14838*214
private def vec121 : Fin 3 → CertField := fun j => scaled (ivec121 j) (dvec121 j)
private theorem dpos121 : ∀ j, (0:ℤ) < dvec121 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos274) pos35
private theorem vp121 : productBlend (1/2) (4/5) (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec121 := by
  rw [cp274, cp35]
  exact t_blend_scaled n274 n35 14838 214 pos274 pos35
private def ivec122 : Fin 3 → IntField := fun j => blendN 400 sE sF n111 n193 2749 229 j
private def dvec122 : Fin 3 → ℤ := fun _ => 400*2749*229
private def vec122 : Fin 3 → CertField := fun j => scaled (ivec122 j) (dvec122 j)
private theorem dpos122 : ∀ j, (0:ℤ) < dvec122 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos111) pos193
private theorem vp122 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec122 := by
  rw [cp111, cp193]
  exact s_blend_scaled n111 n193 2749 229 pos111 pos193
private def ivec123 : Fin 3 → IntField := fun j => blendN 400 sE sF n111 n259 2749 4654 j
private def dvec123 : Fin 3 → ℤ := fun _ => 400*2749*4654
private def vec123 : Fin 3 → CertField := fun j => scaled (ivec123 j) (dvec123 j)
private theorem dpos123 : ∀ j, (0:ℤ) < dvec123 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos111) pos259
private theorem vp123 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = vec123 := by
  rw [cp111, cp259]
  exact s_blend_scaled n111 n259 2749 4654 pos111 pos259
private def ivec124 : Fin 3 → IntField := fun j => blendN 100 tE tF n226 n48 709 3013 j
private def dvec124 : Fin 3 → ℤ := fun _ => 100*709*3013
private def vec124 : Fin 3 → CertField := fun j => scaled (ivec124 j) (dvec124 j)
private theorem dpos124 : ∀ j, (0:ℤ) < dvec124 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos226) pos48
private theorem vp124 : productBlend (1/2) (4/5) (⟨(278/709),(-1/709),0,0⟩ : CertField) (⟨(1272/3013),(1/3013),0,0⟩ : CertField) = vec124 := by
  rw [cp226, cp48]
  exact t_blend_scaled n226 n48 709 3013 pos226 pos48
private def ivec125 : Fin 3 → IntField := fun j => blendN 100 tE tF n274 n48 14838 3013 j
private def dvec125 : Fin 3 → ℤ := fun _ => 100*14838*3013
private def vec125 : Fin 3 → CertField := fun j => scaled (ivec125 j) (dvec125 j)
private theorem dpos125 : ∀ j, (0:ℤ) < dvec125 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos274) pos48
private theorem vp125 : productBlend (1/2) (4/5) (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) (⟨(1272/3013),(1/3013),0,0⟩ : CertField) = vec125 := by
  rw [cp274, cp48]
  exact t_blend_scaled n274 n48 14838 3013 pos274 pos48
private def ivec126 : Fin 3 → IntField := fun j => blendN 100 tE tF n98 n283 22 12598 j
private def dvec126 : Fin 3 → ℤ := fun _ => 100*22*12598
private def vec126 : Fin 3 → CertField := fun j => scaled (ivec126 j) (dvec126 j)
private theorem dpos126 : ∀ j, (0:ℤ) < dvec126 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos283
private theorem vp126 : productBlend (1/2) (4/5) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = vec126 := by
  rw [cp98, cp283]
  exact t_blend_scaled n98 n283 22 12598 pos98 pos283
private def ivec127 : Fin 3 → IntField := fun j => blendN 100 tE tF n98 n284 22 1 j
private def dvec127 : Fin 3 → ℤ := fun _ => 100*22*1
private def vec127 : Fin 3 → CertField := fun j => scaled (ivec127 j) (dvec127 j)
private theorem dpos127 : ∀ j, (0:ℤ) < dvec127 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos284
private theorem vp127 : productBlend (1/2) (4/5) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨2,-1,0,0⟩ : CertField) = vec127 := by
  rw [cp98, cp284]
  exact t_blend_scaled n98 n284 22 1 pos98 pos284
private def ivec128 : Fin 3 → IntField := fun j => blendN 400 sE sF n109 n6 1006 13 j
private def dvec128 : Fin 3 → ℤ := fun _ => 400*1006*13
private def vec128 : Fin 3 → CertField := fun j => scaled (ivec128 j) (dvec128 j)
private theorem dpos128 : ∀ j, (0:ℤ) < dvec128 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos6
private theorem vp128 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(4/13),(1/13),0,0⟩ : CertField) = vec128 := by
  rw [cp109, cp6]
  exact s_blend_scaled n109 n6 1006 13 pos109 pos6
private def ivec129 : Fin 3 → IntField := fun j => blendN 400 sE sF n109 n35 1006 214 j
private def dvec129 : Fin 3 → ℤ := fun _ => 400*1006*214
private def vec129 : Fin 3 → CertField := fun j => scaled (ivec129 j) (dvec129 j)
private theorem dpos129 : ∀ j, (0:ℤ) < dvec129 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos35
private theorem vp129 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec129 := by
  rw [cp109, cp35]
  exact s_blend_scaled n109 n35 1006 214 pos109 pos35
private def ivec130 : Fin 3 → IntField := fun j => blendN 100 tE tF n58 n283 429 12598 j
private def dvec130 : Fin 3 → ℤ := fun _ => 100*429*12598
private def vec130 : Fin 3 → CertField := fun j => scaled (ivec130 j) (dvec130 j)
private theorem dpos130 : ∀ j, (0:ℤ) < dvec130 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos58) pos283
private theorem vp130 : productBlend (1/2) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = vec130 := by
  rw [cp58, cp283]
  exact t_blend_scaled n58 n283 429 12598 pos58 pos283
private def ivec131 : Fin 3 → IntField := fun j => blendN 400 sE sF n288 n108 313 37 j
private def dvec131 : Fin 3 → ℤ := fun _ => 400*313*37
private def vec131 : Fin 3 → CertField := fun j => scaled (ivec131 j) (dvec131 j)
private theorem dpos131 : ∀ j, (0:ℤ) < dvec131 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos288) pos108
private theorem vp131 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec131 := by
  rw [cp288, cp108]
  exact s_blend_scaled n288 n108 313 37 pos288 pos108
private def ivec132 : Fin 3 → IntField := fun j => blendN 100 tE tF n109 n289 1006 262 j
private def dvec132 : Fin 3 → ℤ := fun _ => 100*1006*262
private def vec132 : Fin 3 → CertField := fun j => scaled (ivec132 j) (dvec132 j)
private theorem dpos132 : ∀ j, (0:ℤ) < dvec132 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos289
private theorem vp132 : productBlend (1/2) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(93/262),(1/262),0,0⟩ : CertField) = vec132 := by
  rw [cp109, cp289]
  exact t_blend_scaled n109 n289 1006 262 pos109 pos289
private def ivec133 : Fin 3 → IntField := fun j => blendN 400 sE sF n291 n108 5893 37 j
private def dvec133 : Fin 3 → ℤ := fun _ => 400*5893*37
private def vec133 : Fin 3 → CertField := fun j => scaled (ivec133 j) (dvec133 j)
private theorem dpos133 : ∀ j, (0:ℤ) < dvec133 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos291) pos108
private theorem vp133 : productBlend (3/4) (4/5) (⟨(1590/5893),(1/5893),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec133 := by
  rw [cp291, cp108]
  exact s_blend_scaled n291 n108 5893 37 pos291 pos108
private def ivec134 : Fin 3 → IntField := fun j => blendN 400 sE sF n293 n294 5530 430 j
private def dvec134 : Fin 3 → ℤ := fun _ => 400*5530*430
private def vec134 : Fin 3 → CertField := fun j => scaled (ivec134 j) (dvec134 j)
private theorem dpos134 : ∀ j, (0:ℤ) < dvec134 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos293) pos294
private theorem vp134 : productBlend (3/4) (4/5) (⟨(213/790),0,0,(1/5530)⟩ : CertField) (⟨(121/430),0,0,(-1/430)⟩ : CertField) = vec134 := by
  rw [cp293, cp294]
  exact s_blend_scaled n293 n294 5530 430 pos293 pos294
private def ivec135 : Fin 3 → IntField := fun j => blendN 100 tE tF n295 n123 5158 510 j
private def dvec135 : Fin 3 → ℤ := fun _ => 100*5158*510
private def vec135 : Fin 3 → CertField := fun j => scaled (ivec135 j) (dvec135 j)
private theorem dpos135 : ∀ j, (0:ℤ) < dvec135 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos295) pos123
private theorem vp135 : productBlend (1/2) (4/5) (⟨(1859/5158),0,0,(1/5158)⟩ : CertField) (⟨(63/170),0,0,(-1/510)⟩ : CertField) = vec135 := by
  rw [cp295, cp123]
  exact t_blend_scaled n295 n123 5158 510 pos295 pos123
private def ivec136 : Fin 3 → IntField := fun j => blendN 100 tE tF n109 n297 1006 5521 j
private def dvec136 : Fin 3 → ℤ := fun _ => 100*1006*5521
private def vec136 : Fin 3 → CertField := fun j => scaled (ivec136 j) (dvec136 j)
private theorem dpos136 : ∀ j, (0:ℤ) < dvec136 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos297
private theorem vp136 : productBlend (1/2) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(1991/5521),(1/5521),0,0⟩ : CertField) = vec136 := by
  rw [cp109, cp297]
  exact t_blend_scaled n109 n297 1006 5521 pos109 pos297
private def ivec137 : Fin 3 → IntField := fun j => blendN 400 sE sF n288 n24 313 478 j
private def dvec137 : Fin 3 → ℤ := fun _ => 400*313*478
private def vec137 : Fin 3 → CertField := fun j => scaled (ivec137 j) (dvec137 j)
private theorem dpos137 : ∀ j, (0:ℤ) < dvec137 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos288) pos24
private theorem vp137 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(133/478),(-1/478),0,0⟩ : CertField) = vec137 := by
  rw [cp288, cp24]
  exact s_blend_scaled n288 n24 313 478 pos288 pos24
private def ivec138 : Fin 3 → IntField := fun j => blendN 100 tE tF n289 n283 262 12598 j
private def dvec138 : Fin 3 → ℤ := fun _ => 100*262*12598
private def vec138 : Fin 3 → CertField := fun j => scaled (ivec138 j) (dvec138 j)
private theorem dpos138 : ∀ j, (0:ℤ) < dvec138 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos289) pos283
private theorem vp138 : productBlend (1/2) (4/5) (⟨(93/262),(1/262),0,0⟩ : CertField) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = vec138 := by
  rw [cp289, cp283]
  exact t_blend_scaled n289 n283 262 12598 pos289 pos283
private def ivec139 : Fin 3 → IntField := fun j => blendN 400 sE sF n301 n294 118 430 j
private def dvec139 : Fin 3 → ℤ := fun _ => 400*118*430
private def vec139 : Fin 3 → CertField := fun j => scaled (ivec139 j) (dvec139 j)
private theorem dpos139 : ∀ j, (0:ℤ) < dvec139 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos301) pos294
private theorem vp139 : productBlend (3/4) (4/5) (⟨(27/118),0,0,(1/118)⟩ : CertField) (⟨(121/430),0,0,(-1/430)⟩ : CertField) = vec139 := by
  rw [cp301, cp294]
  exact s_blend_scaled n301 n294 118 430 pos301 pos294
private def ivec140 : Fin 3 → IntField := fun j => blendN 100 tE tF n283 n304 12598 169 j
private def dvec140 : Fin 3 → ℤ := fun _ => 100*12598*169
private def vec140 : Fin 3 → CertField := fun j => scaled (ivec140 j) (dvec140 j)
private theorem dpos140 : ∀ j, (0:ℤ) < dvec140 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos283) pos304
private theorem vp140 : productBlend (1/2) (4/5) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(61/169),(1/169),0,0⟩ : CertField) = vec140 := by
  rw [cp283, cp304]
  exact t_blend_scaled n283 n304 12598 169 pos283 pos304
private def ivec141 : Fin 3 → IntField := fun j => blendN 100 tE tF n306 n307 2950 222 j
private def dvec141 : Fin 3 → ℤ := fun _ => 100*2950*222
private def vec141 : Fin 3 → CertField := fun j => scaled (ivec141 j) (dvec141 j)
private theorem dpos141 : ∀ j, (0:ℤ) < dvec141 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos306) pos307
private theorem vp141 : productBlend (1/2) (4/5) (⟨(1089/2950),0,0,(1/2950)⟩ : CertField) (⟨(29/74),0,0,(-1/222)⟩ : CertField) = vec141 := by
  rw [cp306, cp307]
  exact t_blend_scaled n306 n307 2950 222 pos306 pos307
private def ivec142 : Fin 3 → IntField := fun j => blendN 100 tE tF n283 n310 12598 3142 j
private def dvec142 : Fin 3 → ℤ := fun _ => 100*12598*3142
private def vec142 : Fin 3 → CertField := fun j => scaled (ivec142 j) (dvec142 j)
private theorem dpos142 : ∀ j, (0:ℤ) < dvec142 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos283) pos310
private theorem vp142 : productBlend (1/2) (4/5) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(1161/3142),(1/3142),0,0⟩ : CertField) = vec142 := by
  rw [cp283, cp310]
  exact t_blend_scaled n283 n310 12598 3142 pos283 pos310
private def ivec143 : Fin 3 → IntField := fun j => blendN 100 tE tF n289 n121 262 537 j
private def dvec143 : Fin 3 → ℤ := fun _ => 100*262*537
private def vec143 : Fin 3 → CertField := fun j => scaled (ivec143 j) (dvec143 j)
private theorem dpos143 : ∀ j, (0:ℤ) < dvec143 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos289) pos121
private theorem vp143 : productBlend (1/2) (4/5) (⟨(93/262),(1/262),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec143 := by
  rw [cp289, cp121]
  exact t_blend_scaled n289 n121 262 537 pos289 pos121
private def ivec144 : Fin 3 → IntField := fun j => blendN 400 sE sF n24 n58 478 429 j
private def dvec144 : Fin 3 → ℤ := fun _ => 400*478*429
private def vec144 : Fin 3 → CertField := fun j => scaled (ivec144 j) (dvec144 j)
private theorem dpos144 : ∀ j, (0:ℤ) < dvec144 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos24) pos58
private theorem vp144 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(42/143),(1/429),0,0⟩ : CertField) = vec144 := by
  rw [cp24, cp58]
  exact s_blend_scaled n24 n58 478 429 pos24 pos58
private def ivec145 : Fin 3 → IntField := fun j => blendN 100 tE tF n314 n315 70 7138 j
private def dvec145 : Fin 3 → ℤ := fun _ => 100*70*7138
private def vec145 : Fin 3 → CertField := fun j => scaled (ivec145 j) (dvec145 j)
private theorem dpos145 : ∀ j, (0:ℤ) < dvec145 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos314) pos315
private theorem vp145 : productBlend (1/2) (4/5) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(2615/7138),0,0,(-1/7138)⟩ : CertField) = vec145 := by
  rw [cp314, cp315]
  exact t_blend_scaled n314 n315 70 7138 pos314 pos315
private def ivec146 : Fin 3 → IntField := fun j => blendN 400 sE sF n26 n58 7081 429 j
private def dvec146 : Fin 3 → ℤ := fun _ => 400*7081*429
private def vec146 : Fin 3 → CertField := fun j => scaled (ivec146 j) (dvec146 j)
private theorem dpos146 : ∀ j, (0:ℤ) < dvec146 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos26) pos58
private theorem vp146 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(42/143),(1/429),0,0⟩ : CertField) = vec146 := by
  rw [cp26, cp58]
  exact s_blend_scaled n26 n58 7081 429 pos26 pos58
private def ivec147 : Fin 3 → IntField := fun j => blendN 100 tE tF n289 n319 262 7501 j
private def dvec147 : Fin 3 → ℤ := fun _ => 100*262*7501
private def vec147 : Fin 3 → CertField := fun j => scaled (ivec147 j) (dvec147 j)
private theorem dpos147 : ∀ j, (0:ℤ) < dvec147 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos289) pos319
private theorem vp147 : productBlend (1/2) (4/5) (⟨(93/262),(1/262),0,0⟩ : CertField) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = vec147 := by
  rw [cp289, cp319]
  exact t_blend_scaled n289 n319 262 7501 pos289 pos319
private def ivec148 : Fin 3 → IntField := fun j => blendN 100 tE tF n314 n307 70 222 j
private def dvec148 : Fin 3 → ℤ := fun _ => 100*70*222
private def vec148 : Fin 3 → CertField := fun j => scaled (ivec148 j) (dvec148 j)
private theorem dpos148 : ∀ j, (0:ℤ) < dvec148 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos314) pos307
private theorem vp148 : productBlend (1/2) (4/5) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(29/74),0,0,(-1/222)⟩ : CertField) = vec148 := by
  rw [cp314, cp307]
  exact t_blend_scaled n314 n307 70 222 pos314 pos307
private def ivec149 : Fin 3 → IntField := fun j => blendN 400 sE sF n24 n62 478 6094 j
private def dvec149 : Fin 3 → ℤ := fun _ => 400*478*6094
private def vec149 : Fin 3 → CertField := fun j => scaled (ivec149 j) (dvec149 j)
private theorem dpos149 : ∀ j, (0:ℤ) < dvec149 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos24) pos62
private theorem vp149 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) = vec149 := by
  rw [cp24, cp62]
  exact s_blend_scaled n24 n62 478 6094 pos24 pos62
private def ivec150 : Fin 3 → IntField := fun j => blendN 400 sE sF n26 n62 7081 6094 j
private def dvec150 : Fin 3 → ℤ := fun _ => 400*7081*6094
private def vec150 : Fin 3 → CertField := fun j => scaled (ivec150 j) (dvec150 j)
private theorem dpos150 : ∀ j, (0:ℤ) < dvec150 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos26) pos62
private theorem vp150 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) = vec150 := by
  rw [cp26, cp62]
  exact s_blend_scaled n26 n62 7081 6094 pos26 pos62
private def ivec151 : Fin 3 → IntField := fun j => blendN 100 tE tF n297 n121 5521 537 j
private def dvec151 : Fin 3 → ℤ := fun _ => 100*5521*537
private def vec151 : Fin 3 → CertField := fun j => scaled (ivec151 j) (dvec151 j)
private theorem dpos151 : ∀ j, (0:ℤ) < dvec151 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos297) pos121
private theorem vp151 : productBlend (1/2) (4/5) (⟨(1991/5521),(1/5521),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec151 := by
  rw [cp297, cp121]
  exact t_blend_scaled n297 n121 5521 537 pos297 pos121
private def ivec152 : Fin 3 → IntField := fun j => blendN 100 tE tF n297 n319 5521 7501 j
private def dvec152 : Fin 3 → ℤ := fun _ => 100*5521*7501
private def vec152 : Fin 3 → CertField := fun j => scaled (ivec152 j) (dvec152 j)
private theorem dpos152 : ∀ j, (0:ℤ) < dvec152 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos297) pos319
private theorem vp152 : productBlend (1/2) (4/5) (⟨(1991/5521),(1/5521),0,0⟩ : CertField) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = vec152 := by
  rw [cp297, cp319]
  exact t_blend_scaled n297 n319 5521 7501 pos297 pos319
private def ivec153 : Fin 3 → IntField := fun j => blendN 400 sE sF n251 n192 2497 10753 j
private def dvec153 : Fin 3 → ℤ := fun _ => 400*2497*10753
private def vec153 : Fin 3 → CertField := fun j => scaled (ivec153 j) (dvec153 j)
private theorem dpos153 : ∀ j, (0:ℤ) < dvec153 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos251) pos192
private theorem vp153 : productBlend (3/4) (4/5) (⟨(731/2497),(-1/2497),0,0⟩ : CertField) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = vec153 := by
  rw [cp251, cp192]
  exact s_blend_scaled n251 n192 2497 10753 pos251 pos192
private def ivec154 : Fin 3 → IntField := fun j => blendN 400 sE sF n59 n192 142 10753 j
private def dvec154 : Fin 3 → ℤ := fun _ => 400*142*10753
private def vec154 : Fin 3 → CertField := fun j => scaled (ivec154 j) (dvec154 j)
private theorem dpos154 : ∀ j, (0:ℤ) < dvec154 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos59) pos192
private theorem vp154 : productBlend (3/4) (4/5) (⟨(43/142),(-1/142),0,0⟩ : CertField) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = vec154 := by
  rw [cp59, cp192]
  exact s_blend_scaled n59 n192 142 10753 pos59 pos192
private def ivec155 : Fin 3 → IntField := fun j => blendN 400 sE sF n62 n193 6094 229 j
private def dvec155 : Fin 3 → ℤ := fun _ => 400*6094*229
private def vec155 : Fin 3 → CertField := fun j => scaled (ivec155 j) (dvec155 j)
private theorem dpos155 : ∀ j, (0:ℤ) < dvec155 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos62) pos193
private theorem vp155 : productBlend (3/4) (4/5) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec155 := by
  rw [cp62, cp193]
  exact s_blend_scaled n62 n193 6094 229 pos62 pos193
private def ivec156 : Fin 3 → IntField := fun j => blendN 100 tE tF n304 n150 169 249 j
private def dvec156 : Fin 3 → ℤ := fun _ => 100*169*249
private def vec156 : Fin 3 → CertField := fun j => scaled (ivec156 j) (dvec156 j)
private theorem dpos156 : ∀ j, (0:ℤ) < dvec156 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos304) pos150
private theorem vp156 : productBlend (1/2) (4/5) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec156 := by
  rw [cp304, cp150]
  exact t_blend_scaled n304 n150 169 249 pos304 pos150
private def ivec157 : Fin 3 → IntField := fun j => blendN 100 tE tF n304 n154 169 3718 j
private def dvec157 : Fin 3 → ℤ := fun _ => 100*169*3718
private def vec157 : Fin 3 → CertField := fun j => scaled (ivec157 j) (dvec157 j)
private theorem dpos157 : ∀ j, (0:ℤ) < dvec157 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos304) pos154
private theorem vp157 : productBlend (1/2) (4/5) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec157 := by
  rw [cp304, cp154]
  exact t_blend_scaled n304 n154 169 3718 pos304 pos154
private def ivec158 : Fin 3 → IntField := fun j => blendN 100 tE tF n310 n150 3142 249 j
private def dvec158 : Fin 3 → ℤ := fun _ => 100*3142*249
private def vec158 : Fin 3 → CertField := fun j => scaled (ivec158 j) (dvec158 j)
private theorem dpos158 : ∀ j, (0:ℤ) < dvec158 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos310) pos150
private theorem vp158 : productBlend (1/2) (4/5) (⟨(1161/3142),(1/3142),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec158 := by
  rw [cp310, cp150]
  exact t_blend_scaled n310 n150 3142 249 pos310 pos150
private def ivec159 : Fin 3 → IntField := fun j => blendN 100 tE tF n310 n154 3142 3718 j
private def dvec159 : Fin 3 → ℤ := fun _ => 100*3142*3718
private def vec159 : Fin 3 → CertField := fun j => scaled (ivec159 j) (dvec159 j)
private theorem dpos159 : ∀ j, (0:ℤ) < dvec159 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos310) pos154
private theorem vp159 : productBlend (1/2) (4/5) (⟨(1161/3142),(1/3142),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec159 := by
  rw [cp310, cp154]
  exact t_blend_scaled n310 n154 3142 3718 pos310 pos154
private def ivec160 : Fin 3 → IntField := fun j => blendN 100 tE tF n121 n141 537 649 j
private def dvec160 : Fin 3 → ℤ := fun _ => 100*537*649
private def vec160 : Fin 3 → CertField := fun j => scaled (ivec160 j) (dvec160 j)
private theorem dpos160 : ∀ j, (0:ℤ) < dvec160 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos121) pos141
private theorem vp160 : productBlend (1/2) (4/5) (⟨(66/179),(-1/537),0,0⟩ : CertField) (⟨(247/649),(1/649),0,0⟩ : CertField) = vec160 := by
  rw [cp121, cp141]
  exact t_blend_scaled n121 n141 537 649 pos121 pos141
private def ivec161 : Fin 3 → IntField := fun j => blendN 100 tE tF n319 n141 7501 649 j
private def dvec161 : Fin 3 → ℤ := fun _ => 100*7501*649
private def vec161 : Fin 3 → CertField := fun j => scaled (ivec161 j) (dvec161 j)
private theorem dpos161 : ∀ j, (0:ℤ) < dvec161 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos319) pos141
private theorem vp161 : productBlend (1/2) (4/5) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) (⟨(247/649),(1/649),0,0⟩ : CertField) = vec161 := by
  rw [cp319, cp141]
  exact t_blend_scaled n319 n141 7501 649 pos319 pos141
private def ivec162 : Fin 3 → IntField := fun j => blendN 400 sE sF n111 n251 2749 2497 j
private def dvec162 : Fin 3 → ℤ := fun _ => 400*2749*2497
private def vec162 : Fin 3 → CertField := fun j => scaled (ivec162 j) (dvec162 j)
private theorem dpos162 : ∀ j, (0:ℤ) < dvec162 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos111) pos251
private theorem vp162 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(731/2497),(-1/2497),0,0⟩ : CertField) = vec162 := by
  rw [cp111, cp251]
  exact s_blend_scaled n111 n251 2749 2497 pos111 pos251
private def ivec163 : Fin 3 → IntField := fun j => blendN 100 tE tF n314 n360 70 670 j
private def dvec163 : Fin 3 → ℤ := fun _ => 100*70*670
private def vec163 : Fin 3 → CertField := fun j => scaled (ivec163 j) (dvec163 j)
private theorem dpos163 : ∀ j, (0:ℤ) < dvec163 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos314) pos360
private theorem vp163 : productBlend (1/2) (4/5) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(251/670),0,0,(-1/670)⟩ : CertField) = vec163 := by
  rw [cp314, cp360]
  exact t_blend_scaled n314 n360 70 670 pos314 pos360
private def ivec164 : Fin 3 → IntField := fun j => blendN 100 tE tF n121 n171 537 9757 j
private def dvec164 : Fin 3 → ℤ := fun _ => 100*537*9757
private def vec164 : Fin 3 → CertField := fun j => scaled (ivec164 j) (dvec164 j)
private theorem dpos164 : ∀ j, (0:ℤ) < dvec164 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos121) pos171
private theorem vp164 : productBlend (1/2) (4/5) (⟨(66/179),(-1/537),0,0⟩ : CertField) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) = vec164 := by
  rw [cp121, cp171]
  exact t_blend_scaled n121 n171 537 9757 pos121 pos171
private def ivec165 : Fin 3 → IntField := fun j => blendN 100 tE tF n319 n171 7501 9757 j
private def dvec165 : Fin 3 → ℤ := fun _ => 100*7501*9757
private def vec165 : Fin 3 → CertField := fun j => scaled (ivec165 j) (dvec165 j)
private theorem dpos165 : ∀ j, (0:ℤ) < dvec165 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos319) pos171
private theorem vp165 : productBlend (1/2) (4/5) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) = vec165 := by
  rw [cp319, cp171]
  exact t_blend_scaled n319 n171 7501 9757 pos319 pos171
private def ivec166 : Fin 3 → IntField := fun j => blendN 100 tE tF n366 n136 19050 202 j
private def dvec166 : Fin 3 → ℤ := fun _ => 100*19050*202
private def vec166 : Fin 3 → CertField := fun j => scaled (ivec166 j) (dvec166 j)
private theorem dpos166 : ∀ j, (0:ℤ) < dvec166 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos366) pos136
private theorem vp166 : productBlend (1/2) (4/5) (⟨(2463/6350),0,0,(1/19050)⟩ : CertField) (⟨(83/202),0,0,(-1/202)⟩ : CertField) = vec166 := by
  rw [cp366, cp136]
  exact t_blend_scaled n366 n136 19050 202 pos366 pos136
private def ivec167 : Fin 3 → IntField := fun j => blendN 100 tE tF n150 n198 249 1429 j
private def dvec167 : Fin 3 → ℤ := fun _ => 100*249*1429
private def vec167 : Fin 3 → CertField := fun j => scaled (ivec167 j) (dvec167 j)
private theorem dpos167 : ∀ j, (0:ℤ) < dvec167 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos150) pos198
private theorem vp167 : productBlend (1/2) (4/5) (⟨(32/83),(-1/249),0,0⟩ : CertField) (⟨(553/1429),(1/1429),0,0⟩ : CertField) = vec167 := by
  rw [cp150, cp198]
  exact t_blend_scaled n150 n198 249 1429 pos150 pos198
private def ivec168 : Fin 3 → IntField := fun j => blendN 100 tE tF n154 n198 3718 1429 j
private def dvec168 : Fin 3 → ℤ := fun _ => 100*3718*1429
private def vec168 : Fin 3 → CertField := fun j => scaled (ivec168 j) (dvec168 j)
private theorem dpos168 : ∀ j, (0:ℤ) < dvec168 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos154) pos198
private theorem vp168 : productBlend (1/2) (4/5) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) (⟨(553/1429),(1/1429),0,0⟩ : CertField) = vec168 := by
  rw [cp154, cp198]
  exact t_blend_scaled n154 n198 3718 1429 pos154 pos198
private def ivec169 : Fin 3 → IntField := fun j => blendN 100 tE tF n181 n136 1770 202 j
private def dvec169 : Fin 3 → ℤ := fun _ => 100*1770*202
private def vec169 : Fin 3 → CertField := fun j => scaled (ivec169 j) (dvec169 j)
private theorem dpos169 : ∀ j, (0:ℤ) < dvec169 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos181) pos136
private theorem vp169 : productBlend (1/2) (4/5) (⟨(227/590),0,0,(1/1770)⟩ : CertField) (⟨(83/202),0,0,(-1/202)⟩ : CertField) = vec169 := by
  rw [cp181, cp136]
  exact t_blend_scaled n181 n136 1770 202 pos181 pos136
private def ivec170 : Fin 3 → IntField := fun j => blendN 100 tE tF n150 n208 249 20022 j
private def dvec170 : Fin 3 → ℤ := fun _ => 100*249*20022
private def vec170 : Fin 3 → CertField := fun j => scaled (ivec170 j) (dvec170 j)
private theorem dpos170 : ∀ j, (0:ℤ) < dvec170 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos150) pos208
private theorem vp170 : productBlend (1/2) (4/5) (⟨(32/83),(-1/249),0,0⟩ : CertField) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) = vec170 := by
  rw [cp150, cp208]
  exact t_blend_scaled n150 n208 249 20022 pos150 pos208
private def ivec171 : Fin 3 → IntField := fun j => blendN 100 tE tF n154 n208 3718 20022 j
private def dvec171 : Fin 3 → ℤ := fun _ => 100*3718*20022
private def vec171 : Fin 3 → CertField := fun j => scaled (ivec171 j) (dvec171 j)
private theorem dpos171 : ∀ j, (0:ℤ) < dvec171 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos154) pos208
private theorem vp171 : productBlend (1/2) (4/5) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) = vec171 := by
  rw [cp154, cp208]
  exact t_blend_scaled n154 n208 3718 20022 pos154 pos208
private def ivec172 : Fin 3 → IntField := fun j => blendN 100 tE tF n171 n145 9757 8353 j
private def dvec172 : Fin 3 → ℤ := fun _ => 100*9757*8353
private def vec172 : Fin 3 → CertField := fun j => scaled (ivec172 j) (dvec172 j)
private theorem dpos172 : ∀ j, (0:ℤ) < dvec172 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos145
private theorem vp172 : productBlend (1/2) (4/5) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = vec172 := by
  rw [cp171, cp145]
  exact t_blend_scaled n171 n145 9757 8353 pos171 pos145
private def ivec173 : Fin 3 → IntField := fun j => blendN 100 tE tF n141 n150 649 249 j
private def dvec173 : Fin 3 → ℤ := fun _ => 100*649*249
private def vec173 : Fin 3 → CertField := fun j => scaled (ivec173 j) (dvec173 j)
private theorem dpos173 : ∀ j, (0:ℤ) < dvec173 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos141) pos150
private theorem vp173 : productBlend (1/2) (4/5) (⟨(247/649),(1/649),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec173 := by
  rw [cp141, cp150]
  exact t_blend_scaled n141 n150 649 249 pos141 pos150
private def ivec174 : Fin 3 → IntField := fun j => blendN 100 tE tF n171 n150 9757 249 j
private def dvec174 : Fin 3 → ℤ := fun _ => 100*9757*249
private def vec174 : Fin 3 → CertField := fun j => scaled (ivec174 j) (dvec174 j)
private theorem dpos174 : ∀ j, (0:ℤ) < dvec174 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos150
private theorem vp174 : productBlend (1/2) (4/5) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec174 := by
  rw [cp171, cp150]
  exact t_blend_scaled n171 n150 9757 249 pos171 pos150
private def ivec175 : Fin 3 → IntField := fun j => blendN 400 sE sF n62 n259 6094 4654 j
private def dvec175 : Fin 3 → ℤ := fun _ => 400*6094*4654
private def vec175 : Fin 3 → CertField := fun j => scaled (ivec175 j) (dvec175 j)
private theorem dpos175 : ∀ j, (0:ℤ) < dvec175 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos62) pos259
private theorem vp175 : productBlend (3/4) (4/5) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = vec175 := by
  rw [cp62, cp259]
  exact s_blend_scaled n62 n259 6094 4654 pos62 pos259
private def ivec176 : Fin 3 → IntField := fun j => blendN 100 tE tF n208 n226 20022 709 j
private def dvec176 : Fin 3 → ℤ := fun _ => 100*20022*709
private def vec176 : Fin 3 → CertField := fun j => scaled (ivec176 j) (dvec176 j)
private theorem dpos176 : ∀ j, (0:ℤ) < dvec176 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos208) pos226
private theorem vp176 : productBlend (1/2) (4/5) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) (⟨(278/709),(-1/709),0,0⟩ : CertField) = vec176 := by
  rw [cp208, cp226]
  exact t_blend_scaled n208 n226 20022 709 pos208 pos226
private def ivec177 : Fin 3 → IntField := fun j => blendN 100 tE tF n142 n225 454 33937 j
private def dvec177 : Fin 3 → ℤ := fun _ => 100*454*33937
private def vec177 : Fin 3 → CertField := fun j => scaled (ivec177 j) (dvec177 j)
private theorem dpos177 : ∀ j, (0:ℤ) < dvec177 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos142) pos225
private theorem vp177 : productBlend (1/2) (4/5) (⟨(177/454),(-1/454),0,0⟩ : CertField) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) = vec177 := by
  rw [cp142, cp225]
  exact t_blend_scaled n142 n225 454 33937 pos142 pos225
private def ivec178 : Fin 3 → IntField := fun j => blendN 100 tE tF n145 n225 8353 33937 j
private def dvec178 : Fin 3 → ℤ := fun _ => 100*8353*33937
private def vec178 : Fin 3 → CertField := fun j => scaled (ivec178 j) (dvec178 j)
private theorem dpos178 : ∀ j, (0:ℤ) < dvec178 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos145) pos225
private theorem vp178 : productBlend (1/2) (4/5) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) = vec178 := by
  rw [cp145, cp225]
  exact t_blend_scaled n145 n225 8353 33937 pos145 pos225
private def ivec179 : Fin 3 → IntField := fun j => blendN 100 tE tF n198 n274 1429 14838 j
private def dvec179 : Fin 3 → ℤ := fun _ => 100*1429*14838
private def vec179 : Fin 3 → CertField := fun j => scaled (ivec179 j) (dvec179 j)
private theorem dpos179 : ∀ j, (0:ℤ) < dvec179 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos198) pos274
private theorem vp179 : productBlend (1/2) (4/5) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) = vec179 := by
  rw [cp198, cp274]
  exact t_blend_scaled n198 n274 1429 14838 pos198 pos274
private def ivec180 : Fin 3 → IntField := fun j => blendN 400 sE sF n109 n23 1006 177 j
private def dvec180 : Fin 3 → ℤ := fun _ => 400*1006*177
private def vec180 : Fin 3 → CertField := fun j => scaled (ivec180 j) (dvec180 j)
private theorem dpos180 : ∀ j, (0:ℤ) < dvec180 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos23
private theorem vp180 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(16/59),(1/177),0,0⟩ : CertField) = vec180 := by
  rw [cp109, cp23]
  exact s_blend_scaled n109 n23 1006 177 pos109 pos23
private def ivec181 : Fin 3 → IntField := fun j => blendN 400 sE sF n301 n425 118 13326 j
private def dvec181 : Fin 3 → ℤ := fun _ => 400*118*13326
private def vec181 : Fin 3 → CertField := fun j => scaled (ivec181 j) (dvec181 j)
private theorem dpos181 : ∀ j, (0:ℤ) < dvec181 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos301) pos425
private theorem vp181 : productBlend (3/4) (4/5) (⟨(27/118),0,0,(1/118)⟩ : CertField) (⟨(1191/4442),0,0,(-1/13326)⟩ : CertField) = vec181 := by
  rw [cp301, cp425]
  exact s_blend_scaled n301 n425 118 13326 pos301 pos425
private def ivec182 : Fin 3 → IntField := fun j => blendN 400 sE sF n426 n23 14001 177 j
private def dvec182 : Fin 3 → ℤ := fun _ => 400*14001*177
private def vec182 : Fin 3 → CertField := fun j => scaled (ivec182 j) (dvec182 j)
private theorem dpos182 : ∀ j, (0:ℤ) < dvec182 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos426) pos23
private theorem vp182 : productBlend (3/4) (4/5) (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) (⟨(16/59),(1/177),0,0⟩ : CertField) = vec182 := by
  rw [cp426, cp23]
  exact s_blend_scaled n426 n23 14001 177 pos426 pos23
private def ivec183 : Fin 3 → IntField := fun j => blendN 400 sE sF n301 n430 118 1266 j
private def dvec183 : Fin 3 → ℤ := fun _ => 400*118*1266
private def vec183 : Fin 3 → CertField := fun j => scaled (ivec183 j) (dvec183 j)
private theorem dpos183 : ∀ j, (0:ℤ) < dvec183 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos301) pos430
private theorem vp183 : productBlend (3/4) (4/5) (⟨(27/118),0,0,(1/118)⟩ : CertField) (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = vec183 := by
  rw [cp301, cp430]
  exact s_blend_scaled n301 n430 118 1266 pos301 pos430
private def ivec184 : Fin 3 → IntField := fun j => blendN 400 sE sF n109 n111 1006 2749 j
private def dvec184 : Fin 3 → ℤ := fun _ => 400*1006*2749
private def vec184 : Fin 3 → CertField := fun j => scaled (ivec184 j) (dvec184 j)
private theorem dpos184 : ∀ j, (0:ℤ) < dvec184 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos109) pos111
private theorem vp184 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(767/2749),(1/2749),0,0⟩ : CertField) = vec184 := by
  rw [cp109, cp111]
  exact s_blend_scaled n109 n111 1006 2749 pos109 pos111
private def ivec185 : Fin 3 → IntField := fun j => blendN 400 sE sF n426 n111 14001 2749 j
private def dvec185 : Fin 3 → ℤ := fun _ => 400*14001*2749
private def vec185 : Fin 3 → CertField := fun j => scaled (ivec185 j) (dvec185 j)
private theorem dpos185 : ∀ j, (0:ℤ) < dvec185 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos426) pos111
private theorem vp185 : productBlend (3/4) (4/5) (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) (⟨(767/2749),(1/2749),0,0⟩ : CertField) = vec185 := by
  rw [cp426, cp111]
  exact s_blend_scaled n426 n111 14001 2749 pos426 pos111
private def ivec186 : Fin 3 → IntField := fun j => blendN 100 tE tF n441 n360 19270 670 j
private def dvec186 : Fin 3 → ℤ := fun _ => 100*19270*670
private def vec186 : Fin 3 → CertField := fun j => scaled (ivec186 j) (dvec186 j)
private theorem dpos186 : ∀ j, (0:ℤ) < dvec186 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos441) pos360
private theorem vp186 : productBlend (1/2) (4/5) (⟨(7081/19270),0,0,(1/19270)⟩ : CertField) (⟨(251/670),0,0,(-1/670)⟩ : CertField) = vec186 := by
  rw [cp441, cp360]
  exact t_blend_scaled n441 n360 19270 670 pos441 pos360
private def ivec187 : Fin 3 → IntField := fun j => blendN 100 tE tF n283 n442 12598 1318 j
private def dvec187 : Fin 3 → ℤ := fun _ => 100*12598*1318
private def vec187 : Fin 3 → CertField := fun j => scaled (ivec187 j) (dvec187 j)
private theorem dpos187 : ∀ j, (0:ℤ) < dvec187 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos283) pos442
private theorem vp187 : productBlend (1/2) (4/5) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(483/1318),(1/1318),0,0⟩ : CertField) = vec187 := by
  rw [cp283, cp442]
  exact t_blend_scaled n283 n442 12598 1318 pos283 pos442
private def ivec188 : Fin 3 → IntField := fun j => blendN 100 tE tF n445 n360 1258 670 j
private def dvec188 : Fin 3 → ℤ := fun _ => 100*1258*670
private def vec188 : Fin 3 → CertField := fun j => scaled (ivec188 j) (dvec188 j)
private theorem dpos188 : ∀ j, (0:ℤ) < dvec188 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos445) pos360
private theorem vp188 : productBlend (1/2) (4/5) (⟨(457/1258),0,0,(1/1258)⟩ : CertField) (⟨(251/670),0,0,(-1/670)⟩ : CertField) = vec188 := by
  rw [cp445, cp360]
  exact t_blend_scaled n445 n360 1258 670 pos445 pos360
private def ivec189 : Fin 3 → IntField := fun j => blendN 400 sE sF n291 n24 5893 478 j
private def dvec189 : Fin 3 → ℤ := fun _ => 400*5893*478
private def vec189 : Fin 3 → CertField := fun j => scaled (ivec189 j) (dvec189 j)
private theorem dpos189 : ∀ j, (0:ℤ) < dvec189 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos291) pos24
private theorem vp189 : productBlend (3/4) (4/5) (⟨(1590/5893),(1/5893),0,0⟩ : CertField) (⟨(133/478),(-1/478),0,0⟩ : CertField) = vec189 := by
  rw [cp291, cp24]
  exact s_blend_scaled n291 n24 5893 478 pos291 pos24
private def ivec190 : Fin 3 → IntField := fun j => blendN 100 tE tF n314 n314 70 70 j
private def dvec190 : Fin 3 → ℤ := fun _ => 100*70*70
private def vec190 : Fin 3 → CertField := fun j => scaled (ivec190 j) (dvec190 j)
private theorem dpos190 : ∀ j, (0:ℤ) < dvec190 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos314) pos314
private theorem vp190 : productBlend (1/2) (4/5) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(3/10),0,0,(1/70)⟩ : CertField) = vec190 := by
  rw [cp314]
  exact t_blend_scaled n314 n314 70 70 pos314 pos314
private def ivec191 : Fin 3 → IntField := fun j => blendN 400 sE sF n294 n294 430 430 j
private def dvec191 : Fin 3 → ℤ := fun _ => 400*430*430
private def vec191 : Fin 3 → CertField := fun j => scaled (ivec191 j) (dvec191 j)
private theorem dpos191 : ∀ j, (0:ℤ) < dvec191 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos294) pos294
private theorem vp191 : productBlend (3/4) (4/5) (⟨(121/430),0,0,(-1/430)⟩ : CertField) (⟨(121/430),0,0,(-1/430)⟩ : CertField) = vec191 := by
  rw [cp294]
  exact s_blend_scaled n294 n294 430 430 pos294 pos294
private def ivec192 : Fin 3 → IntField := fun j => blendN 100 tE tF n283 n449 12598 20353 j
private def dvec192 : Fin 3 → ℤ := fun _ => 100*12598*20353
private def vec192 : Fin 3 → CertField := fun j => scaled (ivec192 j) (dvec192 j)
private theorem dpos192 : ∀ j, (0:ℤ) < dvec192 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos283) pos449
private theorem vp192 : productBlend (1/2) (4/5) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(7480/20353),(1/20353),0,0⟩ : CertField) = vec192 := by
  rw [cp283, cp449]
  exact t_blend_scaled n283 n449 12598 20353 pos283 pos449
private def ivec193 : Fin 3 → IntField := fun j => blendN 100 tE tF n442 n121 1318 537 j
private def dvec193 : Fin 3 → ℤ := fun _ => 100*1318*537
private def vec193 : Fin 3 → CertField := fun j => scaled (ivec193 j) (dvec193 j)
private theorem dpos193 : ∀ j, (0:ℤ) < dvec193 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos442) pos121
private theorem vp193 : productBlend (1/2) (4/5) (⟨(483/1318),(1/1318),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec193 := by
  rw [cp442, cp121]
  exact t_blend_scaled n442 n121 1318 537 pos442 pos121
private def ivec194 : Fin 3 → IntField := fun j => blendN 100 tE tF n449 n121 20353 537 j
private def dvec194 : Fin 3 → ℤ := fun _ => 100*20353*537
private def vec194 : Fin 3 → CertField := fun j => scaled (ivec194 j) (dvec194 j)
private theorem dpos194 : ∀ j, (0:ℤ) < dvec194 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos449) pos121
private theorem vp194 : productBlend (1/2) (4/5) (⟨(7480/20353),(1/20353),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec194 := by
  rw [cp449, cp121]
  exact t_blend_scaled n449 n121 20353 537 pos449 pos121
private def ivec195 : Fin 3 → IntField := fun j => blendN 100 tE tF n304 n121 169 537 j
private def dvec195 : Fin 3 → ℤ := fun _ => 100*169*537
private def vec195 : Fin 3 → CertField := fun j => scaled (ivec195 j) (dvec195 j)
private theorem dpos195 : ∀ j, (0:ℤ) < dvec195 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos304) pos121
private theorem vp195 : productBlend (1/2) (4/5) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec195 := by
  rw [cp304, cp121]
  exact t_blend_scaled n304 n121 169 537 pos304 pos121
private def ivec196 : Fin 3 → IntField := fun j => blendN 400 sE sF n288 n26 313 7081 j
private def dvec196 : Fin 3 → ℤ := fun _ => 400*313*7081
private def vec196 : Fin 3 → CertField := fun j => scaled (ivec196 j) (dvec196 j)
private theorem dpos196 : ∀ j, (0:ℤ) < dvec196 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos288) pos26
private theorem vp196 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) = vec196 := by
  rw [cp288, cp26]
  exact s_blend_scaled n288 n26 313 7081 pos288 pos26
private def ivec197 : Fin 3 → IntField := fun j => blendN 100 tE tF n304 n319 169 7501 j
private def dvec197 : Fin 3 → ℤ := fun _ => 100*169*7501
private def vec197 : Fin 3 → CertField := fun j => scaled (ivec197 j) (dvec197 j)
private theorem dpos197 : ∀ j, (0:ℤ) < dvec197 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos304) pos319
private theorem vp197 : productBlend (1/2) (4/5) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = vec197 := by
  rw [cp304, cp319]
  exact t_blend_scaled n304 n319 169 7501 pos304 pos319
private def ivec198 : Fin 3 → IntField := fun j => blendN 400 sE sF n192 n108 10753 37 j
private def dvec198 : Fin 3 → ℤ := fun _ => 400*10753*37
private def vec198 : Fin 3 → CertField := fun j => scaled (ivec198 j) (dvec198 j)
private theorem dpos198 : ∀ j, (0:ℤ) < dvec198 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos192) pos108
private theorem vp198 : productBlend (3/4) (4/5) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec198 := by
  rw [cp192, cp108]
  exact s_blend_scaled n192 n108 10753 37 pos192 pos108
private def ivec199 : Fin 3 → IntField := fun j => blendN 100 tE tF n225 n108 33937 37 j
private def dvec199 : Fin 3 → ℤ := fun _ => 100*33937*37
private def vec199 : Fin 3 → CertField := fun j => scaled (ivec199 j) (dvec199 j)
private theorem dpos199 : ∀ j, (0:ℤ) < dvec199 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos225) pos108
private theorem vp199 : productBlend (1/2) (4/5) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec199 := by
  rw [cp225, cp108]
  exact t_blend_scaled n225 n108 33937 37 pos225 pos108
private def ivec200 : Fin 3 → IntField := fun j => blendN 100 tE tF n198 n108 1429 37 j
private def dvec200 : Fin 3 → ℤ := fun _ => 100*1429*37
private def vec200 : Fin 3 → CertField := fun j => scaled (ivec200 j) (dvec200 j)
private theorem dpos200 : ∀ j, (0:ℤ) < dvec200 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos198) pos108
private theorem vp200 : productBlend (1/2) (4/5) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec200 := by
  rw [cp198, cp108]
  exact t_blend_scaled n198 n108 1429 37 pos198 pos108
private def ivec201 : Fin 3 → IntField := fun j => blendN 100 tE tF n468 n469 32926 1258 j
private def dvec201 : Fin 3 → ℤ := fun _ => 100*32926*1258
private def vec201 : Fin 3 → CertField := fun j => scaled (ivec201 j) (dvec201 j)
private theorem dpos201 : ∀ j, (0:ℤ) < dvec201 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos468) pos469
private theorem vp201 : productBlend (1/2) (4/5) (⟨(11835/32926),0,0,(1/32926)⟩ : CertField) (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = vec201 := by
  rw [cp468, cp469]
  exact t_blend_scaled n468 n469 32926 1258 pos468 pos469
private def ivec202 : Fin 3 → IntField := fun j => blendN 100 tE tF n471 n472 1858 30226 j
private def dvec202 : Fin 3 → ℤ := fun _ => 100*1858*30226
private def vec202 : Fin 3 → CertField := fun j => scaled (ivec202 j) (dvec202 j)
private theorem dpos202 : ∀ j, (0:ℤ) < dvec202 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos471) pos472
private theorem vp202 : productBlend (1/2) (4/5) (⟨(665/1858),0,0,(1/1858)⟩ : CertField) (⟨(1557/4318),0,0,(-1/30226)⟩ : CertField) = vec202 := by
  rw [cp471, cp472]
  exact t_blend_scaled n471 n472 1858 30226 pos471 pos472
private def ivec203 : Fin 3 → IntField := fun j => blendN 100 tE tF n471 n474 1858 1126 j
private def dvec203 : Fin 3 → ℤ := fun _ => 100*1858*1126
private def vec203 : Fin 3 → CertField := fun j => scaled (ivec203 j) (dvec203 j)
private theorem dpos203 : ∀ j, (0:ℤ) < dvec203 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos471) pos474
private theorem vp203 : productBlend (1/2) (4/5) (⟨(665/1858),0,0,(1/1858)⟩ : CertField) (⟨(411/1126),0,0,(-1/1126)⟩ : CertField) = vec203 := by
  rw [cp471, cp474]
  exact t_blend_scaled n471 n474 1858 1126 pos471 pos474
private def ivec204 : Fin 3 → IntField := fun j => blendN 100 tE tF n476 n469 2026 1258 j
private def dvec204 : Fin 3 → ℤ := fun _ => 100*2026*1258
private def vec204 : Fin 3 → CertField := fun j => scaled (ivec204 j) (dvec204 j)
private theorem dpos204 : ∀ j, (0:ℤ) < dvec204 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos476) pos469
private theorem vp204 : productBlend (1/2) (4/5) (⟨(723/2026),0,0,(1/2026)⟩ : CertField) (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = vec204 := by
  rw [cp476, cp469]
  exact t_blend_scaled n476 n469 2026 1258 pos476 pos469
private def ivec205 : Fin 3 → IntField := fun j => blendN 100 tE tF n479 n480 2221 1846 j
private def dvec205 : Fin 3 → ℤ := fun _ => 100*2221*1846
private def vec205 : Fin 3 → CertField := fun j => scaled (ivec205 j) (dvec205 j)
private theorem dpos205 : ∀ j, (0:ℤ) < dvec205 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos479) pos480
private theorem vp205 : productBlend (1/2) (4/5) (⟨(797/2221),(1/2221),0,0⟩ : CertField) (⟨(667/1846),(-1/1846),0,0⟩ : CertField) = vec205 := by
  rw [cp479, cp480]
  exact t_blend_scaled n479 n480 2221 1846 pos479 pos480
private def ivec206 : Fin 3 → IntField := fun j => blendN 400 sE sF n288 n109 313 1006 j
private def dvec206 : Fin 3 → ℤ := fun _ => 400*313*1006
private def vec206 : Fin 3 → CertField := fun j => scaled (ivec206 j) (dvec206 j)
private theorem dpos206 : ∀ j, (0:ℤ) < dvec206 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos288) pos109
private theorem vp206 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) = vec206 := by
  rw [cp288, cp109]
  exact s_blend_scaled n288 n109 313 1006 pos288 pos109
private def ivec207 : Fin 3 → IntField := fun j => blendN 400 sE sF n288 n426 313 14001 j
private def dvec207 : Fin 3 → ℤ := fun _ => 400*313*14001
private def vec207 : Fin 3 → CertField := fun j => scaled (ivec207 j) (dvec207 j)
private theorem dpos207 : ∀ j, (0:ℤ) < dvec207 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos288) pos426
private theorem vp207 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) = vec207 := by
  rw [cp288, cp426]
  exact s_blend_scaled n288 n426 313 14001 pos288 pos426
private def ivec208 : Fin 3 → IntField := fun j => blendN 100 tE tF n479 n483 2221 32101 j
private def dvec208 : Fin 3 → ℤ := fun _ => 100*2221*32101
private def vec208 : Fin 3 → CertField := fun j => scaled (ivec208 j) (dvec208 j)
private theorem dpos208 : ∀ j, (0:ℤ) < dvec208 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos479) pos483
private theorem vp208 : productBlend (1/2) (4/5) (⟨(797/2221),(1/2221),0,0⟩ : CertField) (⟨(11574/32101),(-1/32101),0,0⟩ : CertField) = vec208 := by
  rw [cp479, cp483]
  exact t_blend_scaled n479 n483 2221 32101 pos479 pos483
private def ivec209 : Fin 3 → IntField := fun j => blendN 100 tE tF n95 n469 10 1258 j
private def dvec209 : Fin 3 → ℤ := fun _ => 100*10*1258
private def vec209 : Fin 3 → CertField := fun j => scaled (ivec209 j) (dvec209 j)
private theorem dpos209 : ∀ j, (0:ℤ) < dvec209 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos95) pos469
private theorem vp209 : productBlend (1/2) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = vec209 := by
  rw [cp95, cp469]
  exact t_blend_scaled n95 n469 10 1258 pos95 pos469
private def ivec210 : Fin 3 → IntField := fun j => blendN 400 sE sF n487 n488 2461 1941 j
private def dvec210 : Fin 3 → ℤ := fun _ => 400*2461*1941
private def vec210 : Fin 3 → CertField := fun j => scaled (ivec210 j) (dvec210 j)
private theorem dpos210 : ∀ j, (0:ℤ) < dvec210 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos487) pos488
private theorem vp210 : productBlend (3/4) (4/5) (⟨(660/2461),(1/2461),0,0⟩ : CertField) (⟨(175/647),(-1/1941),0,0⟩ : CertField) = vec210 := by
  rw [cp487, cp488]
  exact s_blend_scaled n487 n488 2461 1941 pos487 pos488
private def ivec211 : Fin 3 → IntField := fun j => blendN 400 sE sF n490 n491 2098 1090 j
private def dvec211 : Fin 3 → ℤ := fun _ => 400*2098*1090
private def vec211 : Fin 3 → CertField := fun j => scaled (ivec211 j) (dvec211 j)
private theorem dpos211 : ∀ j, (0:ℤ) < dvec211 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos490) pos491
private theorem vp211 : productBlend (3/4) (4/5) (⟨(561/2098),0,0,(1/2098)⟩ : CertField) (⟨(299/1090),0,0,(-1/1090)⟩ : CertField) = vec211 := by
  rw [cp490, cp491]
  exact s_blend_scaled n490 n491 2098 1090 pos490 pos491
private def ivec212 : Fin 3 → IntField := fun j => blendN 400 sE sF n493 n430 36034 1266 j
private def dvec212 : Fin 3 → ℤ := fun _ => 400*36034*1266
private def vec212 : Fin 3 → CertField := fun j => scaled (ivec212 j) (dvec212 j)
private theorem dpos212 : ∀ j, (0:ℤ) < dvec212 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos493) pos430
private theorem vp212 : productBlend (3/4) (4/5) (⟨(9683/36034),0,0,(1/36034)⟩ : CertField) (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = vec212 := by
  rw [cp493, cp430]
  exact s_blend_scaled n493 n430 36034 1266 pos493 pos430
private def ivec213 : Fin 3 → IntField := fun j => blendN 400 sE sF n496 n430 2338 1266 j
private def dvec213 : Fin 3 → ℤ := fun _ => 400*2338*1266
private def vec213 : Fin 3 → CertField := fun j => scaled (ivec213 j) (dvec213 j)
private theorem dpos213 : ∀ j, (0:ℤ) < dvec213 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos496) pos430
private theorem vp213 : productBlend (3/4) (4/5) (⟨(89/334),0,0,(1/2338)⟩ : CertField) (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = vec213 := by
  rw [cp496, cp430]
  exact s_blend_scaled n496 n430 2338 1266 pos496 pos430
private def ivec214 : Fin 3 → IntField := fun j => blendN 100 tE tF n511 n512 1126 17218 j
private def dvec214 : Fin 3 → ℤ := fun _ => 100*1126*17218
private def vec214 : Fin 3 → CertField := fun j => scaled (ivec214 j) (dvec214 j)
private theorem dpos214 : ∀ j, (0:ℤ) < dvec214 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos511) pos512
private theorem vp214 : productBlend (1/2) (4/5) (⟨(411/1126),0,0,(1/1126)⟩ : CertField) (⟨(6361/17218),0,0,(-1/17218)⟩ : CertField) = vec214 := by
  rw [cp511, cp512]
  exact t_blend_scaled n511 n512 1126 17218 pos511 pos512
private def ivec215 : Fin 3 → IntField := fun j => blendN 100 tE tF n511 n515 1126 574 j
private def dvec215 : Fin 3 → ℤ := fun _ => 100*1126*574
private def vec215 : Fin 3 → CertField := fun j => scaled (ivec215 j) (dvec215 j)
private theorem dpos215 : ∀ j, (0:ℤ) < dvec215 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos511) pos515
private theorem vp215 : productBlend (1/2) (4/5) (⟨(411/1126),0,0,(1/1126)⟩ : CertField) (⟨(31/82),0,0,(-1/574)⟩ : CertField) = vec215 := by
  rw [cp511, cp515]
  exact t_blend_scaled n511 n515 1126 574 pos511 pos515
private def ivec216 : Fin 3 → IntField := fun j => blendN 100 tE tF n442 n517 1318 1033 j
private def dvec216 : Fin 3 → ℤ := fun _ => 100*1318*1033
private def vec216 : Fin 3 → CertField := fun j => scaled (ivec216 j) (dvec216 j)
private theorem dpos216 : ∀ j, (0:ℤ) < dvec216 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos442) pos517
private theorem vp216 : productBlend (1/2) (4/5) (⟨(483/1318),(1/1318),0,0⟩ : CertField) (⟨(383/1033),(-1/1033),0,0⟩ : CertField) = vec216 := by
  rw [cp442, cp517]
  exact t_blend_scaled n442 n517 1318 1033 pos442 pos517
private def ivec217 : Fin 3 → IntField := fun j => blendN 100 tE tF n442 n520 1318 18301 j
private def dvec217 : Fin 3 → ℤ := fun _ => 100*1318*18301
private def vec217 : Fin 3 → CertField := fun j => scaled (ivec217 j) (dvec217 j)
private theorem dpos217 : ∀ j, (0:ℤ) < dvec217 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos442) pos520
private theorem vp217 : productBlend (1/2) (4/5) (⟨(483/1318),(1/1318),0,0⟩ : CertField) (⟨(6760/18301),(-1/18301),0,0⟩ : CertField) = vec217 := by
  rw [cp442, cp520]
  exact t_blend_scaled n442 n520 1318 18301 pos442 pos520
private def ivec218 : Fin 3 → IntField := fun j => blendN 100 tE tF n535 n480 34801 1846 j
private def dvec218 : Fin 3 → ℤ := fun _ => 100*34801*1846
private def vec218 : Fin 3 → CertField := fun j => scaled (ivec218 j) (dvec218 j)
private theorem dpos218 : ∀ j, (0:ℤ) < dvec218 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos535) pos480
private theorem vp218 : productBlend (1/2) (4/5) (⟨(12510/34801),(1/34801),0,0⟩ : CertField) (⟨(667/1846),(-1/1846),0,0⟩ : CertField) = vec218 := by
  rw [cp535, cp480]
  exact t_blend_scaled n535 n480 34801 1846 pos535 pos480
private def ivec219 : Fin 3 → IntField := fun j => blendN 400 sE sF n546 n211 25486 1594 j
private def dvec219 : Fin 3 → ℤ := fun _ => 400*25486*1594
private def vec219 : Fin 3 → CertField := fun j => scaled (ivec219 j) (dvec219 j)
private theorem dpos219 : ∀ j, (0:ℤ) < dvec219 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos546) pos211
private theorem vp219 : productBlend (3/4) (4/5) (⟨(7739/25486),0,0,(1/25486)⟩ : CertField) (⟨(489/1594),0,0,(-1/1594)⟩ : CertField) = vec219 := by
  rw [cp546, cp211]
  exact s_blend_scaled n546 n211 25486 1594 pos546 pos211
private def ivec220 : Fin 3 → IntField := fun j => blendN 100 tE tF n449 n517 20353 1033 j
private def dvec220 : Fin 3 → ℤ := fun _ => 100*20353*1033
private def vec220 : Fin 3 → CertField := fun j => scaled (ivec220 j) (dvec220 j)
private theorem dpos220 : ∀ j, (0:ℤ) < dvec220 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos449) pos517
private theorem vp220 : productBlend (1/2) (4/5) (⟨(7480/20353),(1/20353),0,0⟩ : CertField) (⟨(383/1033),(-1/1033),0,0⟩ : CertField) = vec220 := by
  rw [cp449, cp517]
  exact t_blend_scaled n449 n517 20353 1033 pos449 pos517
private def ivec221 : Fin 3 → IntField := fun j => blendN 100 tE tF n562 n563 20418 1510 j
private def dvec221 : Fin 3 → ℤ := fun _ => 100*20418*1510
private def vec221 : Fin 3 → CertField := fun j => scaled (ivec221 j) (dvec221 j)
private theorem dpos221 : ∀ j, (0:ℤ) < dvec221 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos562) pos563
private theorem vp221 : productBlend (1/2) (4/5) (⟨(2587/6806),0,0,(1/20418)⟩ : CertField) (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) = vec221 := by
  rw [cp562, cp563]
  exact t_blend_scaled n562 n563 20418 1510 pos562 pos563
private def ivec222 : Fin 3 → IntField := fun j => blendN 100 tE tF n565 n563 510 1510 j
private def dvec222 : Fin 3 → ℤ := fun _ => 100*510*1510
private def vec222 : Fin 3 → CertField := fun j => scaled (ivec222 j) (dvec222 j)
private theorem dpos222 : ∀ j, (0:ℤ) < dvec222 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos565) pos563
private theorem vp222 : productBlend (1/2) (4/5) (⟨(63/170),0,0,(1/510)⟩ : CertField) (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) = vec222 := by
  rw [cp565, cp563]
  exact t_blend_scaled n565 n563 510 1510 pos565 pos563
private def ivec223 : Fin 3 → IntField := fun j => blendN 100 tE tF n567 n568 1177 1702 j
private def dvec223 : Fin 3 → ℤ := fun _ => 100*1177*1702
private def vec223 : Fin 3 → CertField := fun j => scaled (ivec223 j) (dvec223 j)
private theorem dpos223 : ∀ j, (0:ℤ) < dvec223 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos567) pos568
private theorem vp223 : productBlend (1/2) (4/5) (⟨(446/1177),(1/1177),0,0⟩ : CertField) (⟨(651/1702),(-1/1702),0,0⟩ : CertField) = vec223 := by
  rw [cp567, cp568]
  exact t_blend_scaled n567 n568 1177 1702 pos567 pos568
private def ivec224 : Fin 3 → IntField := fun j => blendN 100 tE tF n567 n571 1177 25521 j
private def dvec224 : Fin 3 → ℤ := fun _ => 100*1177*25521
private def vec224 : Fin 3 → CertField := fun j => scaled (ivec224 j) (dvec224 j)
private theorem dpos224 : ∀ j, (0:ℤ) < dvec224 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos567) pos571
private theorem vp224 : productBlend (1/2) (4/5) (⟨(446/1177),(1/1177),0,0⟩ : CertField) (⟨(3247/8507),(-1/25521),0,0⟩ : CertField) = vec224 := by
  rw [cp567, cp571]
  exact t_blend_scaled n567 n571 1177 25521 pos567 pos571
private def ivec225 : Fin 3 → IntField := fun j => blendN 100 tE tF n580 n188 45778 3010 j
private def dvec225 : Fin 3 → ℤ := fun _ => 100*45778*3010
private def vec225 : Fin 3 → CertField := fun j => scaled (ivec225 j) (dvec225 j)
private theorem dpos225 : ∀ j, (0:ℤ) < dvec225 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos580) pos188
private theorem vp225 : productBlend (1/2) (4/5) (⟨(17703/45778),0,0,(1/45778)⟩ : CertField) (⟨(167/430),0,0,(-1/3010)⟩ : CertField) = vec225 := by
  rw [cp580, cp188]
  exact t_blend_scaled n580 n188 45778 3010 pos580 pos188
private def ivec226 : Fin 3 → IntField := fun j => blendN 100 tE tF n190 n585 2742 54241 j
private def dvec226 : Fin 3 → ℤ := fun _ => 100*2742*54241
private def vec226 : Fin 3 → CertField := fun j => scaled (ivec226 j) (dvec226 j)
private theorem dpos226 : ∀ j, (0:ℤ) < dvec226 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos190) pos585
private theorem vp226 : productBlend (1/2) (4/5) (⟨(353/914),(1/2742),0,0⟩ : CertField) (⟨(21015/54241),(-1/54241),0,0⟩ : CertField) = vec226 := by
  rw [cp190, cp585]
  exact t_blend_scaled n190 n585 2742 54241 pos190 pos585
private def ivec227 : Fin 3 → IntField := fun j => blendN 100 tE tF n138 n594 670 24198 j
private def dvec227 : Fin 3 → ℤ := fun _ => 100*670*24198
private def vec227 : Fin 3 → CertField := fun j => scaled (ivec227 j) (dvec227 j)
private theorem dpos227 : ∀ j, (0:ℤ) < dvec227 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos138) pos594
private theorem vp227 : productBlend (1/2) (4/5) (⟨(251/670),0,0,(1/670)⟩ : CertField) (⟨(3079/8066),0,0,(-1/24198)⟩ : CertField) = vec227 := by
  rw [cp138, cp594]
  exact t_blend_scaled n138 n594 670 24198 pos138 pos594
private def ivec228 : Fin 3 → IntField := fun j => blendN 100 tE tF n138 n596 670 1770 j
private def dvec228 : Fin 3 → ℤ := fun _ => 100*670*1770
private def vec228 : Fin 3 → CertField := fun j => scaled (ivec228 j) (dvec228 j)
private theorem dpos228 : ∀ j, (0:ℤ) < dvec228 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos138) pos596
private theorem vp228 : productBlend (1/2) (4/5) (⟨(251/670),0,0,(1/670)⟩ : CertField) (⟨(227/590),0,0,(-1/1770)⟩ : CertField) = vec228 := by
  rw [cp138, cp596]
  exact t_blend_scaled n138 n596 670 1770 pos138 pos596
private def ivec229 : Fin 3 → IntField := fun j => blendN 100 tE tF n602 n568 21741 1702 j
private def dvec229 : Fin 3 → ℤ := fun _ => 100*21741*1702
private def vec229 : Fin 3 → CertField := fun j => scaled (ivec229 j) (dvec229 j)
private theorem dpos229 : ∀ j, (0:ℤ) < dvec229 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos602) pos568
private theorem vp229 : productBlend (1/2) (4/5) (⟨(2755/7247),(1/21741),0,0⟩ : CertField) (⟨(651/1702),(-1/1702),0,0⟩ : CertField) = vec229 := by
  rw [cp602, cp568]
  exact t_blend_scaled n602 n568 21741 1702 pos602 pos568
private def ivec230 : Fin 3 → IntField := fun j => blendN 100 tE tF n630 n191 48661 3517 j
private def dvec230 : Fin 3 → ℤ := fun _ => 100*48661*3517
private def vec230 : Fin 3 → CertField := fun j => scaled (ivec230 j) (dvec230 j)
private theorem dpos230 : ∀ j, (0:ℤ) < dvec230 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos630) pos191
private theorem vp230 : productBlend (1/2) (4/5) (⟨(18819/48661),(1/48661),0,0⟩ : CertField) (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) = vec230 := by
  rw [cp630, cp191]
  exact t_blend_scaled n630 n191 48661 3517 pos630 pos191
private def ivec231 : Fin 3 → IntField := fun j => blendN 100 tE tF n646 n222 86281 5982 j
private def dvec231 : Fin 3 → ℤ := fun _ => 100*86281*5982
private def vec231 : Fin 3 → CertField := fun j => scaled (ivec231 j) (dvec231 j)
private theorem dpos231 : ∀ j, (0:ℤ) < dvec231 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos646) pos222
private theorem vp231 : productBlend (1/2) (4/5) (⟨(33653/86281),(1/86281),0,0⟩ : CertField) (⟨(779/1994),(-1/5982),0,0⟩ : CertField) = vec231 := by
  rw [cp646, cp222]
  exact t_blend_scaled n646 n222 86281 5982 pos646 pos222
private def ivec232 : Fin 3 → IntField := fun j => blendN 400 sE sF n487 n662 2461 34318 j
private def dvec232 : Fin 3 → ℤ := fun _ => 400*2461*34318
private def vec232 : Fin 3 → CertField := fun j => scaled (ivec232 j) (dvec232 j)
private theorem dpos232 : ∀ j, (0:ℤ) < dvec232 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos487) pos662
private theorem vp232 : productBlend (3/4) (4/5) (⟨(660/2461),(1/2461),0,0⟩ : CertField) (⟨(9257/34318),(-1/34318),0,0⟩ : CertField) = vec232 := by
  rw [cp487, cp662]
  exact s_blend_scaled n487 n662 2461 34318 pos487 pos662
private def ivec233 : Fin 3 → IntField := fun j => blendN 100 tE tF n669 n670 41226 3178 j
private def dvec233 : Fin 3 → ℤ := fun _ => 100*41226*3178
private def vec233 : Fin 3 → CertField := fun j => scaled (ivec233 j) (dvec233 j)
private theorem dpos233 : ∀ j, (0:ℤ) < dvec233 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos669) pos670
private theorem vp233 : productBlend (1/2) (4/5) (⟨(5033/13742),0,0,(1/41226)⟩ : CertField) (⟨(167/454),0,0,(-1/3178)⟩ : CertField) = vec233 := by
  rw [cp669, cp670]
  exact t_blend_scaled n669 n670 41226 3178 pos669 pos670
private def ivec234 : Fin 3 → IntField := fun j => blendN 100 tE tF n672 n670 906 3178 j
private def dvec234 : Fin 3 → ℤ := fun _ => 100*906*3178
private def vec234 : Fin 3 → CertField := fun j => scaled (ivec234 j) (dvec234 j)
private theorem dpos234 : ∀ j, (0:ℤ) < dvec234 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos672) pos670
private theorem vp234 : productBlend (1/2) (4/5) (⟨(109/302),0,0,(1/906)⟩ : CertField) (⟨(167/454),0,0,(-1/3178)⟩ : CertField) = vec234 := by
  rw [cp672, cp670]
  exact t_blend_scaled n672 n670 906 3178 pos672 pos670
private def ivec235 : Fin 3 → IntField := fun j => blendN 100 tE tF n674 n675 2341 3541 j
private def dvec235 : Fin 3 → ℤ := fun _ => 100*2341*3541
private def vec235 : Fin 3 → CertField := fun j => scaled (ivec235 j) (dvec235 j)
private theorem dpos235 : ∀ j, (0:ℤ) < dvec235 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos674) pos675
private theorem vp235 : productBlend (1/2) (4/5) (⟨(856/2341),(1/2341),0,0⟩ : CertField) (⟨(1301/3541),(-1/3541),0,0⟩ : CertField) = vec235 := by
  rw [cp674, cp675]
  exact t_blend_scaled n674 n675 2341 3541 pos674 pos675
private def ivec236 : Fin 3 → IntField := fun j => blendN 100 tE tF n674 n678 2341 52566 j
private def dvec236 : Fin 3 → ℤ := fun _ => 100*2341*52566
private def vec236 : Fin 3 → CertField := fun j => scaled (ivec236 j) (dvec236 j)
private theorem dpos236 : ∀ j, (0:ℤ) < dvec236 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos674) pos678
private theorem vp236 : productBlend (1/2) (4/5) (⟨(856/2341),(1/2341),0,0⟩ : CertField) (⟨(6431/17522),(-1/52566),0,0⟩ : CertField) = vec236 := by
  rw [cp674, cp678]
  exact t_blend_scaled n674 n678 2341 52566 pos674 pos678
private def ivec237 : Fin 3 → IntField := fun j => blendN 100 tE tF n445 n680 1258 49866 j
private def dvec237 : Fin 3 → ℤ := fun _ => 100*1258*49866
private def vec237 : Fin 3 → CertField := fun j => scaled (ivec237 j) (dvec237 j)
private theorem dpos237 : ∀ j, (0:ℤ) < dvec237 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos445) pos680
private theorem vp237 : productBlend (1/2) (4/5) (⟨(457/1258),0,0,(1/1258)⟩ : CertField) (⟨(6101/16622),0,0,(-1/49866)⟩ : CertField) = vec237 := by
  rw [cp445, cp680]
  exact t_blend_scaled n445 n680 1258 49866 pos445 pos680
private def ivec238 : Fin 3 → IntField := fun j => blendN 400 sE sF n490 n684 2098 32290 j
private def dvec238 : Fin 3 → ℤ := fun _ => 400*2098*32290
private def vec238 : Fin 3 → CertField := fun j => scaled (ivec238 j) (dvec238 j)
private theorem dpos238 : ∀ j, (0:ℤ) < dvec238 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos490) pos684
private theorem vp238 : productBlend (3/4) (4/5) (⟨(561/2098),0,0,(1/2098)⟩ : CertField) (⟨(8711/32290),0,0,(-1/32290)⟩ : CertField) = vec238 := by
  rw [cp490, cp684]
  exact s_blend_scaled n490 n684 2098 32290 pos490 pos684
private def ivec239 : Fin 3 → IntField := fun j => blendN 400 sE sF n688 n488 38062 1941 j
private def dvec239 : Fin 3 → ℤ := fun _ => 400*38062*1941
private def vec239 : Fin 3 → CertField := fun j => scaled (ivec239 j) (dvec239 j)
private theorem dpos239 : ∀ j, (0:ℤ) < dvec239 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos688) pos488
private theorem vp239 : productBlend (3/4) (4/5) (⟨(10229/38062),(1/38062),0,0⟩ : CertField) (⟨(175/647),(-1/1941),0,0⟩ : CertField) = vec239 := by
  rw [cp688, cp488]
  exact s_blend_scaled n688 n488 38062 1941 pos688 pos488
private def ivec240 : Fin 3 → IntField := fun j => blendN 100 tE tF n129 n129 9250 9250 j
private def dvec240 : Fin 3 → ℤ := fun _ => 100*9250*9250
private def vec240 : Fin 3 → CertField := fun j => scaled (ivec240 j) (dvec240 j)
private theorem dpos240 : ∀ j, (0:ℤ) < dvec240 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos129) pos129
private theorem vp240 : productBlend (1/2) (4/5) (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) = vec240 := by
  rw [cp129]
  exact t_blend_scaled n129 n129 9250 9250 pos129 pos129
private def ivec241 : Fin 3 → IntField := fun j => blendN 400 sE sF n10 n10 94 94 j
private def dvec241 : Fin 3 → ℤ := fun _ => 400*94*94
private def vec241 : Fin 3 → CertField := fun j => scaled (ivec241 j) (dvec241 j)
private theorem dpos241 : ∀ j, (0:ℤ) < dvec241 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos10) pos10
private theorem vp241 : productBlend (3/4) (4/5) (⟨(31/94),0,0,(-1/94)⟩ : CertField) (⟨(31/94),0,0,(-1/94)⟩ : CertField) = vec241 := by
  rw [cp10]
  exact s_blend_scaled n10 n10 94 94 pos10 pos10

private def eb1 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def eb2 : CertBound := ⟨true,false,⟨⟨(1703/253),(-884/253),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/11),(-1/11),0,0⟩,⟨(3/13),(1/39),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩

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

private def eb110 : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

private def eb114 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

private def eb115 : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

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

private def eb144 : CertBound := ⟨true,true,⟨⟨(360273/1694452),(736243/1694452),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩

private def eb145 : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩

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

private def eb170 : CertBound := ⟨true,false,⟨⟨(64145/160843),0,0,(311040/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb171 : CertBound := ⟨false,false,⟨⟨(-601572/1915199),(3511661/7660796),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb172 : CertBound := ⟨true,true,⟨⟨(628621/804215),0,0,(62208/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb173 : CertBound := ⟨true,true,⟨⟨(3553/4141),0,0,(108/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb174 : CertBound := ⟨false,false,⟨⟨(187203/5421097),(1481141/5421097),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb183 : CertBound := ⟨false,false,⟨⟨(1355921/3029375),0,0,(-33236/3029375)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb186 : CertBound := ⟨true,true,⟨⟨(9833/12314),0,0,(-171/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb187 : CertBound := ⟨true,true,⟨⟨(187/94),0,0,(-31/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb188 : CertBound := ⟨true,false,⟨⟨(184867/101426),(1145809/304278),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb193 : CertBound := ⟨true,false,⟨⟨(-297343/612457),(2732382/612457),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(1493/5354),(-1/16062),0,0⟩⟩⟩

private def eb194 : CertBound := ⟨true,false,⟨⟨(3216375/580027),0,0,(-294950/580027)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩

private def eb195 : CertBound := ⟨true,true,⟨⟨(25971/6157),0,0,(-34/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩

private def eb196 : CertBound := ⟨true,true,⟨⟨(900585/82861),0,0,(-82586/82861)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩

private def eb197 : CertBound := ⟨true,false,⟨⟨(2514041/1135849),(3575763/1135849),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb199 : CertBound := ⟨true,true,⟨⟨(991/94),0,0,(57/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩

private def eb203 : CertBound := ⟨true,false,⟨⟨(85625/9478),0,0,(565/9478)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb207 : CertBound := ⟨true,true,⟨⟨(23975/1354),0,0,(791/6770)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb208 : CertBound := ⟨true,true,⟨⟨(1207/94),0,0,(33/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(115/422),0,0,(1/1266)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb214 : CertBound := ⟨false,true,⟨⟨(225375/1125901),0,0,(20000/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb215 : CertBound := ⟨false,false,⟨⟨(-16887/147323),(43160/147323),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb216 : CertBound := ⟨false,false,⟨⟨(33/101),0,0,(-4/707)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb217 : CertBound := ⟨false,false,⟨⟨(8727/12314),0,0,(-143/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb218 : CertBound := ⟨false,true,⟨⟨(566107/1696450),0,0,(39413/1696450)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb223 : CertBound := ⟨false,false,⟨⟨(63105/160843),0,0,(800/160843)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb226 : CertBound := ⟨false,false,⟨⟨(-73993/348218),(64543/174109),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb229 : CertBound := ⟨true,true,⟨⟨(3962749/6058750),0,0,(275891/6058750)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb230 : CertBound := ⟨true,true,⟨⟨(8727/12314),0,0,(-143/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb231 : CertBound := ⟨false,false,⟨⟨(5976/2214839),(566539/2214839),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb235 : CertBound := ⟨true,true,⟨⟨(83/47),0,0,(-4/329)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb236 : CertBound := ⟨true,false,⟨⟨(81657/50713),(512554/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb241 : CertBound := ⟨true,false,⟨⟨(138122/612457),(6708677/1837371),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩⟩⟩

private def eb242 : CertBound := ⟨true,false,⟨⟨(583805/165722),0,0,(-89725/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

private def eb243 : CertBound := ⟨true,true,⟨⟨(319/94),0,0,(395/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb244 : CertBound := ⟨true,true,⟨⟨(5721289/828610),0,0,(-25123/165722)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

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

private def eb348 : CertBound := ⟨true,false,⟨⟨(922125/1160054),0,0,(-75625/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb349 : CertBound := ⟨true,true,⟨⟨(258195/165722),0,0,(-21175/165722)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb350 : CertBound := ⟨true,true,⟨⟨(376986/1135849),(542948/1135849),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb355 : CertBound := ⟨true,true,⟨⟨(671227/1541891),(499219/1541891),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb356 : CertBound := ⟨true,true,⟨⟨(6116773/18621299),(5788260/18621299),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb357 : CertBound := ⟨true,true,⟨⟨(17121447/34534643),(7927814/34534643),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

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

private def eb394 : CertBound := ⟨false,false,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def eb395 : CertBound := ⟨false,false,⟨⟨(153/250),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(35/94),(1/94),0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(5/22),(1/22),0,0⟩⟩⟩

private def eb396 : CertBound := ⟨false,true,⟨⟨(-4735814/5058097),(10860688/15174291),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩

private def eb397 : CertBound := ⟨false,true,⟨⟨(7469552/7968235),(-2765481/7968235),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩

private def eb398 : CertBound := ⟨false,true,⟨⟨(-35971057/197265783),(20250238/65755261),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩

private def eb399 : CertBound := ⟨true,true,⟨⟨(677899/922502),(177747/922502),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩

private def eb402 : CertBound := ⟨true,true,⟨⟨(11490431/15484855),(1712455/9290913),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩

private def eb403 : CertBound := ⟨true,false,⟨⟨(59835/87686),0,0,(26785/1841406)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb404 : CertBound := ⟨true,true,⟨⟨(586383/438430),0,0,(37499/1315290)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb405 : CertBound := ⟨true,true,⟨⟨(873/170),0,0,(-451/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb406 : CertBound := ⟨true,true,⟨⟨(59273105/77757764),(1918001/11108252),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩

private def eb408 : CertBound := ⟨true,true,⟨⟨(1586290/10727197),(3840344/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb411 : CertBound := ⟨true,true,⟨⟨(615684/1064531),(448863/1064531),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb412 : CertBound := ⟨false,false,⟨⟨(241/85),0,0,(-44/85)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb414 : CertBound := ⟨false,true,⟨⟨(70237/152810),0,0,(2057/65490)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb415 : CertBound := ⟨true,true,⟨⟨(241/85),0,0,(-44/85)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb416 : CertBound := ⟨true,true,⟨⟨(77513961/167131367),(66212564/167131367),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb419 : CertBound := ⟨true,true,⟨⟨(373/370),0,0,(-187/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb420 : CertBound := ⟨true,true,⟨⟨(88747320/128644477),(37227830/128644477),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb422 : CertBound := ⟨false,true,⟨⟨(1384994/867613),(-714779/867613),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb424 : CertBound := ⟨true,false,⟨⟨(101/86),0,0,(-451/4214)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb425 : CertBound := ⟨false,true,⟨⟨(20949305/22604836),(-9833499/22604836),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb426 : CertBound := ⟨true,true,⟨⟨(4949/2150),0,0,(-451/2150)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb427 : CertBound := ⟨false,true,⟨⟨(3510339/2796719),(-1718470/2796719),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb431 : CertBound := ⟨true,false,⟨⟨(263083/613802),0,0,(121589/1841406)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb432 : CertBound := ⟨false,true,⟨⟨(10052507/11302418),(-14005655/33907254),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb433 : CertBound := ⟨false,true,⟨⟨(303972265/465908181),(-127591766/465908181),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb434 : CertBound := ⟨false,true,⟨⟨(338003377/473628142),(-141533453/473628142),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb435 : CertBound := ⟨true,true,⟨⟨(1841581/2192150),0,0,(851123/6576450)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb436 : CertBound := ⟨true,true,⟨⟨(701/170),0,0,(-329/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb437 : CertBound := ⟨false,true,⟨⟨(30853093/36565583),(-13656585/36565583),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb439 : CertBound := ⟨false,true,⟨⟨(122644153/238170419),(-86222743/476340838),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb440 : CertBound := ⟨false,true,⟨⟨(59241606/117867829),(-19341618/117867829),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb441 : CertBound := ⟨true,true,⟨⟨(1385355/10727197),(3126197/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb443 : CertBound := ⟨true,true,⟨⟨(341/170),0,0,(-43/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb446 : CertBound := ⟨false,true,⟨⟨(42225/49966),0,0,(-45425/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb447 : CertBound := ⟨false,false,⟨⟨(381/670),0,0,(-253/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb449 : CertBound := ⟨false,true,⟨⟨(-5855080/5135331),(4134061/5135331),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb450 : CertBound := ⟨false,true,⟨⟨(2377493/2157308),(-3837982/8089905),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb452 : CertBound := ⟨true,true,⟨⟨(11823/7138),0,0,(-1817/7138)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb454 : CertBound := ⟨false,true,⟨⟨(-59465899/71732063),(138588056/215196189),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb455 : CertBound := ⟨false,false,⟨⟨(11823/7138),0,0,(-1817/7138)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb456 : CertBound := ⟨true,true,⟨⟨(331/370),0,0,(-53/2590)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb457 : CertBound := ⟨true,true,⟨⟨(194397/163774),(139809/163774),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb460 : CertBound := ⟨true,true,⟨⟨(164975997/167131367),(132610256/167131367),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb461 : CertBound := ⟨true,false,⟨⟨(60857/76405),0,0,(25714/229215)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb462 : CertBound := ⟨true,true,⟨⟨(425999/272875),0,0,(179998/818625)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb463 : CertBound := ⟨true,true,⟨⟨(311/185),0,0,(286/3885)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb464 : CertBound := ⟨true,true,⟨⟨(179334165/128644477),(76652585/128644477),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb466 : CertBound := ⟨false,true,⟨⟨(113317/39923),(-58057/39923),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb468 : CertBound := ⟨false,true,⟨⟨(429625/260039),(-397911/520078),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb469 : CertBound := ⟨true,true,⟨⟨(22927/12314),0,0,(121/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb470 : CertBound := ⟨false,true,⟨⟨(143862/68783),(-68665/68783),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb471 : CertBound := ⟨false,true,⟨⟨(5361524/3380507),(-7364405/10141521),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb472 : CertBound := ⟨false,true,⟨⟨(325056155/278702463),(-133599949/278702463),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb473 : CertBound := ⟨false,true,⟨⟨(1075417/896038),(-428303/896038),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb474 : CertBound := ⟨false,true,⟨⟨(8166794/4824541),(-3688227/4824541),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb475 : CertBound := ⟨false,true,⟨⟨(129082073/125698852),(-47154571/125698852),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb476 : CertBound := ⟨false,true,⟨⟨(102212817/108058093),(-33339399/108058093),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb477 : CertBound := ⟨true,true,⟨⟨(1474639/1510223),(754191/1510223),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb478 : CertBound := ⟨true,true,⟨⟨(16314613/18238847),(7455368/18238847),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb479 : CertBound := ⟨true,true,⟨⟨(4877310/4868149),(2214722/4868149),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb480 : CertBound := ⟨true,true,⟨⟨(16243773/18238847),(22981565/54716541),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb481 : CertBound := ⟨true,true,⟨⟨(34072259/37290891),(22261037/74581782),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb482 : CertBound := ⟨true,true,⟨⟨(720674542/764299393),(277946054/764299393),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb483 : CertBound := ⟨true,true,⟨⟨(22700866/22704539),(10519166/22704539),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb484 : CertBound := ⟨true,true,⟨⟨(260311300/274200971),(98013814/274200971),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb485 : CertBound := ⟨true,true,⟨⟨(75037587/73187257),(30655035/73187257),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb486 : CertBound := ⟨false,true,⟨⟨(190017/897890),0,0,(-65341/2693670)⟩,⟨(2463/6350),0,0,(1/19050)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb487 : CertBound := ⟨false,false,⟨⟨(13651/59590),0,0,(-3667/178770)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb488 : CertBound := ⟨true,true,⟨⟨(6440201/18621299),(17076737/55863897),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb490 : CertBound := ⟨true,true,⟨⟨(6232877/38072847),(8942231/25381898),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb491 : CertBound := ⟨true,true,⟨⟨(193668946/417072227),(77221239/417072227),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb494 : CertBound := ⟨true,true,⟨⟨(22564/50713),(15573/50713),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb495 : CertBound := ⟨false,false,⟨⟨(1330119/3206750),0,0,(-457387/9620250)⟩,⟨(2463/6350),0,0,(1/19050)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb496 : CertBound := ⟨true,true,⟨⟨(30639607/86968894),(24993995/86968894),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb497 : CertBound := ⟨true,true,⟨⟨(574040/1135849),(241790/1135849),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb498 : CertBound := ⟨false,true,⟨⟨(530634/495541),(-271739/495541),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb499 : CertBound := ⟨false,true,⟨⟨(8048625/12910852),(-3724019/12910852),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb500 : CertBound := ⟨false,true,⟨⟨(11762541/18234599),(-5322545/18234599),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb501 : CertBound := ⟨false,true,⟨⟨(3863267/6455426),(-1767205/6455426),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb502 : CertBound := ⟨false,true,⟨⟨(39042915/88701839),(-48075646/266105517),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb503 : CertBound := ⟨false,true,⟨⟨(44781028/118771307),(-16029627/118771307),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩

private def eb504 : CertBound := ⟨false,true,⟨⟨(5839677/7449913),(-2780866/7449913),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb505 : CertBound := ⟨false,true,⟨⟨(90786309/194100436),(-36671293/194100436),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb506 : CertBound := ⟨false,true,⟨⟨(98170698/274137107),(-32019006/274137107),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩

private def eb507 : CertBound := ⟨true,true,⟨⟨(14759/63661),(27704/63661),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb510 : CertBound := ⟨true,false,⟨⟨(157065/82861),0,0,(-119990/580027)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb512 : CertBound := ⟨true,true,⟨⟨(1539237/414305),0,0,(-167986/414305)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb513 : CertBound := ⟨true,true,⟨⟨(5115/6157),0,0,(494/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb516 : CertBound := ⟨true,true,⟨⟨(69253/768829),(1042741/2306487),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb519 : CertBound := ⟨true,true,⟨⟨(262658/957073),(348954/957073),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb522 : CertBound := ⟨false,true,⟨⟨(-8132320/10754579),(17468351/32263737),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb523 : CertBound := ⟨false,true,⟨⟨(10070839/13553716),(-5308804/16942145),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb524 : CertBound := ⟨false,true,⟨⟨(-149448477/395740081),(402336023/1187220243),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb525 : CertBound := ⟨true,true,⟨⟨(1378579/1541891),(1010248/1541891),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb526 : CertBound := ⟨false,true,⟨⟨(113787/448945),0,0,(-10376/1346835)⟩,⟨(2463/6350),0,0,(1/19050)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb527 : CertBound := ⟨true,true,⟨⟨(11910457/18621299),(11928891/18621299),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩

private def eb528 : CertBound := ⟨true,true,⟨⟨(69347763/69069286),(32526001/69069286),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb529 : CertBound := ⟨true,true,⟨⟨(13758617/18621299),(34140713/55863897),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb531 : CertBound := ⟨true,true,⟨⟨(12705500/38072847),(9090187/12690949),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩

private def eb532 : CertBound := ⟨true,true,⟨⟨(388324822/417072227),(163972491/417072227),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb534 : CertBound := ⟨true,true,⟨⟨(6563101/7201246),(4482897/7201246),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb535 : CertBound := ⟨false,false,⟨⟨(796509/1603375),0,0,(-72632/4810125)⟩,⟨(2463/6350),0,0,(1/19050)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb536 : CertBound := ⟨true,true,⟨⟨(30213209/43484447),(25619932/43484447),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩

private def eb537 : CertBound := ⟨true,true,⟨⟨(82365655/80645279),(35341555/80645279),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb538 : CertBound := ⟨false,true,⟨⟨(2177375/21903658),0,0,(11875/3129094)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb539 : CertBound := ⟨false,false,⟨⟨(967/1354),0,0,(-1121/9478)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb540 : CertBound := ⟨false,true,⟨⟨(-784719/11144771),(1774045/11144771),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb545 : CertBound := ⟨false,false,⟨⟨(609665/3129094),0,0,(23275/3129094)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb547 : CertBound := ⟨false,true,⟨⟨(-3305591/26342186),(5323257/26342186),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb550 : CertBound := ⟨false,true,⟨⟨(-6088/366553),(52493/366553),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb553 : CertBound := ⟨true,true,⟨⟨(89059389/200296174),(63877233/200296174),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb554 : CertBound := ⟨true,true,⟨⟨(392627001/1209480743),(373531548/1209480743),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩

private def eb555 : CertBound := ⟨true,true,⟨⟨(1920033810/3685184893),(820805110/3685184893),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb556 : CertBound := ⟨false,true,⟨⟨(-31345815/73960753),(66451517/221882259),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb557 : CertBound := ⟨false,true,⟨⟨(38221813/93210812),(-82168347/466054060),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb558 : CertBound := ⟨false,true,⟨⟨(-138472771/773927823),(129224168/773927823),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩

private def eb559 : CertBound := ⟨false,true,⟨⟨(669/1406),0,0,(109/29526)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb560 : CertBound := ⟨false,true,⟨⟨(-576131/539327),(424264/539327),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def eb564 : CertBound := ⟨true,true,⟨⟨(367/335),0,0,(-176/2345)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb567 : CertBound := ⟨true,false,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩

private def eb568 : CertBound := ⟨false,true,⟨⟨(-5445979/3423554),(3737807/3423554),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def eb569 : CertBound := ⟨true,true,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩

private def eb570 : CertBound := ⟨true,true,⟨⟨(1197/670),0,0,(83/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb571 : CertBound := ⟨false,true,⟨⟨(-17325864/22600513),(14330533/22600513),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def eb573 : CertBound := ⟨false,true,⟨⟨(10086040/5651209),(-14268851/16953627),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def eb575 : CertBound := ⟨false,true,⟨⟨(2854249/2157308),(-3078379/5393270),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def eb576 : CertBound := ⟨false,true,⟨⟨(338188789/236814071),(-144869352/236814071),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def eb577 : CertBound := ⟨true,true,⟨⟨(1026067/2192150),0,0,(275471/6576450)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb578 : CertBound := ⟨true,true,⟨⟨(109/34),0,0,(-299/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb579 : CertBound := ⟨false,true,⟨⟨(-9733651/22729957),(10108657/22729957),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def eb581 : CertBound := ⟨false,true,⟨⟨(-49334341/72142907),(43021876/72142907),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def eb582 : CertBound := ⟨false,true,⟨⟨(-120589494/952499483),(278276430/952499483),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def eb583 : CertBound := ⟨true,true,⟨⟨(71202757/53963533),(32270063/53963533),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb584 : CertBound := ⟨false,true,⟨⟨(84205/258218),0,0,(-43875/1807526)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb585 : CertBound := ⟨false,false,⟨⟨(20875/84286),0,0,(621/84286)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb586 : CertBound := ⟨true,true,⟨⟨(831164429/651713437),(287756229/651713437),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb590 : CertBound := ⟨true,true,⟨⟨(2246128119/1666646111),(925182554/1666646111),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb591 : CertBound := ⟨false,false,⟨⟨(825209/1291090),0,0,(-12285/258218)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb592 : CertBound := ⟨true,true,⟨⟨(214600/1533493),(1183231/4600479),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb595 : CertBound := ⟨true,true,⟨⟨(-396257/18519877),(16952696/55559631),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb598 : CertBound := ⟨true,true,⟨⟨(7965000/47361431),(30450956/142084293),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb601 : CertBound := ⟨true,false,⟨⟨(669/1406),0,0,(109/29526)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb603 : CertBound := ⟨true,true,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb604 : CertBound := ⟨true,true,⟨⟨(1523676/1064531),(1105007/1064531),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb606 : CertBound := ⟨true,true,⟨⟨(178613577/167131367),(166787020/167131367),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb607 : CertBound := ⟨true,false,⟨⟨(5943/4366),0,0,(-373/91686)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb608 : CertBound := ⟨true,true,⟨⟨(291207/109150),0,0,(-2611/327450)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb609 : CertBound := ⟨true,true,⟨⟨(218317480/128644477),(92246870/128644477),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb611 : CertBound := ⟨true,true,⟨⟨(7617/30251),(63275/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb612 : CertBound := ⟨true,true,⟨⟨(-97181/4749407),(10761892/14248221),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb613 : CertBound := ⟨true,true,⟨⟨(30400/97513),(57452/97513),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb620 : CertBound := ⟨false,true,⟨⟨(-24300/147323),(51497/147323),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb621 : CertBound := ⟨true,true,⟨⟨(74197/700271),(152797/700271),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb627 : CertBound := ⟨true,true,⟨⟨(1361824/10527803),(1917252/10527803),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb630 : CertBound := ⟨true,false,⟨⟨(-24300/147323),(51497/147323),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb631 : CertBound := ⟨false,true,⟨⟨(-601572/1915199),(3511661/7660796),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb632 : CertBound := ⟨false,true,⟨⟨(187203/5421097),(1481141/5421097),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb639 : CertBound := ⟨true,true,⟨⟨(4995615/51991484),(15493577/51991484),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩

private def eb642 : CertBound := ⟨true,true,⟨⟨(30007/547307),(160632/547307),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩

private def eb645 : CertBound := ⟨false,true,⟨⟨(1859225/10355227),0,0,(-858600/72486589)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb646 : CertBound := ⟨false,false,⟨⟨(-1325497/22549813),(3996240/22549813),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def eb647 : CertBound := ⟨false,false,⟨⟨(91003/637177),0,0,(3078/637177)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb648 : CertBound := ⟨false,false,⟨⟨(164831/1046054),0,0,(5481/1046054)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb654 : CertBound := ⟨false,false,⟨⟨(-11689311/106599116),(5871683/26649779),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def eb655 : CertBound := ⟨true,true,⟨⟨(3389547/10028555),0,0,(106634/2005711)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(1557/4318),0,0,(-1/30226)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩

private def eb656 : CertBound := ⟨true,true,⟨⟨(159387/523027),0,0,(16720/523027)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb657 : CertBound := ⟨false,false,⟨⟨(24985871/784259531),(114593233/784259531),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(11574/32101),(-1/32101),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def eb666 : CertBound := ⟨false,false,⟨⟨(3644081/10355227),0,0,(-240408/10355227)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb669 : CertBound := ⟨true,true,⟨⟨(5981/1258),0,0,(-1183/1258)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb670 : CertBound := ⟨true,false,⟨⟨(8564475/10727197),(21645893/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩

private def eb673 : CertBound := ⟨true,true,⟨⟨(6533/170),0,0,(-3569/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩⟩⟩

private def eb677 : CertBound := ⟨true,false,⟨⟨(2012539/613802),0,0,(184759/613802)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb679 : CertBound := ⟨true,true,⟨⟨(14087773/2192150),0,0,(1293313/2192150)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb680 : CertBound := ⟨true,true,⟨⟨(7469/170),0,0,(-1363/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(89/334),0,0,(1/2338)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb683 : CertBound := ⟨false,true,⟨⟨(3979975/72486589),0,0,(22280/72486589)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb684 : CertBound := ⟨false,false,⟨⟨(-967545/22549813),(2108488/22549813),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb685 : CertBound := ⟨false,false,⟨⟨(49859/637177),0,0,(118/637177)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb686 : CertBound := ⟨false,false,⟨⟨(90343/1046054),0,0,(161/1046054)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb692 : CertBound := ⟨false,false,⟨⟨(-8792967/106599116),(3264491/26649779),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb695 : CertBound := ⟨false,false,⟨⟨(5007399/784259531),(58998601/784259531),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(11574/32101),(-1/32101),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb704 : CertBound := ⟨false,false,⟨⟨(1114393/10355227),0,0,(31192/51776135)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb708 : CertBound := ⟨true,false,⟨⟨(4177235/10727197),(10328301/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb711 : CertBound := ⟨true,true,⟨⟨(2717/170),0,0,(-483/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩

private def eb715 : CertBound := ⟨true,false,⟨⟨(133573/87686),0,0,(100031/613802)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb717 : CertBound := ⟨true,true,⟨⟨(6545077/2192150),0,0,(700217/2192150)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb718 : CertBound := ⟨true,true,⟨⟨(673/34),0,0,(-603/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(115/422),0,0,(1/1266)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb721 : CertBound := ⟨false,true,⟨⟨(177731/1807526),0,0,(-683/1807526)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb722 : CertBound := ⟨false,false,⟨⟨(-562140/7488217),(1215739/7488217),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb723 : CertBound := ⟨false,false,⟨⟨(57343/421430),0,0,(-103/421430)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb724 : CertBound := ⟨false,false,⟨⟨(3587/23083),0,0,(-80/161581)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb730 : CertBound := ⟨false,false,⟨⟨(-1273854/8849711),(7531157/35398844),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb731 : CertBound := ⟨true,true,⟨⟨(17885273/48468670),0,0,(323757/9693734)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(6361/17218),0,0,(-1/17218)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb733 : CertBound := ⟨false,false,⟨⟨(1707987/132663949),(17165996/132663949),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(6760/18301),(-1/18301),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb742 : CertBound := ⟨false,false,⟨⟨(1244117/6455450),0,0,(-4781/6455450)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb746 : CertBound := ⟨true,false,⟨⟨(19993/30251),(170200/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb751 : CertBound := ⟨true,false,⟨⟨(-2681441/4749407),(10850397/4749407),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(1493/5354),(-1/16062),0,0⟩⟩⟩

private def eb755 : CertBound := ⟨true,false,⟨⟨(80450/97513),(154458/97513),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb757 : CertBound := ⟨true,true,⟨⟨(983/185),0,0,(-54/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩

private def eb761 : CertBound := ⟨true,false,⟨⟨(31703/10915),0,0,(19414/76405)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb765 : CertBound := ⟨true,true,⟨⟨(1553447/272875),0,0,(135898/272875)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb766 : CertBound := ⟨true,true,⟨⟨(1199/185),0,0,(-102/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(115/422),0,0,(1/1266)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb771 : CertBound := ⟨false,true,⟨⟨(794625/14039977),0,0,(-19750/98279839)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(1557/4318),0,0,(-1/30226)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb772 : CertBound := ⟨false,false,⟨⟨(-51396/1734601),(135985/1734601),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb773 : CertBound := ⟨false,false,⟨⟨(40107/523027),0,0,(112/523027)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb780 : CertBound := ⟨false,false,⟨⟨(222495/2005711),0,0,(-790/2005711)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(1557/4318),0,0,(-1/30226)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb783 : CertBound := ⟨false,false,⟨⟨(-1481041/26649779),(5282779/53299558),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb788 : CertBound := ⟨false,false,⟨⟨(121599/27179581),(1826912/27179581),0,0⟩,⟨(12510/34801),(1/34801),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb792 : CertBound := ⟨true,false,⟨⟨(3680200/10727197),(9241922/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb795 : CertBound := ⟨true,false,⟨⟨(486249/306901),0,0,(50102/920703)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb797 : CertBound := ⟨true,true,⟨⟨(3403743/1096075),0,0,(350714/3288225)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb798 : CertBound := ⟨true,true,⟨⟨(1341/85),0,0,(-728/255)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb801 : CertBound := ⟨false,true,⟨⟨(3592515/28079954),0,0,(-132425/28079954)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(1557/4318),0,0,(-1/30226)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb802 : CertBound := ⟨false,false,⟨⟨(-7420123/106599116),(8699437/53299558),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb803 : CertBound := ⟨false,false,⟨⟨(98331/1046054),0,0,(10955/1046054)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb808 : CertBound := ⟨false,false,⟨⟨(5029521/20057110),0,0,(-37079/4011422)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(1557/4318),0,0,(-1/30226)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb810 : CertBound := ⟨true,false,⟨⟨(6671500/10727197),(16958462/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩

private def eb813 : CertBound := ⟨true,false,⟨⟨(1754301/613802),0,0,(216193/1841406)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩

private def eb815 : CertBound := ⟨true,true,⟨⟨(12280107/2192150),0,0,(1513351/6576450)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩

private def eb816 : CertBound := ⟨true,true,⟨⟨(5301/170),0,0,(-2911/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩

private def eb819 : CertBound := ⟨false,true,⟨⟨(6535875/67856138),0,0,(2125/9693734)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(6361/17218),0,0,(-1/17218)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb820 : CertBound := ⟨false,false,⟨⟨(-388869/7488217),(1019200/7488217),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb821 : CertBound := ⟨false,false,⟨⟨(6369/46166),0,0,(-97/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb827 : CertBound := ⟨false,false,⟨⟨(1830045/9693734),0,0,(4165/9693734)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(6361/17218),0,0,(-1/17218)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb830 : CertBound := ⟨false,false,⟨⟨(-1718411/17699422),(1523201/8849711),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb834 : CertBound := ⟨false,false,⟨⟨(1305027/231271139),(27163759/231271139),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb838 : CertBound := ⟨true,false,⟨⟨(17571/30251),(152315/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb842 : CertBound := ⟨true,false,⟨⟨(-4067/28103),(156391/84309),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩⟩⟩

private def eb845 : CertBound := ⟨true,false,⟨⟨(71140/97513),(138176/97513),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb847 : CertBound := ⟨true,false,⟨⟨(95943/30562),0,0,(2951/91686)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb851 : CertBound := ⟨true,true,⟨⟨(671601/109150),0,0,(20657/327450)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb852 : CertBound := ⟨true,true,⟨⟨(375/74),0,0,(-139/1554)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb857 : CertBound := ⟨false,true,⟨⟨(240413/3596971),0,0,(6892/1541559)⟩,⟨(2587/6806),0,0,(1/20418)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb858 : CertBound := ⟨false,false,⟨⟨(-698820/11017897),(1477331/11017897),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb859 : CertBound := ⟨false,false,⟨⟨(367/2567),0,0,(-112/38505)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb862 : CertBound := ⟨false,false,⟨⟨(-1571436/13021151),(9159133/52084604),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb864 : CertBound := ⟨false,false,⟨⟨(-1011781/110140129),(12763133/110140129),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(3247/8507),(-1/25521),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb872 : CertBound := ⟨false,false,⟨⟨(1682891/12846325),0,0,(337708/38538975)⟩,⟨(2587/6806),0,0,(1/20418)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb876 : CertBound := ⟨true,false,⟨⟨(497957/700271),(3016696/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb880 : CertBound := ⟨true,false,⟨⟨(1269727/8457119),(13024501/8457119),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb885 : CertBound := ⟨true,false,⟨⟨(9078694/10527803),(37882186/31583409),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb889 : CertBound := ⟨false,true,⟨⟨(429509/13779178),0,0,(170973/96454246)⟩,⟨(17703/45778),0,0,(1/45778)⟩,⟨(167/430),0,0,(-1/3010)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb890 : CertBound := ⟨false,false,⟨⟨(-499115/17679959),(1078592/17679959),0,0⟩,⟨(353/914),(1/2742),0,0⟩,⟨(1364/3517),(-1/3517),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb891 : CertBound := ⟨false,false,⟨⟨(761/12986),0,0,(-99/454510)⟩,⟨(579/1510),0,0,(1/1510)⟩,⟨(167/430),0,0,(-1/3010)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb894 : CertBound := ⟨false,false,⟨⟨(-4522933/83577988),(1670439/20894497),0,0⟩,⟨(353/914),(1/2742),0,0⟩,⟨(1364/3517),(-1/3517),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def eb896 : CertBound := ⟨false,false,⟨⟨(-561788/272669507),(14188809/272669507),0,0⟩,⟨(353/914),(1/2742),0,0⟩,⟨(21015/54241),(-1/54241),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def eb904 : CertBound := ⟨false,false,⟨⟨(3006563/49211350),0,0,(170973/49211350)⟩,⟨(17703/45778),0,0,(1/45778)⟩,⟨(167/430),0,0,(-1/3010)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb908 : CertBound := ⟨true,false,⟨⟨(2128591/8433958),(5921041/8433958),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb912 : CertBound := ⟨true,false,⟨⟨(439125/321686),0,0,(25225/15762614)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩

private def eb914 : CertBound := ⟨true,true,⟨⟨(860685/321686),0,0,(1009/321686)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩

private def eb915 : CertBound := ⟨true,true,⟨⟨(16101/8282),0,0,(-253/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩

private def eb918 : CertBound := ⟨true,false,⟨⟨(-1837512/50928131),(39097169/50928131),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb923 : CertBound := ⟨true,false,⟨⟨(3095681/9847487),(17507389/29542461),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩

private def eb927 : CertBound := ⟨false,true,⟨⟨(213575/1891477),0,0,(-2400/270211)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(3079/8066),0,0,(-1/24198)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb928 : CertBound := ⟨false,false,⟨⟨(-485901/11017897),(1238120/11017897),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb929 : CertBound := ⟨false,false,⟨⟨(2017/19765),0,0,(-28/19765)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(227/590),0,0,(-1/1770)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb930 : CertBound := ⟨false,false,⟨⟨(3257/25670),0,0,(-63/25670)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb937 : CertBound := ⟨false,false,⟨⟨(59801/270211),0,0,(-4704/270211)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(3079/8066),0,0,(-1/24198)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb943 : CertBound := ⟨false,false,⟨⟨(-2126899/26042302),(1851669/13021151),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb948 : CertBound := ⟨false,false,⟨⟨(1295416/67839167),(6050211/67839167),0,0⟩,⟨(2755/7247),(1/21741),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb952 : CertBound := ⟨true,false,⟨⟨(440039/700271),(2698847/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb960 : CertBound := ⟨true,true,⟨⟨(57529/12314),0,0,(-755/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩

private def eb962 : CertBound := ⟨true,false,⟨⟨(-1014103/8457119),(38088568/25371357),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb968 : CertBound := ⟨true,false,⟨⟨(8056428/10527803),(33874112/31583409),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb972 : CertBound := ⟨true,true,⟨⟨(49471/12314),0,0,(-551/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb973 : CertBound := ⟨false,true,⟨⟨(2167/8066),0,0,(-1611/56462)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(3079/8066),0,0,(-1/24198)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb974 : CertBound := ⟨false,false,⟨⟨(-2686183/26042302),(12188673/52084604),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb975 : CertBound := ⟨false,false,⟨⟨(71/590),0,0,(7/590)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(227/590),0,0,(-1/1770)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb976 : CertBound := ⟨false,false,⟨⟨(223/1510),0,0,(21/1510)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb983 : CertBound := ⟨false,false,⟨⟨(106183/201650),0,0,(-11277/201650)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(3079/8066),0,0,(-1/24198)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb984 : CertBound := ⟨true,true,⟨⟨(411/1310),0,0,(41/1310)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb986 : CertBound := ⟨true,false,⟨⟨(799619/700271),(4951487/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩

private def eb994 : CertBound := ⟨true,false,⟨⟨(7863965/1160054),0,0,(-264385/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩

private def eb996 : CertBound := ⟨true,true,⟨⟨(11009551/828610),0,0,(-370139/828610)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩

private def eb997 : CertBound := ⟨true,true,⟨⟨(106351/12314),0,0,(-1991/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩⟩⟩

private def eb1000 : CertBound := ⟨true,false,⟨⟨(-1434967/8457119),(69110935/25371357),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(8222/27073),(1/27073),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩

private def eb1006 : CertBound := ⟨true,false,⟨⟨(14687988/10527803),(62124152/31583409),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩

private def eb1010 : CertBound := ⟨true,true,⟨⟨(95449/12314),0,0,(-1715/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩

private def eb1011 : CertBound := ⟨false,true,⟨⟨(979525/21210854),0,0,(-57475/21210854)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(19899/51358),0,0,(-1/51358)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb1012 : CertBound := ⟨false,false,⟨⟨(-345332/17679959),(904215/17679959),0,0⟩,⟨(353/914),(1/2742),0,0⟩,⟨(1364/3517),(-1/3517),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb1013 : CertBound := ⟨false,false,⟨⟨(9029/198830),0,0,(-11/198830)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(1311/3370),0,0,(-1/3370)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1014 : CertBound := ⟨false,false,⟨⟨(1689/32465),0,0,(-32/227255)⟩,⟨(579/1510),0,0,(1/1510)⟩,⟨(167/430),0,0,(-1/3010)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1021 : CertBound := ⟨false,false,⟨⟨(274267/3030122),0,0,(-16093/3030122)⟩,⟨(227/590),0,0,(1/1770)⟩,⟨(19899/51358),0,0,(-1/51358)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb1027 : CertBound := ⟨false,false,⟨⟨(-762759/20894497),(8108323/125366982),0,0⟩,⟨(353/914),(1/2742),0,0⟩,⟨(1364/3517),(-1/3517),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb1032 : CertBound := ⟨false,false,⟨⟨(14504541/1882548107),(77921561/1882548107),0,0⟩,⟨(18819/48661),(1/48661),0,0⟩,⟨(1364/3517),(-1/3517),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb1036 : CertBound := ⟨true,false,⟨⟨(935716/4216979),(2649381/4216979),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb1037 : CertBound := ⟨false,true,⟨⟨(323783/179578),0,0,(-147649/538734)⟩,⟨(2463/6350),0,0,(1/19050)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb1044 : CertBound := ⟨true,false,⟨⟨(2275405/2251802),0,0,(168075/2251802)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

private def eb1046 : CertBound := ⟨true,true,⟨⟨(3185567/1608430),0,0,(47061/321686)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

private def eb1047 : CertBound := ⟨true,true,⟨⟨(17837/8282),0,0,(-1755/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩

private def eb1050 : CertBound := ⟨true,false,⟨⟨(-17165189/101856262),(76876453/101856262),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb1056 : CertBound := ⟨true,false,⟨⟨(2738072/9847487),(15661538/29542461),0,0⟩,⟨(2589/6674),(1/20022),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb1060 : CertBound := ⟨true,true,⟨⟨(7669/4141),0,0,(-648/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb1061 : CertBound := ⟨false,true,⟨⟨(2633475/104524931),0,0,(-130150/104524931)⟩,⟨(1311/3370),0,0,(1/3370)⟩,⟨(34601/88618),0,0,(-1/88618)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb1062 : CertBound := ⟨false,false,⟨⟨(-599222/54363419),(1584765/54363419),0,0⟩,⟨(1932/4957),(1/4957),0,0⟩,⟨(779/1994),(-1/5982),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb1063 : CertBound := ⟨false,false,⟨⟨(23811/921695),0,0,(76/921695)⟩,⟨(1311/3370),0,0,(1/3370)⟩,⟨(2141/5470),0,0,(-1/5470)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1064 : CertBound := ⟨false,false,⟨⟨(2051/71810),0,0,(37/502670)⟩,⟨(167/430),0,0,(1/3010)⟩,⟨(653/1670),0,0,(-1/5010)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1071 : CertBound := ⟨false,false,⟨⟨(737373/14932133),0,0,(-36442/14932133)⟩,⟨(1311/3370),0,0,(1/3370)⟩,⟨(34601/88618),0,0,(-1/88618)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb1077 : CertBound := ⟨false,false,⟨⟨(-1328064/64247677),(14207533/385486062),0,0⟩,⟨(1932/4957),(1/4957),0,0⟩,⟨(779/1994),(-1/5982),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb1082 : CertBound := ⟨false,false,⟨⟨(296587/72787979),(1733302/72787979),0,0⟩,⟨(33653/86281),(1/86281),0,0⟩,⟨(779/1994),(-1/5982),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb1086 : CertBound := ⟨true,false,⟨⟨(40426244/312797329),(99902592/312797329),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩

private def eb1087 : CertBound := ⟨false,false,⟨⟨(725/677),0,0,(-1976/14217)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1092 : CertBound := ⟨true,false,⟨⟨(1621835/3129094),0,0,(3262775/65710974)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

private def eb1094 : CertBound := ⟨true,true,⟨⟨(15893983/15645470),0,0,(913577/9387282)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

private def eb1095 : CertBound := ⟨true,true,⟨⟨(6309/1354),0,0,(-21755/28434)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩

private def eb1098 : CertBound := ⟨true,true,⟨⟨(5391/1354),0,0,(-18491/28434)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩

private def eb1099 : CertBound := ⟨false,false,⟨⟨(-772516/7488217),(2303835/7488217),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def eb1100 : CertBound := ⟨false,false,⟨⟨(6523/23083),0,0,(1296/161581)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1104 : CertBound := ⟨true,false,⟨⟨(20305875/67856138),0,0,(3249835/67856138)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(6361/17218),0,0,(-1/17218)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩

private def eb1105 : CertBound := ⟨false,false,⟨⟨(-1696782/8849711),(13542941/35398844),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def eb1106 : CertBound := ⟨true,true,⟨⟨(5685645/9693734),0,0,(4549769/48468670)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(6361/17218),0,0,(-1/17218)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩

private def eb1107 : CertBound := ⟨true,true,⟨⟨(25041/46166),0,0,(17711/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb1108 : CertBound := ⟨false,false,⟨⟨(7755571/132663949),(33363284/132663949),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(6760/18301),(-1/18301),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def eb1116 : CertBound := ⟨true,false,⟨⟨(40849/30251),(118920/30251),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩

private def eb1121 : CertBound := ⟨true,false,⟨⟨(-4959321/4749407),(66978287/14248221),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(9257/34318),(-1/34318),0,0⟩⟩⟩

private def eb1122 : CertBound := ⟨true,false,⟨⟨(588533/49966),0,0,(-636579/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(8711/32290),0,0,(-1/32290)⟩⟩⟩

private def eb1123 : CertBound := ⟨true,true,⟨⟨(5179/670),0,0,(-3393/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩⟩⟩

private def eb1124 : CertBound := ⟨true,true,⟨⟨(4119731/178450),0,0,(-636579/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(8711/32290),0,0,(-1/32290)⟩⟩⟩

private def eb1125 : CertBound := ⟨true,false,⟨⟨(165810/97513),(323594/97513),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩

private def eb1127 : CertBound := ⟨true,true,⟨⟨(451/37),0,0,(-202/777)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩⟩⟩

private def eb1131 : CertBound := ⟨true,false,⟨⟨(481577/76405),0,0,(4874/10915)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb1135 : CertBound := ⟨true,true,⟨⟨(3371039/272875),0,0,(238826/272875)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb1136 : CertBound := ⟨true,true,⟨⟨(2567/185),0,0,(-58/185)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(89/334),0,0,(1/2338)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩

private def eb1141 : CertBound := ⟨false,true,⟨⟨(2101275/21836038),0,0,(-4975/65508114)⟩,⟨(5033/13742),0,0,(1/41226)⟩,⟨(167/454),0,0,(-1/3178)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1142 : CertBound := ⟨false,false,⟨⟨(-4002949/91184291),(11391205/91184291),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def eb1143 : CertBound := ⟨false,false,⟨⟨(9101/68554),0,0,(421/1439634)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(167/454),0,0,(-1/3178)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1144 : CertBound := ⟨false,true,⟨⟨(9352415/73186666),0,0,(950325/73186666)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(6101/16622),0,0,(-1/49866)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩

private def eb1146 : CertBound := ⟨false,false,⟨⟨(-34615287/431053012),(67024319/431053012),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def eb1148 : CertBound := ⟨false,false,⟨⟨(980921/225604511),(74695124/676813533),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(6431/17522),(-1/52566),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def eb1157 : CertBound := ⟨false,false,⟨⟨(588357/3119434),0,0,(-1393/9358302)⟩,⟨(5033/13742),0,0,(1/41226)⟩,⟨(167/454),0,0,(-1/3178)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1160 : CertBound := ⟨true,false,⟨⟨(2343295/3066986),(4442563/3066986),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩

private def eb1164 : CertBound := ⟨true,false,⟨⟨(3102587/18519877),(28971396/18519877),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(10229/38062),(1/38062),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩

private def eb1169 : CertBound := ⟨true,false,⟨⟨(43953010/47361431),(57080994/47361431),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩

private def eb1174 : CertBound := ⟨false,true,⟨⟨(1355921/3029375),0,0,(-33236/3029375)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

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

private theorem of_local (id : Nat) (b : CertBound)
    (h : lowerEarlyTerminalBounds[id-1]? = some b) :
    lowerEarlyTerminalBound lowerEarlyTerminalState1 id = b := by
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

private theorem selected1 :
  (lowerEarlyTerminalBounds01[0]? = some eb1) ∧
  (lowerEarlyTerminalBounds01[1]? = some eb2) ∧
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
  (lowerEarlyTerminalBounds01[109]? = some eb110) ∧
  (lowerEarlyTerminalBounds01[113]? = some eb114) ∧
  (lowerEarlyTerminalBounds01[114]? = some eb115) ∧
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
  (lowerEarlyTerminalBounds01[143]? = some eb144) ∧
  (lowerEarlyTerminalBounds01[144]? = some eb145) ∧
  (lowerEarlyTerminalBounds01[145]? = some eb146) ∧
  (lowerEarlyTerminalBounds01[146]? = some eb147) ∧
  (lowerEarlyTerminalBounds01[149]? = some eb150) := by
  exact And.intro (Eq.refl (some eb1)) (And.intro (Eq.refl (some eb2)) (And.intro (Eq.refl (some eb6)) (And.intro (Eq.refl (some eb7)) (And.intro (Eq.refl (some eb8)) (And.intro (Eq.refl (some eb12)) (And.intro (Eq.refl (some eb13)) (And.intro (Eq.refl (some eb14)) (And.intro (Eq.refl (some eb15)) (And.intro (Eq.refl (some eb23)) (And.intro (Eq.refl (some eb27)) (And.intro (Eq.refl (some eb28)) (And.intro (Eq.refl (some eb33)) (And.intro (Eq.refl (some eb35)) (And.intro (Eq.refl (some eb36)) (And.intro (Eq.refl (some eb39)) (And.intro (Eq.refl (some eb43)) (And.intro (Eq.refl (some eb45)) (And.intro (Eq.refl (some eb50)) (And.intro (Eq.refl (some eb51)) (And.intro (Eq.refl (some eb52)) (And.intro (Eq.refl (some eb53)) (And.intro (Eq.refl (some eb60)) (And.intro (Eq.refl (some eb61)) (And.intro (Eq.refl (some eb66)) (And.intro (Eq.refl (some eb69)) (And.intro (Eq.refl (some eb70)) (And.intro (Eq.refl (some eb71)) (And.intro (Eq.refl (some eb75)) (And.intro (Eq.refl (some eb76)) (And.intro (Eq.refl (some eb84)) (And.intro (Eq.refl (some eb86)) (And.intro (Eq.refl (some eb87)) (And.intro (Eq.refl (some eb90)) (And.intro (Eq.refl (some eb96)) (And.intro (Eq.refl (some eb100)) (And.intro (Eq.refl (some eb101)) (And.intro (Eq.refl (some eb102)) (And.intro (Eq.refl (some eb103)) (And.intro (Eq.refl (some eb105)) (And.intro (Eq.refl (some eb106)) (And.intro (Eq.refl (some eb107)) (And.intro (Eq.refl (some eb109)) (And.intro (Eq.refl (some eb110)) (And.intro (Eq.refl (some eb114)) (And.intro (Eq.refl (some eb115)) (And.intro (Eq.refl (some eb116)) (And.intro (Eq.refl (some eb118)) (And.intro (Eq.refl (some eb119)) (And.intro (Eq.refl (some eb120)) (And.intro (Eq.refl (some eb121)) (And.intro (Eq.refl (some eb122)) (And.intro (Eq.refl (some eb125)) (And.intro (Eq.refl (some eb127)) (And.intro (Eq.refl (some eb129)) (And.intro (Eq.refl (some eb131)) (And.intro (Eq.refl (some eb134)) (And.intro (Eq.refl (some eb137)) (And.intro (Eq.refl (some eb140)) (And.intro (Eq.refl (some eb144)) (And.intro (Eq.refl (some eb145)) (And.intro (Eq.refl (some eb146)) (And.intro (Eq.refl (some eb147)) (Eq.refl (some eb150))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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

private theorem selected2 :
  (lowerEarlyTerminalBounds02[3]? = some eb154) ∧
  (lowerEarlyTerminalBounds02[8]? = some eb159) ∧
  (lowerEarlyTerminalBounds02[9]? = some eb160) ∧
  (lowerEarlyTerminalBounds02[11]? = some eb162) ∧
  (lowerEarlyTerminalBounds02[12]? = some eb163) ∧
  (lowerEarlyTerminalBounds02[13]? = some eb164) ∧
  (lowerEarlyTerminalBounds02[14]? = some eb165) ∧
  (lowerEarlyTerminalBounds02[19]? = some eb170) ∧
  (lowerEarlyTerminalBounds02[20]? = some eb171) ∧
  (lowerEarlyTerminalBounds02[21]? = some eb172) ∧
  (lowerEarlyTerminalBounds02[22]? = some eb173) ∧
  (lowerEarlyTerminalBounds02[23]? = some eb174) ∧
  (lowerEarlyTerminalBounds02[32]? = some eb183) ∧
  (lowerEarlyTerminalBounds02[35]? = some eb186) ∧
  (lowerEarlyTerminalBounds02[36]? = some eb187) ∧
  (lowerEarlyTerminalBounds02[37]? = some eb188) ∧
  (lowerEarlyTerminalBounds02[42]? = some eb193) ∧
  (lowerEarlyTerminalBounds02[43]? = some eb194) ∧
  (lowerEarlyTerminalBounds02[44]? = some eb195) ∧
  (lowerEarlyTerminalBounds02[45]? = some eb196) ∧
  (lowerEarlyTerminalBounds02[46]? = some eb197) ∧
  (lowerEarlyTerminalBounds02[48]? = some eb199) ∧
  (lowerEarlyTerminalBounds02[52]? = some eb203) ∧
  (lowerEarlyTerminalBounds02[56]? = some eb207) ∧
  (lowerEarlyTerminalBounds02[57]? = some eb208) ∧
  (lowerEarlyTerminalBounds02[63]? = some eb214) ∧
  (lowerEarlyTerminalBounds02[64]? = some eb215) ∧
  (lowerEarlyTerminalBounds02[65]? = some eb216) ∧
  (lowerEarlyTerminalBounds02[66]? = some eb217) ∧
  (lowerEarlyTerminalBounds02[67]? = some eb218) ∧
  (lowerEarlyTerminalBounds02[72]? = some eb223) ∧
  (lowerEarlyTerminalBounds02[75]? = some eb226) ∧
  (lowerEarlyTerminalBounds02[78]? = some eb229) ∧
  (lowerEarlyTerminalBounds02[79]? = some eb230) ∧
  (lowerEarlyTerminalBounds02[80]? = some eb231) ∧
  (lowerEarlyTerminalBounds02[84]? = some eb235) ∧
  (lowerEarlyTerminalBounds02[85]? = some eb236) ∧
  (lowerEarlyTerminalBounds02[90]? = some eb241) ∧
  (lowerEarlyTerminalBounds02[91]? = some eb242) ∧
  (lowerEarlyTerminalBounds02[92]? = some eb243) ∧
  (lowerEarlyTerminalBounds02[93]? = some eb244) ∧
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
  exact And.intro (Eq.refl (some eb154)) (And.intro (Eq.refl (some eb159)) (And.intro (Eq.refl (some eb160)) (And.intro (Eq.refl (some eb162)) (And.intro (Eq.refl (some eb163)) (And.intro (Eq.refl (some eb164)) (And.intro (Eq.refl (some eb165)) (And.intro (Eq.refl (some eb170)) (And.intro (Eq.refl (some eb171)) (And.intro (Eq.refl (some eb172)) (And.intro (Eq.refl (some eb173)) (And.intro (Eq.refl (some eb174)) (And.intro (Eq.refl (some eb183)) (And.intro (Eq.refl (some eb186)) (And.intro (Eq.refl (some eb187)) (And.intro (Eq.refl (some eb188)) (And.intro (Eq.refl (some eb193)) (And.intro (Eq.refl (some eb194)) (And.intro (Eq.refl (some eb195)) (And.intro (Eq.refl (some eb196)) (And.intro (Eq.refl (some eb197)) (And.intro (Eq.refl (some eb199)) (And.intro (Eq.refl (some eb203)) (And.intro (Eq.refl (some eb207)) (And.intro (Eq.refl (some eb208)) (And.intro (Eq.refl (some eb214)) (And.intro (Eq.refl (some eb215)) (And.intro (Eq.refl (some eb216)) (And.intro (Eq.refl (some eb217)) (And.intro (Eq.refl (some eb218)) (And.intro (Eq.refl (some eb223)) (And.intro (Eq.refl (some eb226)) (And.intro (Eq.refl (some eb229)) (And.intro (Eq.refl (some eb230)) (And.intro (Eq.refl (some eb231)) (And.intro (Eq.refl (some eb235)) (And.intro (Eq.refl (some eb236)) (And.intro (Eq.refl (some eb241)) (And.intro (Eq.refl (some eb242)) (And.intro (Eq.refl (some eb243)) (And.intro (Eq.refl (some eb244)) (And.intro (Eq.refl (some eb245)) (And.intro (Eq.refl (some eb247)) (And.intro (Eq.refl (some eb251)) (And.intro (Eq.refl (some eb252)) (And.intro (Eq.refl (some eb257)) (And.intro (Eq.refl (some eb258)) (And.intro (Eq.refl (some eb259)) (And.intro (Eq.refl (some eb260)) (And.intro (Eq.refl (some eb261)) (And.intro (Eq.refl (some eb268)) (And.intro (Eq.refl (some eb272)) (And.intro (Eq.refl (some eb280)) (And.intro (Eq.refl (some eb282)) (And.intro (Eq.refl (some eb283)) (And.intro (Eq.refl (some eb286)) (And.intro (Eq.refl (some eb292)) (And.intro (Eq.refl (some eb296)) (And.intro (Eq.refl (some eb297)) (And.intro (Eq.refl (some eb298)) (And.intro (Eq.refl (some eb299)) (Eq.refl (some eb300))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  (lowerEarlyTerminalBounds03[47]? = some eb348) ∧
  (lowerEarlyTerminalBounds03[48]? = some eb349) ∧
  (lowerEarlyTerminalBounds03[49]? = some eb350) ∧
  (lowerEarlyTerminalBounds03[54]? = some eb355) ∧
  (lowerEarlyTerminalBounds03[55]? = some eb356) ∧
  (lowerEarlyTerminalBounds03[56]? = some eb357) ∧
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
  (lowerEarlyTerminalBounds03[92]? = some eb393) ∧
  (lowerEarlyTerminalBounds03[93]? = some eb394) ∧
  (lowerEarlyTerminalBounds03[94]? = some eb395) ∧
  (lowerEarlyTerminalBounds03[95]? = some eb396) ∧
  (lowerEarlyTerminalBounds03[96]? = some eb397) ∧
  (lowerEarlyTerminalBounds03[97]? = some eb398) ∧
  (lowerEarlyTerminalBounds03[98]? = some eb399) ∧
  (lowerEarlyTerminalBounds03[101]? = some eb402) ∧
  (lowerEarlyTerminalBounds03[102]? = some eb403) ∧
  (lowerEarlyTerminalBounds03[103]? = some eb404) ∧
  (lowerEarlyTerminalBounds03[104]? = some eb405) ∧
  (lowerEarlyTerminalBounds03[105]? = some eb406) ∧
  (lowerEarlyTerminalBounds03[107]? = some eb408) ∧
  (lowerEarlyTerminalBounds03[110]? = some eb411) ∧
  (lowerEarlyTerminalBounds03[111]? = some eb412) ∧
  (lowerEarlyTerminalBounds03[113]? = some eb414) ∧
  (lowerEarlyTerminalBounds03[114]? = some eb415) ∧
  (lowerEarlyTerminalBounds03[115]? = some eb416) ∧
  (lowerEarlyTerminalBounds03[118]? = some eb419) ∧
  (lowerEarlyTerminalBounds03[119]? = some eb420) ∧
  (lowerEarlyTerminalBounds03[121]? = some eb422) ∧
  (lowerEarlyTerminalBounds03[123]? = some eb424) ∧
  (lowerEarlyTerminalBounds03[124]? = some eb425) ∧
  (lowerEarlyTerminalBounds03[125]? = some eb426) ∧
  (lowerEarlyTerminalBounds03[126]? = some eb427) ∧
  (lowerEarlyTerminalBounds03[130]? = some eb431) ∧
  (lowerEarlyTerminalBounds03[131]? = some eb432) ∧
  (lowerEarlyTerminalBounds03[132]? = some eb433) ∧
  (lowerEarlyTerminalBounds03[133]? = some eb434) ∧
  (lowerEarlyTerminalBounds03[134]? = some eb435) ∧
  (lowerEarlyTerminalBounds03[135]? = some eb436) ∧
  (lowerEarlyTerminalBounds03[136]? = some eb437) ∧
  (lowerEarlyTerminalBounds03[138]? = some eb439) ∧
  (lowerEarlyTerminalBounds03[139]? = some eb440) ∧
  (lowerEarlyTerminalBounds03[140]? = some eb441) ∧
  (lowerEarlyTerminalBounds03[142]? = some eb443) ∧
  (lowerEarlyTerminalBounds03[145]? = some eb446) ∧
  (lowerEarlyTerminalBounds03[146]? = some eb447) ∧
  (lowerEarlyTerminalBounds03[148]? = some eb449) ∧
  (lowerEarlyTerminalBounds03[149]? = some eb450) := by
  exact And.intro (Eq.refl (some eb301)) (And.intro (Eq.refl (some eb308)) (And.intro (Eq.refl (some eb312)) (And.intro (Eq.refl (some eb318)) (And.intro (Eq.refl (some eb320)) (And.intro (Eq.refl (some eb321)) (And.intro (Eq.refl (some eb324)) (And.intro (Eq.refl (some eb325)) (And.intro (Eq.refl (some eb327)) (And.intro (Eq.refl (some eb328)) (And.intro (Eq.refl (some eb329)) (And.intro (Eq.refl (some eb331)) (And.intro (Eq.refl (some eb332)) (And.intro (Eq.refl (some eb333)) (And.intro (Eq.refl (some eb334)) (And.intro (Eq.refl (some eb335)) (And.intro (Eq.refl (some eb336)) (And.intro (Eq.refl (some eb337)) (And.intro (Eq.refl (some eb338)) (And.intro (Eq.refl (some eb340)) (And.intro (Eq.refl (some eb341)) (And.intro (Eq.refl (some eb342)) (And.intro (Eq.refl (some eb345)) (And.intro (Eq.refl (some eb346)) (And.intro (Eq.refl (some eb347)) (And.intro (Eq.refl (some eb348)) (And.intro (Eq.refl (some eb349)) (And.intro (Eq.refl (some eb350)) (And.intro (Eq.refl (some eb355)) (And.intro (Eq.refl (some eb356)) (And.intro (Eq.refl (some eb357)) (And.intro (Eq.refl (some eb358)) (And.intro (Eq.refl (some eb359)) (And.intro (Eq.refl (some eb360)) (And.intro (Eq.refl (some eb363)) (And.intro (Eq.refl (some eb366)) (And.intro (Eq.refl (some eb370)) (And.intro (Eq.refl (some eb375)) (And.intro (Eq.refl (some eb376)) (And.intro (Eq.refl (some eb380)) (And.intro (Eq.refl (some eb382)) (And.intro (Eq.refl (some eb383)) (And.intro (Eq.refl (some eb384)) (And.intro (Eq.refl (some eb385)) (And.intro (Eq.refl (some eb386)) (And.intro (Eq.refl (some eb387)) (And.intro (Eq.refl (some eb388)) (And.intro (Eq.refl (some eb389)) (And.intro (Eq.refl (some eb390)) (And.intro (Eq.refl (some eb391)) (And.intro (Eq.refl (some eb392)) (And.intro (Eq.refl (some eb393)) (And.intro (Eq.refl (some eb394)) (And.intro (Eq.refl (some eb395)) (And.intro (Eq.refl (some eb396)) (And.intro (Eq.refl (some eb397)) (And.intro (Eq.refl (some eb398)) (And.intro (Eq.refl (some eb399)) (And.intro (Eq.refl (some eb402)) (And.intro (Eq.refl (some eb403)) (And.intro (Eq.refl (some eb404)) (And.intro (Eq.refl (some eb405)) (And.intro (Eq.refl (some eb406)) (And.intro (Eq.refl (some eb408)) (And.intro (Eq.refl (some eb411)) (And.intro (Eq.refl (some eb412)) (And.intro (Eq.refl (some eb414)) (And.intro (Eq.refl (some eb415)) (And.intro (Eq.refl (some eb416)) (And.intro (Eq.refl (some eb419)) (And.intro (Eq.refl (some eb420)) (And.intro (Eq.refl (some eb422)) (And.intro (Eq.refl (some eb424)) (And.intro (Eq.refl (some eb425)) (And.intro (Eq.refl (some eb426)) (And.intro (Eq.refl (some eb427)) (And.intro (Eq.refl (some eb431)) (And.intro (Eq.refl (some eb432)) (And.intro (Eq.refl (some eb433)) (And.intro (Eq.refl (some eb434)) (And.intro (Eq.refl (some eb435)) (And.intro (Eq.refl (some eb436)) (And.intro (Eq.refl (some eb437)) (And.intro (Eq.refl (some eb439)) (And.intro (Eq.refl (some eb440)) (And.intro (Eq.refl (some eb441)) (And.intro (Eq.refl (some eb443)) (And.intro (Eq.refl (some eb446)) (And.intro (Eq.refl (some eb447)) (And.intro (Eq.refl (some eb449)) (Eq.refl (some eb450)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem chunk4 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[450+k]? = lowerEarlyTerminalBounds04[k]? := by
  unfold lowerEarlyTerminalBounds

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05) (by simp only [List.length_append, length01, length02, length03, length04, length05]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04) (by simp only [List.length_append, length01, length02, length03, length04]; omega)]

  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03) (by simp only [List.length_append, length01, length02, length03]; omega)]

  simp only [List.length_append, length01, length02, length03]

  exact congrArg (fun j => lowerEarlyTerminalBounds04[j]?) (by omega)

private theorem selected4 :
  (lowerEarlyTerminalBounds04[1]? = some eb452) ∧
  (lowerEarlyTerminalBounds04[3]? = some eb454) ∧
  (lowerEarlyTerminalBounds04[4]? = some eb455) ∧
  (lowerEarlyTerminalBounds04[5]? = some eb456) ∧
  (lowerEarlyTerminalBounds04[6]? = some eb457) ∧
  (lowerEarlyTerminalBounds04[9]? = some eb460) ∧
  (lowerEarlyTerminalBounds04[10]? = some eb461) ∧
  (lowerEarlyTerminalBounds04[11]? = some eb462) ∧
  (lowerEarlyTerminalBounds04[12]? = some eb463) ∧
  (lowerEarlyTerminalBounds04[13]? = some eb464) ∧
  (lowerEarlyTerminalBounds04[15]? = some eb466) ∧
  (lowerEarlyTerminalBounds04[17]? = some eb468) ∧
  (lowerEarlyTerminalBounds04[18]? = some eb469) ∧
  (lowerEarlyTerminalBounds04[19]? = some eb470) ∧
  (lowerEarlyTerminalBounds04[20]? = some eb471) ∧
  (lowerEarlyTerminalBounds04[21]? = some eb472) ∧
  (lowerEarlyTerminalBounds04[22]? = some eb473) ∧
  (lowerEarlyTerminalBounds04[23]? = some eb474) ∧
  (lowerEarlyTerminalBounds04[24]? = some eb475) ∧
  (lowerEarlyTerminalBounds04[25]? = some eb476) ∧
  (lowerEarlyTerminalBounds04[26]? = some eb477) ∧
  (lowerEarlyTerminalBounds04[27]? = some eb478) ∧
  (lowerEarlyTerminalBounds04[28]? = some eb479) ∧
  (lowerEarlyTerminalBounds04[29]? = some eb480) ∧
  (lowerEarlyTerminalBounds04[30]? = some eb481) ∧
  (lowerEarlyTerminalBounds04[31]? = some eb482) ∧
  (lowerEarlyTerminalBounds04[32]? = some eb483) ∧
  (lowerEarlyTerminalBounds04[33]? = some eb484) ∧
  (lowerEarlyTerminalBounds04[34]? = some eb485) ∧
  (lowerEarlyTerminalBounds04[35]? = some eb486) ∧
  (lowerEarlyTerminalBounds04[36]? = some eb487) ∧
  (lowerEarlyTerminalBounds04[37]? = some eb488) ∧
  (lowerEarlyTerminalBounds04[39]? = some eb490) ∧
  (lowerEarlyTerminalBounds04[40]? = some eb491) ∧
  (lowerEarlyTerminalBounds04[43]? = some eb494) ∧
  (lowerEarlyTerminalBounds04[44]? = some eb495) ∧
  (lowerEarlyTerminalBounds04[45]? = some eb496) ∧
  (lowerEarlyTerminalBounds04[46]? = some eb497) ∧
  (lowerEarlyTerminalBounds04[47]? = some eb498) ∧
  (lowerEarlyTerminalBounds04[48]? = some eb499) ∧
  (lowerEarlyTerminalBounds04[49]? = some eb500) ∧
  (lowerEarlyTerminalBounds04[50]? = some eb501) ∧
  (lowerEarlyTerminalBounds04[51]? = some eb502) ∧
  (lowerEarlyTerminalBounds04[52]? = some eb503) ∧
  (lowerEarlyTerminalBounds04[53]? = some eb504) ∧
  (lowerEarlyTerminalBounds04[54]? = some eb505) ∧
  (lowerEarlyTerminalBounds04[55]? = some eb506) ∧
  (lowerEarlyTerminalBounds04[56]? = some eb507) ∧
  (lowerEarlyTerminalBounds04[59]? = some eb510) ∧
  (lowerEarlyTerminalBounds04[61]? = some eb512) ∧
  (lowerEarlyTerminalBounds04[62]? = some eb513) ∧
  (lowerEarlyTerminalBounds04[65]? = some eb516) ∧
  (lowerEarlyTerminalBounds04[68]? = some eb519) ∧
  (lowerEarlyTerminalBounds04[71]? = some eb522) ∧
  (lowerEarlyTerminalBounds04[72]? = some eb523) ∧
  (lowerEarlyTerminalBounds04[73]? = some eb524) ∧
  (lowerEarlyTerminalBounds04[74]? = some eb525) ∧
  (lowerEarlyTerminalBounds04[75]? = some eb526) ∧
  (lowerEarlyTerminalBounds04[76]? = some eb527) ∧
  (lowerEarlyTerminalBounds04[77]? = some eb528) ∧
  (lowerEarlyTerminalBounds04[78]? = some eb529) ∧
  (lowerEarlyTerminalBounds04[80]? = some eb531) ∧
  (lowerEarlyTerminalBounds04[81]? = some eb532) ∧
  (lowerEarlyTerminalBounds04[83]? = some eb534) ∧
  (lowerEarlyTerminalBounds04[84]? = some eb535) ∧
  (lowerEarlyTerminalBounds04[85]? = some eb536) ∧
  (lowerEarlyTerminalBounds04[86]? = some eb537) ∧
  (lowerEarlyTerminalBounds04[87]? = some eb538) ∧
  (lowerEarlyTerminalBounds04[88]? = some eb539) ∧
  (lowerEarlyTerminalBounds04[89]? = some eb540) ∧
  (lowerEarlyTerminalBounds04[94]? = some eb545) ∧
  (lowerEarlyTerminalBounds04[96]? = some eb547) ∧
  (lowerEarlyTerminalBounds04[99]? = some eb550) ∧
  (lowerEarlyTerminalBounds04[102]? = some eb553) ∧
  (lowerEarlyTerminalBounds04[103]? = some eb554) ∧
  (lowerEarlyTerminalBounds04[104]? = some eb555) ∧
  (lowerEarlyTerminalBounds04[105]? = some eb556) ∧
  (lowerEarlyTerminalBounds04[106]? = some eb557) ∧
  (lowerEarlyTerminalBounds04[107]? = some eb558) ∧
  (lowerEarlyTerminalBounds04[108]? = some eb559) ∧
  (lowerEarlyTerminalBounds04[109]? = some eb560) ∧
  (lowerEarlyTerminalBounds04[113]? = some eb564) ∧
  (lowerEarlyTerminalBounds04[116]? = some eb567) ∧
  (lowerEarlyTerminalBounds04[117]? = some eb568) ∧
  (lowerEarlyTerminalBounds04[118]? = some eb569) ∧
  (lowerEarlyTerminalBounds04[119]? = some eb570) ∧
  (lowerEarlyTerminalBounds04[120]? = some eb571) ∧
  (lowerEarlyTerminalBounds04[122]? = some eb573) ∧
  (lowerEarlyTerminalBounds04[124]? = some eb575) ∧
  (lowerEarlyTerminalBounds04[125]? = some eb576) ∧
  (lowerEarlyTerminalBounds04[126]? = some eb577) ∧
  (lowerEarlyTerminalBounds04[127]? = some eb578) ∧
  (lowerEarlyTerminalBounds04[128]? = some eb579) ∧
  (lowerEarlyTerminalBounds04[130]? = some eb581) ∧
  (lowerEarlyTerminalBounds04[131]? = some eb582) ∧
  (lowerEarlyTerminalBounds04[132]? = some eb583) ∧
  (lowerEarlyTerminalBounds04[133]? = some eb584) ∧
  (lowerEarlyTerminalBounds04[134]? = some eb585) ∧
  (lowerEarlyTerminalBounds04[135]? = some eb586) ∧
  (lowerEarlyTerminalBounds04[139]? = some eb590) ∧
  (lowerEarlyTerminalBounds04[140]? = some eb591) ∧
  (lowerEarlyTerminalBounds04[141]? = some eb592) ∧
  (lowerEarlyTerminalBounds04[144]? = some eb595) ∧
  (lowerEarlyTerminalBounds04[147]? = some eb598) := by
  exact And.intro (Eq.refl (some eb452)) (And.intro (Eq.refl (some eb454)) (And.intro (Eq.refl (some eb455)) (And.intro (Eq.refl (some eb456)) (And.intro (Eq.refl (some eb457)) (And.intro (Eq.refl (some eb460)) (And.intro (Eq.refl (some eb461)) (And.intro (Eq.refl (some eb462)) (And.intro (Eq.refl (some eb463)) (And.intro (Eq.refl (some eb464)) (And.intro (Eq.refl (some eb466)) (And.intro (Eq.refl (some eb468)) (And.intro (Eq.refl (some eb469)) (And.intro (Eq.refl (some eb470)) (And.intro (Eq.refl (some eb471)) (And.intro (Eq.refl (some eb472)) (And.intro (Eq.refl (some eb473)) (And.intro (Eq.refl (some eb474)) (And.intro (Eq.refl (some eb475)) (And.intro (Eq.refl (some eb476)) (And.intro (Eq.refl (some eb477)) (And.intro (Eq.refl (some eb478)) (And.intro (Eq.refl (some eb479)) (And.intro (Eq.refl (some eb480)) (And.intro (Eq.refl (some eb481)) (And.intro (Eq.refl (some eb482)) (And.intro (Eq.refl (some eb483)) (And.intro (Eq.refl (some eb484)) (And.intro (Eq.refl (some eb485)) (And.intro (Eq.refl (some eb486)) (And.intro (Eq.refl (some eb487)) (And.intro (Eq.refl (some eb488)) (And.intro (Eq.refl (some eb490)) (And.intro (Eq.refl (some eb491)) (And.intro (Eq.refl (some eb494)) (And.intro (Eq.refl (some eb495)) (And.intro (Eq.refl (some eb496)) (And.intro (Eq.refl (some eb497)) (And.intro (Eq.refl (some eb498)) (And.intro (Eq.refl (some eb499)) (And.intro (Eq.refl (some eb500)) (And.intro (Eq.refl (some eb501)) (And.intro (Eq.refl (some eb502)) (And.intro (Eq.refl (some eb503)) (And.intro (Eq.refl (some eb504)) (And.intro (Eq.refl (some eb505)) (And.intro (Eq.refl (some eb506)) (And.intro (Eq.refl (some eb507)) (And.intro (Eq.refl (some eb510)) (And.intro (Eq.refl (some eb512)) (And.intro (Eq.refl (some eb513)) (And.intro (Eq.refl (some eb516)) (And.intro (Eq.refl (some eb519)) (And.intro (Eq.refl (some eb522)) (And.intro (Eq.refl (some eb523)) (And.intro (Eq.refl (some eb524)) (And.intro (Eq.refl (some eb525)) (And.intro (Eq.refl (some eb526)) (And.intro (Eq.refl (some eb527)) (And.intro (Eq.refl (some eb528)) (And.intro (Eq.refl (some eb529)) (And.intro (Eq.refl (some eb531)) (And.intro (Eq.refl (some eb532)) (And.intro (Eq.refl (some eb534)) (And.intro (Eq.refl (some eb535)) (And.intro (Eq.refl (some eb536)) (And.intro (Eq.refl (some eb537)) (And.intro (Eq.refl (some eb538)) (And.intro (Eq.refl (some eb539)) (And.intro (Eq.refl (some eb540)) (And.intro (Eq.refl (some eb545)) (And.intro (Eq.refl (some eb547)) (And.intro (Eq.refl (some eb550)) (And.intro (Eq.refl (some eb553)) (And.intro (Eq.refl (some eb554)) (And.intro (Eq.refl (some eb555)) (And.intro (Eq.refl (some eb556)) (And.intro (Eq.refl (some eb557)) (And.intro (Eq.refl (some eb558)) (And.intro (Eq.refl (some eb559)) (And.intro (Eq.refl (some eb560)) (And.intro (Eq.refl (some eb564)) (And.intro (Eq.refl (some eb567)) (And.intro (Eq.refl (some eb568)) (And.intro (Eq.refl (some eb569)) (And.intro (Eq.refl (some eb570)) (And.intro (Eq.refl (some eb571)) (And.intro (Eq.refl (some eb573)) (And.intro (Eq.refl (some eb575)) (And.intro (Eq.refl (some eb576)) (And.intro (Eq.refl (some eb577)) (And.intro (Eq.refl (some eb578)) (And.intro (Eq.refl (some eb579)) (And.intro (Eq.refl (some eb581)) (And.intro (Eq.refl (some eb582)) (And.intro (Eq.refl (some eb583)) (And.intro (Eq.refl (some eb584)) (And.intro (Eq.refl (some eb585)) (And.intro (Eq.refl (some eb586)) (And.intro (Eq.refl (some eb590)) (And.intro (Eq.refl (some eb591)) (And.intro (Eq.refl (some eb592)) (And.intro (Eq.refl (some eb595)) (Eq.refl (some eb598))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem chunk5 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[600+k]? = lowerEarlyTerminalBounds05[k]? := by
  unfold lowerEarlyTerminalBounds

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05) (by simp only [List.length_append, length01, length02, length03, length04, length05]; omega)]

  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04) (by simp only [List.length_append, length01, length02, length03, length04]; omega)]

  simp only [List.length_append, length01, length02, length03, length04]

  exact congrArg (fun j => lowerEarlyTerminalBounds05[j]?) (by omega)

private theorem selected5 :
  (lowerEarlyTerminalBounds05[0]? = some eb601) ∧
  (lowerEarlyTerminalBounds05[2]? = some eb603) ∧
  (lowerEarlyTerminalBounds05[3]? = some eb604) ∧
  (lowerEarlyTerminalBounds05[5]? = some eb606) ∧
  (lowerEarlyTerminalBounds05[6]? = some eb607) ∧
  (lowerEarlyTerminalBounds05[7]? = some eb608) ∧
  (lowerEarlyTerminalBounds05[8]? = some eb609) ∧
  (lowerEarlyTerminalBounds05[10]? = some eb611) ∧
  (lowerEarlyTerminalBounds05[11]? = some eb612) ∧
  (lowerEarlyTerminalBounds05[12]? = some eb613) ∧
  (lowerEarlyTerminalBounds05[19]? = some eb620) ∧
  (lowerEarlyTerminalBounds05[20]? = some eb621) ∧
  (lowerEarlyTerminalBounds05[26]? = some eb627) ∧
  (lowerEarlyTerminalBounds05[29]? = some eb630) ∧
  (lowerEarlyTerminalBounds05[30]? = some eb631) ∧
  (lowerEarlyTerminalBounds05[31]? = some eb632) ∧
  (lowerEarlyTerminalBounds05[38]? = some eb639) ∧
  (lowerEarlyTerminalBounds05[41]? = some eb642) ∧
  (lowerEarlyTerminalBounds05[44]? = some eb645) ∧
  (lowerEarlyTerminalBounds05[45]? = some eb646) ∧
  (lowerEarlyTerminalBounds05[46]? = some eb647) ∧
  (lowerEarlyTerminalBounds05[47]? = some eb648) ∧
  (lowerEarlyTerminalBounds05[53]? = some eb654) ∧
  (lowerEarlyTerminalBounds05[54]? = some eb655) ∧
  (lowerEarlyTerminalBounds05[55]? = some eb656) ∧
  (lowerEarlyTerminalBounds05[56]? = some eb657) ∧
  (lowerEarlyTerminalBounds05[65]? = some eb666) ∧
  (lowerEarlyTerminalBounds05[68]? = some eb669) ∧
  (lowerEarlyTerminalBounds05[69]? = some eb670) ∧
  (lowerEarlyTerminalBounds05[72]? = some eb673) ∧
  (lowerEarlyTerminalBounds05[76]? = some eb677) ∧
  (lowerEarlyTerminalBounds05[78]? = some eb679) ∧
  (lowerEarlyTerminalBounds05[79]? = some eb680) ∧
  (lowerEarlyTerminalBounds05[82]? = some eb683) ∧
  (lowerEarlyTerminalBounds05[83]? = some eb684) ∧
  (lowerEarlyTerminalBounds05[84]? = some eb685) ∧
  (lowerEarlyTerminalBounds05[85]? = some eb686) ∧
  (lowerEarlyTerminalBounds05[91]? = some eb692) ∧
  (lowerEarlyTerminalBounds05[94]? = some eb695) ∧
  (lowerEarlyTerminalBounds05[103]? = some eb704) ∧
  (lowerEarlyTerminalBounds05[107]? = some eb708) ∧
  (lowerEarlyTerminalBounds05[110]? = some eb711) ∧
  (lowerEarlyTerminalBounds05[114]? = some eb715) ∧
  (lowerEarlyTerminalBounds05[116]? = some eb717) ∧
  (lowerEarlyTerminalBounds05[117]? = some eb718) ∧
  (lowerEarlyTerminalBounds05[120]? = some eb721) ∧
  (lowerEarlyTerminalBounds05[121]? = some eb722) ∧
  (lowerEarlyTerminalBounds05[122]? = some eb723) ∧
  (lowerEarlyTerminalBounds05[123]? = some eb724) ∧
  (lowerEarlyTerminalBounds05[129]? = some eb730) ∧
  (lowerEarlyTerminalBounds05[130]? = some eb731) ∧
  (lowerEarlyTerminalBounds05[132]? = some eb733) ∧
  (lowerEarlyTerminalBounds05[141]? = some eb742) ∧
  (lowerEarlyTerminalBounds05[145]? = some eb746) := by
  exact And.intro (Eq.refl (some eb601)) (And.intro (Eq.refl (some eb603)) (And.intro (Eq.refl (some eb604)) (And.intro (Eq.refl (some eb606)) (And.intro (Eq.refl (some eb607)) (And.intro (Eq.refl (some eb608)) (And.intro (Eq.refl (some eb609)) (And.intro (Eq.refl (some eb611)) (And.intro (Eq.refl (some eb612)) (And.intro (Eq.refl (some eb613)) (And.intro (Eq.refl (some eb620)) (And.intro (Eq.refl (some eb621)) (And.intro (Eq.refl (some eb627)) (And.intro (Eq.refl (some eb630)) (And.intro (Eq.refl (some eb631)) (And.intro (Eq.refl (some eb632)) (And.intro (Eq.refl (some eb639)) (And.intro (Eq.refl (some eb642)) (And.intro (Eq.refl (some eb645)) (And.intro (Eq.refl (some eb646)) (And.intro (Eq.refl (some eb647)) (And.intro (Eq.refl (some eb648)) (And.intro (Eq.refl (some eb654)) (And.intro (Eq.refl (some eb655)) (And.intro (Eq.refl (some eb656)) (And.intro (Eq.refl (some eb657)) (And.intro (Eq.refl (some eb666)) (And.intro (Eq.refl (some eb669)) (And.intro (Eq.refl (some eb670)) (And.intro (Eq.refl (some eb673)) (And.intro (Eq.refl (some eb677)) (And.intro (Eq.refl (some eb679)) (And.intro (Eq.refl (some eb680)) (And.intro (Eq.refl (some eb683)) (And.intro (Eq.refl (some eb684)) (And.intro (Eq.refl (some eb685)) (And.intro (Eq.refl (some eb686)) (And.intro (Eq.refl (some eb692)) (And.intro (Eq.refl (some eb695)) (And.intro (Eq.refl (some eb704)) (And.intro (Eq.refl (some eb708)) (And.intro (Eq.refl (some eb711)) (And.intro (Eq.refl (some eb715)) (And.intro (Eq.refl (some eb717)) (And.intro (Eq.refl (some eb718)) (And.intro (Eq.refl (some eb721)) (And.intro (Eq.refl (some eb722)) (And.intro (Eq.refl (some eb723)) (And.intro (Eq.refl (some eb724)) (And.intro (Eq.refl (some eb730)) (And.intro (Eq.refl (some eb731)) (And.intro (Eq.refl (some eb733)) (And.intro (Eq.refl (some eb742)) (Eq.refl (some eb746))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem chunk6 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[750+k]? = lowerEarlyTerminalBounds06[k]? := by
  unfold lowerEarlyTerminalBounds

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]

  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05) (by simp only [List.length_append, length01, length02, length03, length04, length05]; omega)]

  simp only [List.length_append, length01, length02, length03, length04, length05]

  exact congrArg (fun j => lowerEarlyTerminalBounds06[j]?) (by omega)

private theorem selected6 :
  (lowerEarlyTerminalBounds06[0]? = some eb751) ∧
  (lowerEarlyTerminalBounds06[4]? = some eb755) ∧
  (lowerEarlyTerminalBounds06[6]? = some eb757) ∧
  (lowerEarlyTerminalBounds06[10]? = some eb761) ∧
  (lowerEarlyTerminalBounds06[14]? = some eb765) ∧
  (lowerEarlyTerminalBounds06[15]? = some eb766) ∧
  (lowerEarlyTerminalBounds06[20]? = some eb771) ∧
  (lowerEarlyTerminalBounds06[21]? = some eb772) ∧
  (lowerEarlyTerminalBounds06[22]? = some eb773) ∧
  (lowerEarlyTerminalBounds06[29]? = some eb780) ∧
  (lowerEarlyTerminalBounds06[32]? = some eb783) ∧
  (lowerEarlyTerminalBounds06[37]? = some eb788) ∧
  (lowerEarlyTerminalBounds06[41]? = some eb792) ∧
  (lowerEarlyTerminalBounds06[44]? = some eb795) ∧
  (lowerEarlyTerminalBounds06[46]? = some eb797) ∧
  (lowerEarlyTerminalBounds06[47]? = some eb798) ∧
  (lowerEarlyTerminalBounds06[50]? = some eb801) ∧
  (lowerEarlyTerminalBounds06[51]? = some eb802) ∧
  (lowerEarlyTerminalBounds06[52]? = some eb803) ∧
  (lowerEarlyTerminalBounds06[57]? = some eb808) ∧
  (lowerEarlyTerminalBounds06[59]? = some eb810) ∧
  (lowerEarlyTerminalBounds06[62]? = some eb813) ∧
  (lowerEarlyTerminalBounds06[64]? = some eb815) ∧
  (lowerEarlyTerminalBounds06[65]? = some eb816) ∧
  (lowerEarlyTerminalBounds06[68]? = some eb819) ∧
  (lowerEarlyTerminalBounds06[69]? = some eb820) ∧
  (lowerEarlyTerminalBounds06[70]? = some eb821) ∧
  (lowerEarlyTerminalBounds06[76]? = some eb827) ∧
  (lowerEarlyTerminalBounds06[79]? = some eb830) ∧
  (lowerEarlyTerminalBounds06[83]? = some eb834) ∧
  (lowerEarlyTerminalBounds06[87]? = some eb838) ∧
  (lowerEarlyTerminalBounds06[91]? = some eb842) ∧
  (lowerEarlyTerminalBounds06[94]? = some eb845) ∧
  (lowerEarlyTerminalBounds06[96]? = some eb847) ∧
  (lowerEarlyTerminalBounds06[100]? = some eb851) ∧
  (lowerEarlyTerminalBounds06[101]? = some eb852) ∧
  (lowerEarlyTerminalBounds06[106]? = some eb857) ∧
  (lowerEarlyTerminalBounds06[107]? = some eb858) ∧
  (lowerEarlyTerminalBounds06[108]? = some eb859) ∧
  (lowerEarlyTerminalBounds06[111]? = some eb862) ∧
  (lowerEarlyTerminalBounds06[113]? = some eb864) ∧
  (lowerEarlyTerminalBounds06[121]? = some eb872) ∧
  (lowerEarlyTerminalBounds06[125]? = some eb876) ∧
  (lowerEarlyTerminalBounds06[129]? = some eb880) ∧
  (lowerEarlyTerminalBounds06[134]? = some eb885) ∧
  (lowerEarlyTerminalBounds06[138]? = some eb889) ∧
  (lowerEarlyTerminalBounds06[139]? = some eb890) ∧
  (lowerEarlyTerminalBounds06[140]? = some eb891) ∧
  (lowerEarlyTerminalBounds06[143]? = some eb894) ∧
  (lowerEarlyTerminalBounds06[145]? = some eb896) := by
  exact And.intro (Eq.refl (some eb751)) (And.intro (Eq.refl (some eb755)) (And.intro (Eq.refl (some eb757)) (And.intro (Eq.refl (some eb761)) (And.intro (Eq.refl (some eb765)) (And.intro (Eq.refl (some eb766)) (And.intro (Eq.refl (some eb771)) (And.intro (Eq.refl (some eb772)) (And.intro (Eq.refl (some eb773)) (And.intro (Eq.refl (some eb780)) (And.intro (Eq.refl (some eb783)) (And.intro (Eq.refl (some eb788)) (And.intro (Eq.refl (some eb792)) (And.intro (Eq.refl (some eb795)) (And.intro (Eq.refl (some eb797)) (And.intro (Eq.refl (some eb798)) (And.intro (Eq.refl (some eb801)) (And.intro (Eq.refl (some eb802)) (And.intro (Eq.refl (some eb803)) (And.intro (Eq.refl (some eb808)) (And.intro (Eq.refl (some eb810)) (And.intro (Eq.refl (some eb813)) (And.intro (Eq.refl (some eb815)) (And.intro (Eq.refl (some eb816)) (And.intro (Eq.refl (some eb819)) (And.intro (Eq.refl (some eb820)) (And.intro (Eq.refl (some eb821)) (And.intro (Eq.refl (some eb827)) (And.intro (Eq.refl (some eb830)) (And.intro (Eq.refl (some eb834)) (And.intro (Eq.refl (some eb838)) (And.intro (Eq.refl (some eb842)) (And.intro (Eq.refl (some eb845)) (And.intro (Eq.refl (some eb847)) (And.intro (Eq.refl (some eb851)) (And.intro (Eq.refl (some eb852)) (And.intro (Eq.refl (some eb857)) (And.intro (Eq.refl (some eb858)) (And.intro (Eq.refl (some eb859)) (And.intro (Eq.refl (some eb862)) (And.intro (Eq.refl (some eb864)) (And.intro (Eq.refl (some eb872)) (And.intro (Eq.refl (some eb876)) (And.intro (Eq.refl (some eb880)) (And.intro (Eq.refl (some eb885)) (And.intro (Eq.refl (some eb889)) (And.intro (Eq.refl (some eb890)) (And.intro (Eq.refl (some eb891)) (And.intro (Eq.refl (some eb894)) (Eq.refl (some eb896))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem chunk7 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[900+k]? = lowerEarlyTerminalBounds07[k]? := by
  unfold lowerEarlyTerminalBounds

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]

  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06]; omega)]

  simp only [List.length_append, length01, length02, length03, length04, length05, length06]

  exact congrArg (fun j => lowerEarlyTerminalBounds07[j]?) (by omega)

private theorem selected7 :
  (lowerEarlyTerminalBounds07[3]? = some eb904) ∧
  (lowerEarlyTerminalBounds07[7]? = some eb908) ∧
  (lowerEarlyTerminalBounds07[11]? = some eb912) ∧
  (lowerEarlyTerminalBounds07[13]? = some eb914) ∧
  (lowerEarlyTerminalBounds07[14]? = some eb915) ∧
  (lowerEarlyTerminalBounds07[17]? = some eb918) ∧
  (lowerEarlyTerminalBounds07[22]? = some eb923) ∧
  (lowerEarlyTerminalBounds07[26]? = some eb927) ∧
  (lowerEarlyTerminalBounds07[27]? = some eb928) ∧
  (lowerEarlyTerminalBounds07[28]? = some eb929) ∧
  (lowerEarlyTerminalBounds07[29]? = some eb930) ∧
  (lowerEarlyTerminalBounds07[36]? = some eb937) ∧
  (lowerEarlyTerminalBounds07[42]? = some eb943) ∧
  (lowerEarlyTerminalBounds07[47]? = some eb948) ∧
  (lowerEarlyTerminalBounds07[51]? = some eb952) ∧
  (lowerEarlyTerminalBounds07[59]? = some eb960) ∧
  (lowerEarlyTerminalBounds07[61]? = some eb962) ∧
  (lowerEarlyTerminalBounds07[67]? = some eb968) ∧
  (lowerEarlyTerminalBounds07[71]? = some eb972) ∧
  (lowerEarlyTerminalBounds07[72]? = some eb973) ∧
  (lowerEarlyTerminalBounds07[73]? = some eb974) ∧
  (lowerEarlyTerminalBounds07[74]? = some eb975) ∧
  (lowerEarlyTerminalBounds07[75]? = some eb976) ∧
  (lowerEarlyTerminalBounds07[82]? = some eb983) ∧
  (lowerEarlyTerminalBounds07[83]? = some eb984) ∧
  (lowerEarlyTerminalBounds07[85]? = some eb986) ∧
  (lowerEarlyTerminalBounds07[93]? = some eb994) ∧
  (lowerEarlyTerminalBounds07[95]? = some eb996) ∧
  (lowerEarlyTerminalBounds07[96]? = some eb997) ∧
  (lowerEarlyTerminalBounds07[99]? = some eb1000) ∧
  (lowerEarlyTerminalBounds07[105]? = some eb1006) ∧
  (lowerEarlyTerminalBounds07[109]? = some eb1010) ∧
  (lowerEarlyTerminalBounds07[110]? = some eb1011) ∧
  (lowerEarlyTerminalBounds07[111]? = some eb1012) ∧
  (lowerEarlyTerminalBounds07[112]? = some eb1013) ∧
  (lowerEarlyTerminalBounds07[113]? = some eb1014) ∧
  (lowerEarlyTerminalBounds07[120]? = some eb1021) ∧
  (lowerEarlyTerminalBounds07[126]? = some eb1027) ∧
  (lowerEarlyTerminalBounds07[131]? = some eb1032) ∧
  (lowerEarlyTerminalBounds07[135]? = some eb1036) ∧
  (lowerEarlyTerminalBounds07[136]? = some eb1037) ∧
  (lowerEarlyTerminalBounds07[143]? = some eb1044) ∧
  (lowerEarlyTerminalBounds07[145]? = some eb1046) ∧
  (lowerEarlyTerminalBounds07[146]? = some eb1047) ∧
  (lowerEarlyTerminalBounds07[149]? = some eb1050) := by
  exact And.intro (Eq.refl (some eb904)) (And.intro (Eq.refl (some eb908)) (And.intro (Eq.refl (some eb912)) (And.intro (Eq.refl (some eb914)) (And.intro (Eq.refl (some eb915)) (And.intro (Eq.refl (some eb918)) (And.intro (Eq.refl (some eb923)) (And.intro (Eq.refl (some eb927)) (And.intro (Eq.refl (some eb928)) (And.intro (Eq.refl (some eb929)) (And.intro (Eq.refl (some eb930)) (And.intro (Eq.refl (some eb937)) (And.intro (Eq.refl (some eb943)) (And.intro (Eq.refl (some eb948)) (And.intro (Eq.refl (some eb952)) (And.intro (Eq.refl (some eb960)) (And.intro (Eq.refl (some eb962)) (And.intro (Eq.refl (some eb968)) (And.intro (Eq.refl (some eb972)) (And.intro (Eq.refl (some eb973)) (And.intro (Eq.refl (some eb974)) (And.intro (Eq.refl (some eb975)) (And.intro (Eq.refl (some eb976)) (And.intro (Eq.refl (some eb983)) (And.intro (Eq.refl (some eb984)) (And.intro (Eq.refl (some eb986)) (And.intro (Eq.refl (some eb994)) (And.intro (Eq.refl (some eb996)) (And.intro (Eq.refl (some eb997)) (And.intro (Eq.refl (some eb1000)) (And.intro (Eq.refl (some eb1006)) (And.intro (Eq.refl (some eb1010)) (And.intro (Eq.refl (some eb1011)) (And.intro (Eq.refl (some eb1012)) (And.intro (Eq.refl (some eb1013)) (And.intro (Eq.refl (some eb1014)) (And.intro (Eq.refl (some eb1021)) (And.intro (Eq.refl (some eb1027)) (And.intro (Eq.refl (some eb1032)) (And.intro (Eq.refl (some eb1036)) (And.intro (Eq.refl (some eb1037)) (And.intro (Eq.refl (some eb1044)) (And.intro (Eq.refl (some eb1046)) (And.intro (Eq.refl (some eb1047)) (Eq.refl (some eb1050)))))))))))))))))))))))))))))))))))))))))))))

private theorem chunk8 (k : Nat) (hk : k < 150) :
    lowerEarlyTerminalBounds[1050+k]? = lowerEarlyTerminalBounds08[k]? := by
  unfold lowerEarlyTerminalBounds

  rw [List.getElem?_append_left (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]

  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]; omega)]

  simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07]

  exact congrArg (fun j => lowerEarlyTerminalBounds08[j]?) (by omega)

private theorem selected8 :
  (lowerEarlyTerminalBounds08[5]? = some eb1056) ∧
  (lowerEarlyTerminalBounds08[9]? = some eb1060) ∧
  (lowerEarlyTerminalBounds08[10]? = some eb1061) ∧
  (lowerEarlyTerminalBounds08[11]? = some eb1062) ∧
  (lowerEarlyTerminalBounds08[12]? = some eb1063) ∧
  (lowerEarlyTerminalBounds08[13]? = some eb1064) ∧
  (lowerEarlyTerminalBounds08[20]? = some eb1071) ∧
  (lowerEarlyTerminalBounds08[26]? = some eb1077) ∧
  (lowerEarlyTerminalBounds08[31]? = some eb1082) ∧
  (lowerEarlyTerminalBounds08[35]? = some eb1086) ∧
  (lowerEarlyTerminalBounds08[36]? = some eb1087) ∧
  (lowerEarlyTerminalBounds08[41]? = some eb1092) ∧
  (lowerEarlyTerminalBounds08[43]? = some eb1094) ∧
  (lowerEarlyTerminalBounds08[44]? = some eb1095) ∧
  (lowerEarlyTerminalBounds08[47]? = some eb1098) ∧
  (lowerEarlyTerminalBounds08[48]? = some eb1099) ∧
  (lowerEarlyTerminalBounds08[49]? = some eb1100) ∧
  (lowerEarlyTerminalBounds08[53]? = some eb1104) ∧
  (lowerEarlyTerminalBounds08[54]? = some eb1105) ∧
  (lowerEarlyTerminalBounds08[55]? = some eb1106) ∧
  (lowerEarlyTerminalBounds08[56]? = some eb1107) ∧
  (lowerEarlyTerminalBounds08[57]? = some eb1108) ∧
  (lowerEarlyTerminalBounds08[65]? = some eb1116) ∧
  (lowerEarlyTerminalBounds08[70]? = some eb1121) ∧
  (lowerEarlyTerminalBounds08[71]? = some eb1122) ∧
  (lowerEarlyTerminalBounds08[72]? = some eb1123) ∧
  (lowerEarlyTerminalBounds08[73]? = some eb1124) ∧
  (lowerEarlyTerminalBounds08[74]? = some eb1125) ∧
  (lowerEarlyTerminalBounds08[76]? = some eb1127) ∧
  (lowerEarlyTerminalBounds08[80]? = some eb1131) ∧
  (lowerEarlyTerminalBounds08[84]? = some eb1135) ∧
  (lowerEarlyTerminalBounds08[85]? = some eb1136) ∧
  (lowerEarlyTerminalBounds08[90]? = some eb1141) ∧
  (lowerEarlyTerminalBounds08[91]? = some eb1142) ∧
  (lowerEarlyTerminalBounds08[92]? = some eb1143) ∧
  (lowerEarlyTerminalBounds08[93]? = some eb1144) ∧
  (lowerEarlyTerminalBounds08[95]? = some eb1146) ∧
  (lowerEarlyTerminalBounds08[97]? = some eb1148) ∧
  (lowerEarlyTerminalBounds08[106]? = some eb1157) ∧
  (lowerEarlyTerminalBounds08[109]? = some eb1160) ∧
  (lowerEarlyTerminalBounds08[113]? = some eb1164) ∧
  (lowerEarlyTerminalBounds08[118]? = some eb1169) ∧
  (lowerEarlyTerminalBounds08[123]? = some eb1174) := by
  exact And.intro (Eq.refl (some eb1056)) (And.intro (Eq.refl (some eb1060)) (And.intro (Eq.refl (some eb1061)) (And.intro (Eq.refl (some eb1062)) (And.intro (Eq.refl (some eb1063)) (And.intro (Eq.refl (some eb1064)) (And.intro (Eq.refl (some eb1071)) (And.intro (Eq.refl (some eb1077)) (And.intro (Eq.refl (some eb1082)) (And.intro (Eq.refl (some eb1086)) (And.intro (Eq.refl (some eb1087)) (And.intro (Eq.refl (some eb1092)) (And.intro (Eq.refl (some eb1094)) (And.intro (Eq.refl (some eb1095)) (And.intro (Eq.refl (some eb1098)) (And.intro (Eq.refl (some eb1099)) (And.intro (Eq.refl (some eb1100)) (And.intro (Eq.refl (some eb1104)) (And.intro (Eq.refl (some eb1105)) (And.intro (Eq.refl (some eb1106)) (And.intro (Eq.refl (some eb1107)) (And.intro (Eq.refl (some eb1108)) (And.intro (Eq.refl (some eb1116)) (And.intro (Eq.refl (some eb1121)) (And.intro (Eq.refl (some eb1122)) (And.intro (Eq.refl (some eb1123)) (And.intro (Eq.refl (some eb1124)) (And.intro (Eq.refl (some eb1125)) (And.intro (Eq.refl (some eb1127)) (And.intro (Eq.refl (some eb1131)) (And.intro (Eq.refl (some eb1135)) (And.intro (Eq.refl (some eb1136)) (And.intro (Eq.refl (some eb1141)) (And.intro (Eq.refl (some eb1142)) (And.intro (Eq.refl (some eb1143)) (And.intro (Eq.refl (some eb1144)) (And.intro (Eq.refl (some eb1146)) (And.intro (Eq.refl (some eb1148)) (And.intro (Eq.refl (some eb1157)) (And.intro (Eq.refl (some eb1160)) (And.intro (Eq.refl (some eb1164)) (And.intro (Eq.refl (some eb1169)) (Eq.refl (some eb1174)))))))))))))))))))))))))))))))))))))))))))

end LookupFast17

private theorem lookup1 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1 = eb1 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 0 (by omega)).trans LookupFast17.selected1.1

private theorem lookup2 : lowerEarlyTerminalBound lowerEarlyTerminalState1 2 = eb2 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 1 (by omega)).trans LookupFast17.selected1.2.1

private theorem lookup6 : lowerEarlyTerminalBound lowerEarlyTerminalState1 6 = eb6 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 5 (by omega)).trans LookupFast17.selected1.2.2.1

private theorem lookup7 : lowerEarlyTerminalBound lowerEarlyTerminalState1 7 = eb7 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 6 (by omega)).trans LookupFast17.selected1.2.2.2.1

private theorem lookup8 : lowerEarlyTerminalBound lowerEarlyTerminalState1 8 = eb8 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 7 (by omega)).trans LookupFast17.selected1.2.2.2.2.1

private theorem lookup12 : lowerEarlyTerminalBound lowerEarlyTerminalState1 12 = eb12 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 11 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.1

private theorem lookup13 : lowerEarlyTerminalBound lowerEarlyTerminalState1 13 = eb13 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 12 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.1

private theorem lookup14 : lowerEarlyTerminalBound lowerEarlyTerminalState1 14 = eb14 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 13 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.1

private theorem lookup15 : lowerEarlyTerminalBound lowerEarlyTerminalState1 15 = eb15 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 14 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.1

private theorem lookup23 : lowerEarlyTerminalBound lowerEarlyTerminalState1 23 = eb23 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 22 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.1

private theorem lookup27 : lowerEarlyTerminalBound lowerEarlyTerminalState1 27 = eb27 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 26 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup28 : lowerEarlyTerminalBound lowerEarlyTerminalState1 28 = eb28 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 27 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup33 : lowerEarlyTerminalBound lowerEarlyTerminalState1 33 = eb33 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 32 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup35 : lowerEarlyTerminalBound lowerEarlyTerminalState1 35 = eb35 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 34 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup36 : lowerEarlyTerminalBound lowerEarlyTerminalState1 36 = eb36 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 35 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup39 : lowerEarlyTerminalBound lowerEarlyTerminalState1 39 = eb39 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 38 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup43 : lowerEarlyTerminalBound lowerEarlyTerminalState1 43 = eb43 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 42 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup45 : lowerEarlyTerminalBound lowerEarlyTerminalState1 45 = eb45 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 44 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup50 : lowerEarlyTerminalBound lowerEarlyTerminalState1 50 = eb50 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 49 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup51 : lowerEarlyTerminalBound lowerEarlyTerminalState1 51 = eb51 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 50 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup52 : lowerEarlyTerminalBound lowerEarlyTerminalState1 52 = eb52 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 51 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup53 : lowerEarlyTerminalBound lowerEarlyTerminalState1 53 = eb53 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 52 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup60 : lowerEarlyTerminalBound lowerEarlyTerminalState1 60 = eb60 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 59 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup61 : lowerEarlyTerminalBound lowerEarlyTerminalState1 61 = eb61 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 60 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup66 : lowerEarlyTerminalBound lowerEarlyTerminalState1 66 = eb66 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 65 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup69 : lowerEarlyTerminalBound lowerEarlyTerminalState1 69 = eb69 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 68 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup70 : lowerEarlyTerminalBound lowerEarlyTerminalState1 70 = eb70 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 69 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup71 : lowerEarlyTerminalBound lowerEarlyTerminalState1 71 = eb71 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 70 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup75 : lowerEarlyTerminalBound lowerEarlyTerminalState1 75 = eb75 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 74 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup76 : lowerEarlyTerminalBound lowerEarlyTerminalState1 76 = eb76 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 75 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup84 : lowerEarlyTerminalBound lowerEarlyTerminalState1 84 = eb84 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 83 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup86 : lowerEarlyTerminalBound lowerEarlyTerminalState1 86 = eb86 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 85 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup87 : lowerEarlyTerminalBound lowerEarlyTerminalState1 87 = eb87 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 86 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup90 : lowerEarlyTerminalBound lowerEarlyTerminalState1 90 = eb90 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 89 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup96 : lowerEarlyTerminalBound lowerEarlyTerminalState1 96 = eb96 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 95 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup100 : lowerEarlyTerminalBound lowerEarlyTerminalState1 100 = eb100 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 99 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup101 : lowerEarlyTerminalBound lowerEarlyTerminalState1 101 = eb101 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 100 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup102 : lowerEarlyTerminalBound lowerEarlyTerminalState1 102 = eb102 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 101 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup103 : lowerEarlyTerminalBound lowerEarlyTerminalState1 103 = eb103 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 102 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup105 : lowerEarlyTerminalBound lowerEarlyTerminalState1 105 = eb105 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 104 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup106 : lowerEarlyTerminalBound lowerEarlyTerminalState1 106 = eb106 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 105 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup107 : lowerEarlyTerminalBound lowerEarlyTerminalState1 107 = eb107 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 106 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup109 : lowerEarlyTerminalBound lowerEarlyTerminalState1 109 = eb109 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 108 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup110 : lowerEarlyTerminalBound lowerEarlyTerminalState1 110 = eb110 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 109 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup114 : lowerEarlyTerminalBound lowerEarlyTerminalState1 114 = eb114 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 113 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup115 : lowerEarlyTerminalBound lowerEarlyTerminalState1 115 = eb115 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 114 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup116 : lowerEarlyTerminalBound lowerEarlyTerminalState1 116 = eb116 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 115 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup118 : lowerEarlyTerminalBound lowerEarlyTerminalState1 118 = eb118 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 117 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup119 : lowerEarlyTerminalBound lowerEarlyTerminalState1 119 = eb119 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 118 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup120 : lowerEarlyTerminalBound lowerEarlyTerminalState1 120 = eb120 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 119 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup121 : lowerEarlyTerminalBound lowerEarlyTerminalState1 121 = eb121 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 120 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup122 : lowerEarlyTerminalBound lowerEarlyTerminalState1 122 = eb122 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 121 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup125 : lowerEarlyTerminalBound lowerEarlyTerminalState1 125 = eb125 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 124 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup127 : lowerEarlyTerminalBound lowerEarlyTerminalState1 127 = eb127 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 126 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup129 : lowerEarlyTerminalBound lowerEarlyTerminalState1 129 = eb129 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 128 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup131 : lowerEarlyTerminalBound lowerEarlyTerminalState1 131 = eb131 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 130 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup134 : lowerEarlyTerminalBound lowerEarlyTerminalState1 134 = eb134 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 133 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup137 : lowerEarlyTerminalBound lowerEarlyTerminalState1 137 = eb137 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 136 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup140 : lowerEarlyTerminalBound lowerEarlyTerminalState1 140 = eb140 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 139 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup144 : lowerEarlyTerminalBound lowerEarlyTerminalState1 144 = eb144 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 143 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup145 : lowerEarlyTerminalBound lowerEarlyTerminalState1 145 = eb145 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 144 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup146 : lowerEarlyTerminalBound lowerEarlyTerminalState1 146 = eb146 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 145 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup147 : lowerEarlyTerminalBound lowerEarlyTerminalState1 147 = eb147 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 146 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup150 : lowerEarlyTerminalBound lowerEarlyTerminalState1 150 = eb150 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 149 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup154 : lowerEarlyTerminalBound lowerEarlyTerminalState1 154 = eb154 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 3 (by omega)).trans LookupFast17.selected2.1

private theorem lookup159 : lowerEarlyTerminalBound lowerEarlyTerminalState1 159 = eb159 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 8 (by omega)).trans LookupFast17.selected2.2.1

private theorem lookup160 : lowerEarlyTerminalBound lowerEarlyTerminalState1 160 = eb160 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 9 (by omega)).trans LookupFast17.selected2.2.2.1

private theorem lookup162 : lowerEarlyTerminalBound lowerEarlyTerminalState1 162 = eb162 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 11 (by omega)).trans LookupFast17.selected2.2.2.2.1

private theorem lookup163 : lowerEarlyTerminalBound lowerEarlyTerminalState1 163 = eb163 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 12 (by omega)).trans LookupFast17.selected2.2.2.2.2.1

private theorem lookup164 : lowerEarlyTerminalBound lowerEarlyTerminalState1 164 = eb164 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 13 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.1

private theorem lookup165 : lowerEarlyTerminalBound lowerEarlyTerminalState1 165 = eb165 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 14 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.1

private theorem lookup170 : lowerEarlyTerminalBound lowerEarlyTerminalState1 170 = eb170 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 19 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.1

private theorem lookup171 : lowerEarlyTerminalBound lowerEarlyTerminalState1 171 = eb171 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 20 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.1

private theorem lookup172 : lowerEarlyTerminalBound lowerEarlyTerminalState1 172 = eb172 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 21 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.1

private theorem lookup173 : lowerEarlyTerminalBound lowerEarlyTerminalState1 173 = eb173 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 22 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup174 : lowerEarlyTerminalBound lowerEarlyTerminalState1 174 = eb174 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 23 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup183 : lowerEarlyTerminalBound lowerEarlyTerminalState1 183 = eb183 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 32 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup186 : lowerEarlyTerminalBound lowerEarlyTerminalState1 186 = eb186 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 35 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup187 : lowerEarlyTerminalBound lowerEarlyTerminalState1 187 = eb187 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 36 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup188 : lowerEarlyTerminalBound lowerEarlyTerminalState1 188 = eb188 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 37 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup193 : lowerEarlyTerminalBound lowerEarlyTerminalState1 193 = eb193 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 42 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup194 : lowerEarlyTerminalBound lowerEarlyTerminalState1 194 = eb194 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 43 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup195 : lowerEarlyTerminalBound lowerEarlyTerminalState1 195 = eb195 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 44 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup196 : lowerEarlyTerminalBound lowerEarlyTerminalState1 196 = eb196 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 45 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup197 : lowerEarlyTerminalBound lowerEarlyTerminalState1 197 = eb197 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 46 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup199 : lowerEarlyTerminalBound lowerEarlyTerminalState1 199 = eb199 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 48 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup203 : lowerEarlyTerminalBound lowerEarlyTerminalState1 203 = eb203 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 52 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup207 : lowerEarlyTerminalBound lowerEarlyTerminalState1 207 = eb207 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 56 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup208 : lowerEarlyTerminalBound lowerEarlyTerminalState1 208 = eb208 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 57 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup214 : lowerEarlyTerminalBound lowerEarlyTerminalState1 214 = eb214 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 63 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup215 : lowerEarlyTerminalBound lowerEarlyTerminalState1 215 = eb215 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 64 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup216 : lowerEarlyTerminalBound lowerEarlyTerminalState1 216 = eb216 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 65 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup217 : lowerEarlyTerminalBound lowerEarlyTerminalState1 217 = eb217 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 66 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup218 : lowerEarlyTerminalBound lowerEarlyTerminalState1 218 = eb218 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 67 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup223 : lowerEarlyTerminalBound lowerEarlyTerminalState1 223 = eb223 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 72 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup226 : lowerEarlyTerminalBound lowerEarlyTerminalState1 226 = eb226 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 75 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup229 : lowerEarlyTerminalBound lowerEarlyTerminalState1 229 = eb229 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 78 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup230 : lowerEarlyTerminalBound lowerEarlyTerminalState1 230 = eb230 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 79 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup231 : lowerEarlyTerminalBound lowerEarlyTerminalState1 231 = eb231 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 80 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup235 : lowerEarlyTerminalBound lowerEarlyTerminalState1 235 = eb235 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 84 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup236 : lowerEarlyTerminalBound lowerEarlyTerminalState1 236 = eb236 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 85 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup241 : lowerEarlyTerminalBound lowerEarlyTerminalState1 241 = eb241 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 90 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup242 : lowerEarlyTerminalBound lowerEarlyTerminalState1 242 = eb242 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 91 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup243 : lowerEarlyTerminalBound lowerEarlyTerminalState1 243 = eb243 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 92 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup244 : lowerEarlyTerminalBound lowerEarlyTerminalState1 244 = eb244 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 93 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup245 : lowerEarlyTerminalBound lowerEarlyTerminalState1 245 = eb245 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 94 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup247 : lowerEarlyTerminalBound lowerEarlyTerminalState1 247 = eb247 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 96 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup251 : lowerEarlyTerminalBound lowerEarlyTerminalState1 251 = eb251 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 100 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup252 : lowerEarlyTerminalBound lowerEarlyTerminalState1 252 = eb252 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 101 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup257 : lowerEarlyTerminalBound lowerEarlyTerminalState1 257 = eb257 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 106 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup258 : lowerEarlyTerminalBound lowerEarlyTerminalState1 258 = eb258 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 107 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup259 : lowerEarlyTerminalBound lowerEarlyTerminalState1 259 = eb259 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 108 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup260 : lowerEarlyTerminalBound lowerEarlyTerminalState1 260 = eb260 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 109 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup261 : lowerEarlyTerminalBound lowerEarlyTerminalState1 261 = eb261 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 110 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup268 : lowerEarlyTerminalBound lowerEarlyTerminalState1 268 = eb268 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 117 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup272 : lowerEarlyTerminalBound lowerEarlyTerminalState1 272 = eb272 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 121 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup280 : lowerEarlyTerminalBound lowerEarlyTerminalState1 280 = eb280 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 129 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup282 : lowerEarlyTerminalBound lowerEarlyTerminalState1 282 = eb282 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 131 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup283 : lowerEarlyTerminalBound lowerEarlyTerminalState1 283 = eb283 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 132 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup286 : lowerEarlyTerminalBound lowerEarlyTerminalState1 286 = eb286 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 135 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup292 : lowerEarlyTerminalBound lowerEarlyTerminalState1 292 = eb292 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 141 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup296 : lowerEarlyTerminalBound lowerEarlyTerminalState1 296 = eb296 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 145 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup297 : lowerEarlyTerminalBound lowerEarlyTerminalState1 297 = eb297 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 146 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup298 : lowerEarlyTerminalBound lowerEarlyTerminalState1 298 = eb298 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 147 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup299 : lowerEarlyTerminalBound lowerEarlyTerminalState1 299 = eb299 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 148 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup300 : lowerEarlyTerminalBound lowerEarlyTerminalState1 300 = eb300 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 149 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup301 : lowerEarlyTerminalBound lowerEarlyTerminalState1 301 = eb301 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 0 (by omega)).trans LookupFast17.selected3.1

private theorem lookup308 : lowerEarlyTerminalBound lowerEarlyTerminalState1 308 = eb308 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 7 (by omega)).trans LookupFast17.selected3.2.1

private theorem lookup312 : lowerEarlyTerminalBound lowerEarlyTerminalState1 312 = eb312 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 11 (by omega)).trans LookupFast17.selected3.2.2.1

private theorem lookup318 : lowerEarlyTerminalBound lowerEarlyTerminalState1 318 = eb318 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 17 (by omega)).trans LookupFast17.selected3.2.2.2.1

private theorem lookup320 : lowerEarlyTerminalBound lowerEarlyTerminalState1 320 = eb320 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 19 (by omega)).trans LookupFast17.selected3.2.2.2.2.1

private theorem lookup321 : lowerEarlyTerminalBound lowerEarlyTerminalState1 321 = eb321 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 20 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.1

private theorem lookup324 : lowerEarlyTerminalBound lowerEarlyTerminalState1 324 = eb324 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 23 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.1

private theorem lookup325 : lowerEarlyTerminalBound lowerEarlyTerminalState1 325 = eb325 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 24 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.1

private theorem lookup327 : lowerEarlyTerminalBound lowerEarlyTerminalState1 327 = eb327 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 26 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.1

private theorem lookup328 : lowerEarlyTerminalBound lowerEarlyTerminalState1 328 = eb328 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 27 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.1

private theorem lookup329 : lowerEarlyTerminalBound lowerEarlyTerminalState1 329 = eb329 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 28 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup331 : lowerEarlyTerminalBound lowerEarlyTerminalState1 331 = eb331 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 30 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup332 : lowerEarlyTerminalBound lowerEarlyTerminalState1 332 = eb332 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 31 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup333 : lowerEarlyTerminalBound lowerEarlyTerminalState1 333 = eb333 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 32 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup334 : lowerEarlyTerminalBound lowerEarlyTerminalState1 334 = eb334 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 33 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup335 : lowerEarlyTerminalBound lowerEarlyTerminalState1 335 = eb335 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 34 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup336 : lowerEarlyTerminalBound lowerEarlyTerminalState1 336 = eb336 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 35 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup337 : lowerEarlyTerminalBound lowerEarlyTerminalState1 337 = eb337 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 36 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup338 : lowerEarlyTerminalBound lowerEarlyTerminalState1 338 = eb338 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 37 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup340 : lowerEarlyTerminalBound lowerEarlyTerminalState1 340 = eb340 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 39 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup341 : lowerEarlyTerminalBound lowerEarlyTerminalState1 341 = eb341 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 40 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup342 : lowerEarlyTerminalBound lowerEarlyTerminalState1 342 = eb342 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 41 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup345 : lowerEarlyTerminalBound lowerEarlyTerminalState1 345 = eb345 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 44 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup346 : lowerEarlyTerminalBound lowerEarlyTerminalState1 346 = eb346 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 45 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup347 : lowerEarlyTerminalBound lowerEarlyTerminalState1 347 = eb347 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 46 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup348 : lowerEarlyTerminalBound lowerEarlyTerminalState1 348 = eb348 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 47 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup349 : lowerEarlyTerminalBound lowerEarlyTerminalState1 349 = eb349 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 48 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup350 : lowerEarlyTerminalBound lowerEarlyTerminalState1 350 = eb350 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 49 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup355 : lowerEarlyTerminalBound lowerEarlyTerminalState1 355 = eb355 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 54 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup356 : lowerEarlyTerminalBound lowerEarlyTerminalState1 356 = eb356 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 55 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup357 : lowerEarlyTerminalBound lowerEarlyTerminalState1 357 = eb357 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 56 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup358 : lowerEarlyTerminalBound lowerEarlyTerminalState1 358 = eb358 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 57 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup359 : lowerEarlyTerminalBound lowerEarlyTerminalState1 359 = eb359 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 58 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup360 : lowerEarlyTerminalBound lowerEarlyTerminalState1 360 = eb360 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 59 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup363 : lowerEarlyTerminalBound lowerEarlyTerminalState1 363 = eb363 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 62 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup366 : lowerEarlyTerminalBound lowerEarlyTerminalState1 366 = eb366 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 65 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup370 : lowerEarlyTerminalBound lowerEarlyTerminalState1 370 = eb370 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 69 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup375 : lowerEarlyTerminalBound lowerEarlyTerminalState1 375 = eb375 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 74 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup376 : lowerEarlyTerminalBound lowerEarlyTerminalState1 376 = eb376 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 75 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup380 : lowerEarlyTerminalBound lowerEarlyTerminalState1 380 = eb380 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 79 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup382 : lowerEarlyTerminalBound lowerEarlyTerminalState1 382 = eb382 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 81 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup383 : lowerEarlyTerminalBound lowerEarlyTerminalState1 383 = eb383 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 82 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup384 : lowerEarlyTerminalBound lowerEarlyTerminalState1 384 = eb384 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 83 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup385 : lowerEarlyTerminalBound lowerEarlyTerminalState1 385 = eb385 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 84 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup386 : lowerEarlyTerminalBound lowerEarlyTerminalState1 386 = eb386 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 85 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup387 : lowerEarlyTerminalBound lowerEarlyTerminalState1 387 = eb387 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 86 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup388 : lowerEarlyTerminalBound lowerEarlyTerminalState1 388 = eb388 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 87 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup389 : lowerEarlyTerminalBound lowerEarlyTerminalState1 389 = eb389 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 88 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup390 : lowerEarlyTerminalBound lowerEarlyTerminalState1 390 = eb390 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 89 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup391 : lowerEarlyTerminalBound lowerEarlyTerminalState1 391 = eb391 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 90 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup392 : lowerEarlyTerminalBound lowerEarlyTerminalState1 392 = eb392 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 91 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup393 : lowerEarlyTerminalBound lowerEarlyTerminalState1 393 = eb393 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 92 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup394 : lowerEarlyTerminalBound lowerEarlyTerminalState1 394 = eb394 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 93 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup395 : lowerEarlyTerminalBound lowerEarlyTerminalState1 395 = eb395 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 94 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup396 : lowerEarlyTerminalBound lowerEarlyTerminalState1 396 = eb396 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 95 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup397 : lowerEarlyTerminalBound lowerEarlyTerminalState1 397 = eb397 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 96 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup398 : lowerEarlyTerminalBound lowerEarlyTerminalState1 398 = eb398 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 97 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup399 : lowerEarlyTerminalBound lowerEarlyTerminalState1 399 = eb399 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 98 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup402 : lowerEarlyTerminalBound lowerEarlyTerminalState1 402 = eb402 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 101 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup403 : lowerEarlyTerminalBound lowerEarlyTerminalState1 403 = eb403 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 102 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup404 : lowerEarlyTerminalBound lowerEarlyTerminalState1 404 = eb404 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 103 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup405 : lowerEarlyTerminalBound lowerEarlyTerminalState1 405 = eb405 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 104 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup406 : lowerEarlyTerminalBound lowerEarlyTerminalState1 406 = eb406 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 105 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup408 : lowerEarlyTerminalBound lowerEarlyTerminalState1 408 = eb408 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 107 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup411 : lowerEarlyTerminalBound lowerEarlyTerminalState1 411 = eb411 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 110 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup412 : lowerEarlyTerminalBound lowerEarlyTerminalState1 412 = eb412 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 111 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup414 : lowerEarlyTerminalBound lowerEarlyTerminalState1 414 = eb414 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 113 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup415 : lowerEarlyTerminalBound lowerEarlyTerminalState1 415 = eb415 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 114 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup416 : lowerEarlyTerminalBound lowerEarlyTerminalState1 416 = eb416 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 115 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup419 : lowerEarlyTerminalBound lowerEarlyTerminalState1 419 = eb419 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 118 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup420 : lowerEarlyTerminalBound lowerEarlyTerminalState1 420 = eb420 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 119 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup422 : lowerEarlyTerminalBound lowerEarlyTerminalState1 422 = eb422 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 121 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup424 : lowerEarlyTerminalBound lowerEarlyTerminalState1 424 = eb424 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 123 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup425 : lowerEarlyTerminalBound lowerEarlyTerminalState1 425 = eb425 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 124 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup426 : lowerEarlyTerminalBound lowerEarlyTerminalState1 426 = eb426 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 125 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup427 : lowerEarlyTerminalBound lowerEarlyTerminalState1 427 = eb427 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 126 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup431 : lowerEarlyTerminalBound lowerEarlyTerminalState1 431 = eb431 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 130 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup432 : lowerEarlyTerminalBound lowerEarlyTerminalState1 432 = eb432 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 131 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup433 : lowerEarlyTerminalBound lowerEarlyTerminalState1 433 = eb433 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 132 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup434 : lowerEarlyTerminalBound lowerEarlyTerminalState1 434 = eb434 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 133 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup435 : lowerEarlyTerminalBound lowerEarlyTerminalState1 435 = eb435 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 134 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup436 : lowerEarlyTerminalBound lowerEarlyTerminalState1 436 = eb436 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 135 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup437 : lowerEarlyTerminalBound lowerEarlyTerminalState1 437 = eb437 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 136 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup439 : lowerEarlyTerminalBound lowerEarlyTerminalState1 439 = eb439 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 138 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup440 : lowerEarlyTerminalBound lowerEarlyTerminalState1 440 = eb440 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 139 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup441 : lowerEarlyTerminalBound lowerEarlyTerminalState1 441 = eb441 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 140 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup443 : lowerEarlyTerminalBound lowerEarlyTerminalState1 443 = eb443 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 142 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup446 : lowerEarlyTerminalBound lowerEarlyTerminalState1 446 = eb446 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 145 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup447 : lowerEarlyTerminalBound lowerEarlyTerminalState1 447 = eb447 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 146 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup449 : lowerEarlyTerminalBound lowerEarlyTerminalState1 449 = eb449 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 148 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup450 : lowerEarlyTerminalBound lowerEarlyTerminalState1 450 = eb450 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 149 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup452 : lowerEarlyTerminalBound lowerEarlyTerminalState1 452 = eb452 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 1 (by omega)).trans LookupFast17.selected4.1

private theorem lookup454 : lowerEarlyTerminalBound lowerEarlyTerminalState1 454 = eb454 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 3 (by omega)).trans LookupFast17.selected4.2.1

private theorem lookup455 : lowerEarlyTerminalBound lowerEarlyTerminalState1 455 = eb455 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 4 (by omega)).trans LookupFast17.selected4.2.2.1

private theorem lookup456 : lowerEarlyTerminalBound lowerEarlyTerminalState1 456 = eb456 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 5 (by omega)).trans LookupFast17.selected4.2.2.2.1

private theorem lookup457 : lowerEarlyTerminalBound lowerEarlyTerminalState1 457 = eb457 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 6 (by omega)).trans LookupFast17.selected4.2.2.2.2.1

private theorem lookup460 : lowerEarlyTerminalBound lowerEarlyTerminalState1 460 = eb460 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 9 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.1

private theorem lookup461 : lowerEarlyTerminalBound lowerEarlyTerminalState1 461 = eb461 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 10 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.1

private theorem lookup462 : lowerEarlyTerminalBound lowerEarlyTerminalState1 462 = eb462 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 11 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.1

private theorem lookup463 : lowerEarlyTerminalBound lowerEarlyTerminalState1 463 = eb463 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 12 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.1

private theorem lookup464 : lowerEarlyTerminalBound lowerEarlyTerminalState1 464 = eb464 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 13 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.1

private theorem lookup466 : lowerEarlyTerminalBound lowerEarlyTerminalState1 466 = eb466 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 15 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup468 : lowerEarlyTerminalBound lowerEarlyTerminalState1 468 = eb468 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 17 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup469 : lowerEarlyTerminalBound lowerEarlyTerminalState1 469 = eb469 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 18 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup470 : lowerEarlyTerminalBound lowerEarlyTerminalState1 470 = eb470 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 19 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup471 : lowerEarlyTerminalBound lowerEarlyTerminalState1 471 = eb471 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 20 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup472 : lowerEarlyTerminalBound lowerEarlyTerminalState1 472 = eb472 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 21 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup473 : lowerEarlyTerminalBound lowerEarlyTerminalState1 473 = eb473 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 22 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup474 : lowerEarlyTerminalBound lowerEarlyTerminalState1 474 = eb474 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 23 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup475 : lowerEarlyTerminalBound lowerEarlyTerminalState1 475 = eb475 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 24 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup476 : lowerEarlyTerminalBound lowerEarlyTerminalState1 476 = eb476 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 25 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup477 : lowerEarlyTerminalBound lowerEarlyTerminalState1 477 = eb477 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 26 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup478 : lowerEarlyTerminalBound lowerEarlyTerminalState1 478 = eb478 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 27 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup479 : lowerEarlyTerminalBound lowerEarlyTerminalState1 479 = eb479 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 28 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup480 : lowerEarlyTerminalBound lowerEarlyTerminalState1 480 = eb480 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 29 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup481 : lowerEarlyTerminalBound lowerEarlyTerminalState1 481 = eb481 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 30 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup482 : lowerEarlyTerminalBound lowerEarlyTerminalState1 482 = eb482 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 31 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup483 : lowerEarlyTerminalBound lowerEarlyTerminalState1 483 = eb483 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 32 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup484 : lowerEarlyTerminalBound lowerEarlyTerminalState1 484 = eb484 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 33 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup485 : lowerEarlyTerminalBound lowerEarlyTerminalState1 485 = eb485 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 34 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup486 : lowerEarlyTerminalBound lowerEarlyTerminalState1 486 = eb486 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 35 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup487 : lowerEarlyTerminalBound lowerEarlyTerminalState1 487 = eb487 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 36 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup488 : lowerEarlyTerminalBound lowerEarlyTerminalState1 488 = eb488 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 37 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup490 : lowerEarlyTerminalBound lowerEarlyTerminalState1 490 = eb490 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 39 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup491 : lowerEarlyTerminalBound lowerEarlyTerminalState1 491 = eb491 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 40 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup494 : lowerEarlyTerminalBound lowerEarlyTerminalState1 494 = eb494 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 43 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup495 : lowerEarlyTerminalBound lowerEarlyTerminalState1 495 = eb495 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 44 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup496 : lowerEarlyTerminalBound lowerEarlyTerminalState1 496 = eb496 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 45 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup497 : lowerEarlyTerminalBound lowerEarlyTerminalState1 497 = eb497 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 46 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup498 : lowerEarlyTerminalBound lowerEarlyTerminalState1 498 = eb498 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 47 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup499 : lowerEarlyTerminalBound lowerEarlyTerminalState1 499 = eb499 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 48 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup500 : lowerEarlyTerminalBound lowerEarlyTerminalState1 500 = eb500 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 49 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup501 : lowerEarlyTerminalBound lowerEarlyTerminalState1 501 = eb501 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 50 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup502 : lowerEarlyTerminalBound lowerEarlyTerminalState1 502 = eb502 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 51 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup503 : lowerEarlyTerminalBound lowerEarlyTerminalState1 503 = eb503 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 52 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup504 : lowerEarlyTerminalBound lowerEarlyTerminalState1 504 = eb504 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 53 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup505 : lowerEarlyTerminalBound lowerEarlyTerminalState1 505 = eb505 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 54 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup506 : lowerEarlyTerminalBound lowerEarlyTerminalState1 506 = eb506 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 55 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup507 : lowerEarlyTerminalBound lowerEarlyTerminalState1 507 = eb507 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 56 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup510 : lowerEarlyTerminalBound lowerEarlyTerminalState1 510 = eb510 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 59 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup512 : lowerEarlyTerminalBound lowerEarlyTerminalState1 512 = eb512 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 61 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup513 : lowerEarlyTerminalBound lowerEarlyTerminalState1 513 = eb513 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 62 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup516 : lowerEarlyTerminalBound lowerEarlyTerminalState1 516 = eb516 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 65 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup519 : lowerEarlyTerminalBound lowerEarlyTerminalState1 519 = eb519 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 68 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup522 : lowerEarlyTerminalBound lowerEarlyTerminalState1 522 = eb522 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 71 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup523 : lowerEarlyTerminalBound lowerEarlyTerminalState1 523 = eb523 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 72 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup524 : lowerEarlyTerminalBound lowerEarlyTerminalState1 524 = eb524 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 73 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup525 : lowerEarlyTerminalBound lowerEarlyTerminalState1 525 = eb525 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 74 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup526 : lowerEarlyTerminalBound lowerEarlyTerminalState1 526 = eb526 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 75 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup527 : lowerEarlyTerminalBound lowerEarlyTerminalState1 527 = eb527 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 76 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup528 : lowerEarlyTerminalBound lowerEarlyTerminalState1 528 = eb528 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 77 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup529 : lowerEarlyTerminalBound lowerEarlyTerminalState1 529 = eb529 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 78 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup531 : lowerEarlyTerminalBound lowerEarlyTerminalState1 531 = eb531 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 80 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup532 : lowerEarlyTerminalBound lowerEarlyTerminalState1 532 = eb532 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 81 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup534 : lowerEarlyTerminalBound lowerEarlyTerminalState1 534 = eb534 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 83 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup535 : lowerEarlyTerminalBound lowerEarlyTerminalState1 535 = eb535 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 84 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup536 : lowerEarlyTerminalBound lowerEarlyTerminalState1 536 = eb536 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 85 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup537 : lowerEarlyTerminalBound lowerEarlyTerminalState1 537 = eb537 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 86 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup538 : lowerEarlyTerminalBound lowerEarlyTerminalState1 538 = eb538 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 87 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup539 : lowerEarlyTerminalBound lowerEarlyTerminalState1 539 = eb539 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 88 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup540 : lowerEarlyTerminalBound lowerEarlyTerminalState1 540 = eb540 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 89 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup545 : lowerEarlyTerminalBound lowerEarlyTerminalState1 545 = eb545 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 94 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup547 : lowerEarlyTerminalBound lowerEarlyTerminalState1 547 = eb547 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 96 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup550 : lowerEarlyTerminalBound lowerEarlyTerminalState1 550 = eb550 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 99 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup553 : lowerEarlyTerminalBound lowerEarlyTerminalState1 553 = eb553 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 102 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup554 : lowerEarlyTerminalBound lowerEarlyTerminalState1 554 = eb554 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 103 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup555 : lowerEarlyTerminalBound lowerEarlyTerminalState1 555 = eb555 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 104 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup556 : lowerEarlyTerminalBound lowerEarlyTerminalState1 556 = eb556 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 105 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup557 : lowerEarlyTerminalBound lowerEarlyTerminalState1 557 = eb557 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 106 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup558 : lowerEarlyTerminalBound lowerEarlyTerminalState1 558 = eb558 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 107 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup559 : lowerEarlyTerminalBound lowerEarlyTerminalState1 559 = eb559 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 108 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup560 : lowerEarlyTerminalBound lowerEarlyTerminalState1 560 = eb560 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 109 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup564 : lowerEarlyTerminalBound lowerEarlyTerminalState1 564 = eb564 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 113 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup567 : lowerEarlyTerminalBound lowerEarlyTerminalState1 567 = eb567 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 116 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup568 : lowerEarlyTerminalBound lowerEarlyTerminalState1 568 = eb568 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 117 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup569 : lowerEarlyTerminalBound lowerEarlyTerminalState1 569 = eb569 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 118 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup570 : lowerEarlyTerminalBound lowerEarlyTerminalState1 570 = eb570 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 119 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup571 : lowerEarlyTerminalBound lowerEarlyTerminalState1 571 = eb571 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 120 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup573 : lowerEarlyTerminalBound lowerEarlyTerminalState1 573 = eb573 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 122 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup575 : lowerEarlyTerminalBound lowerEarlyTerminalState1 575 = eb575 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 124 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup576 : lowerEarlyTerminalBound lowerEarlyTerminalState1 576 = eb576 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 125 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup577 : lowerEarlyTerminalBound lowerEarlyTerminalState1 577 = eb577 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 126 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup578 : lowerEarlyTerminalBound lowerEarlyTerminalState1 578 = eb578 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 127 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup579 : lowerEarlyTerminalBound lowerEarlyTerminalState1 579 = eb579 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 128 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup581 : lowerEarlyTerminalBound lowerEarlyTerminalState1 581 = eb581 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 130 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup582 : lowerEarlyTerminalBound lowerEarlyTerminalState1 582 = eb582 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 131 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup583 : lowerEarlyTerminalBound lowerEarlyTerminalState1 583 = eb583 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 132 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup584 : lowerEarlyTerminalBound lowerEarlyTerminalState1 584 = eb584 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 133 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup585 : lowerEarlyTerminalBound lowerEarlyTerminalState1 585 = eb585 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 134 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup586 : lowerEarlyTerminalBound lowerEarlyTerminalState1 586 = eb586 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 135 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup590 : lowerEarlyTerminalBound lowerEarlyTerminalState1 590 = eb590 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 139 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup591 : lowerEarlyTerminalBound lowerEarlyTerminalState1 591 = eb591 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 140 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup592 : lowerEarlyTerminalBound lowerEarlyTerminalState1 592 = eb592 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 141 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup595 : lowerEarlyTerminalBound lowerEarlyTerminalState1 595 = eb595 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 144 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup598 : lowerEarlyTerminalBound lowerEarlyTerminalState1 598 = eb598 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 147 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup601 : lowerEarlyTerminalBound lowerEarlyTerminalState1 601 = eb601 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 0 (by omega)).trans LookupFast17.selected5.1

private theorem lookup603 : lowerEarlyTerminalBound lowerEarlyTerminalState1 603 = eb603 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 2 (by omega)).trans LookupFast17.selected5.2.1

private theorem lookup604 : lowerEarlyTerminalBound lowerEarlyTerminalState1 604 = eb604 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 3 (by omega)).trans LookupFast17.selected5.2.2.1

private theorem lookup606 : lowerEarlyTerminalBound lowerEarlyTerminalState1 606 = eb606 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 5 (by omega)).trans LookupFast17.selected5.2.2.2.1

private theorem lookup607 : lowerEarlyTerminalBound lowerEarlyTerminalState1 607 = eb607 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 6 (by omega)).trans LookupFast17.selected5.2.2.2.2.1

private theorem lookup608 : lowerEarlyTerminalBound lowerEarlyTerminalState1 608 = eb608 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 7 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.1

private theorem lookup609 : lowerEarlyTerminalBound lowerEarlyTerminalState1 609 = eb609 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 8 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.1

private theorem lookup611 : lowerEarlyTerminalBound lowerEarlyTerminalState1 611 = eb611 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 10 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.1

private theorem lookup612 : lowerEarlyTerminalBound lowerEarlyTerminalState1 612 = eb612 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 11 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.1

private theorem lookup613 : lowerEarlyTerminalBound lowerEarlyTerminalState1 613 = eb613 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 12 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.1

private theorem lookup620 : lowerEarlyTerminalBound lowerEarlyTerminalState1 620 = eb620 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 19 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup621 : lowerEarlyTerminalBound lowerEarlyTerminalState1 621 = eb621 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 20 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup627 : lowerEarlyTerminalBound lowerEarlyTerminalState1 627 = eb627 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 26 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup630 : lowerEarlyTerminalBound lowerEarlyTerminalState1 630 = eb630 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 29 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup631 : lowerEarlyTerminalBound lowerEarlyTerminalState1 631 = eb631 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 30 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup632 : lowerEarlyTerminalBound lowerEarlyTerminalState1 632 = eb632 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 31 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup639 : lowerEarlyTerminalBound lowerEarlyTerminalState1 639 = eb639 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 38 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup642 : lowerEarlyTerminalBound lowerEarlyTerminalState1 642 = eb642 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 41 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup645 : lowerEarlyTerminalBound lowerEarlyTerminalState1 645 = eb645 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 44 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup646 : lowerEarlyTerminalBound lowerEarlyTerminalState1 646 = eb646 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 45 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup647 : lowerEarlyTerminalBound lowerEarlyTerminalState1 647 = eb647 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 46 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup648 : lowerEarlyTerminalBound lowerEarlyTerminalState1 648 = eb648 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 47 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup654 : lowerEarlyTerminalBound lowerEarlyTerminalState1 654 = eb654 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 53 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup655 : lowerEarlyTerminalBound lowerEarlyTerminalState1 655 = eb655 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 54 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup656 : lowerEarlyTerminalBound lowerEarlyTerminalState1 656 = eb656 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 55 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup657 : lowerEarlyTerminalBound lowerEarlyTerminalState1 657 = eb657 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 56 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup666 : lowerEarlyTerminalBound lowerEarlyTerminalState1 666 = eb666 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 65 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup669 : lowerEarlyTerminalBound lowerEarlyTerminalState1 669 = eb669 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 68 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup670 : lowerEarlyTerminalBound lowerEarlyTerminalState1 670 = eb670 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 69 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup673 : lowerEarlyTerminalBound lowerEarlyTerminalState1 673 = eb673 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 72 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup677 : lowerEarlyTerminalBound lowerEarlyTerminalState1 677 = eb677 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 76 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup679 : lowerEarlyTerminalBound lowerEarlyTerminalState1 679 = eb679 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 78 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup680 : lowerEarlyTerminalBound lowerEarlyTerminalState1 680 = eb680 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 79 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup683 : lowerEarlyTerminalBound lowerEarlyTerminalState1 683 = eb683 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 82 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup684 : lowerEarlyTerminalBound lowerEarlyTerminalState1 684 = eb684 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 83 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup685 : lowerEarlyTerminalBound lowerEarlyTerminalState1 685 = eb685 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 84 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup686 : lowerEarlyTerminalBound lowerEarlyTerminalState1 686 = eb686 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 85 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup692 : lowerEarlyTerminalBound lowerEarlyTerminalState1 692 = eb692 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 91 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup695 : lowerEarlyTerminalBound lowerEarlyTerminalState1 695 = eb695 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 94 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup704 : lowerEarlyTerminalBound lowerEarlyTerminalState1 704 = eb704 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 103 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup708 : lowerEarlyTerminalBound lowerEarlyTerminalState1 708 = eb708 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 107 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup711 : lowerEarlyTerminalBound lowerEarlyTerminalState1 711 = eb711 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 110 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup715 : lowerEarlyTerminalBound lowerEarlyTerminalState1 715 = eb715 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 114 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup717 : lowerEarlyTerminalBound lowerEarlyTerminalState1 717 = eb717 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 116 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup718 : lowerEarlyTerminalBound lowerEarlyTerminalState1 718 = eb718 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 117 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup721 : lowerEarlyTerminalBound lowerEarlyTerminalState1 721 = eb721 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 120 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup722 : lowerEarlyTerminalBound lowerEarlyTerminalState1 722 = eb722 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 121 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup723 : lowerEarlyTerminalBound lowerEarlyTerminalState1 723 = eb723 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 122 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup724 : lowerEarlyTerminalBound lowerEarlyTerminalState1 724 = eb724 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 123 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup730 : lowerEarlyTerminalBound lowerEarlyTerminalState1 730 = eb730 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 129 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup731 : lowerEarlyTerminalBound lowerEarlyTerminalState1 731 = eb731 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 130 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup733 : lowerEarlyTerminalBound lowerEarlyTerminalState1 733 = eb733 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 132 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup742 : lowerEarlyTerminalBound lowerEarlyTerminalState1 742 = eb742 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 141 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup746 : lowerEarlyTerminalBound lowerEarlyTerminalState1 746 = eb746 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 145 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup751 : lowerEarlyTerminalBound lowerEarlyTerminalState1 751 = eb751 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 0 (by omega)).trans LookupFast17.selected6.1

private theorem lookup755 : lowerEarlyTerminalBound lowerEarlyTerminalState1 755 = eb755 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 4 (by omega)).trans LookupFast17.selected6.2.1

private theorem lookup757 : lowerEarlyTerminalBound lowerEarlyTerminalState1 757 = eb757 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 6 (by omega)).trans LookupFast17.selected6.2.2.1

private theorem lookup761 : lowerEarlyTerminalBound lowerEarlyTerminalState1 761 = eb761 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 10 (by omega)).trans LookupFast17.selected6.2.2.2.1

private theorem lookup765 : lowerEarlyTerminalBound lowerEarlyTerminalState1 765 = eb765 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 14 (by omega)).trans LookupFast17.selected6.2.2.2.2.1

private theorem lookup766 : lowerEarlyTerminalBound lowerEarlyTerminalState1 766 = eb766 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 15 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.1

private theorem lookup771 : lowerEarlyTerminalBound lowerEarlyTerminalState1 771 = eb771 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 20 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.1

private theorem lookup772 : lowerEarlyTerminalBound lowerEarlyTerminalState1 772 = eb772 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 21 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.1

private theorem lookup773 : lowerEarlyTerminalBound lowerEarlyTerminalState1 773 = eb773 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 22 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.1

private theorem lookup780 : lowerEarlyTerminalBound lowerEarlyTerminalState1 780 = eb780 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 29 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.1

private theorem lookup783 : lowerEarlyTerminalBound lowerEarlyTerminalState1 783 = eb783 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 32 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup788 : lowerEarlyTerminalBound lowerEarlyTerminalState1 788 = eb788 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 37 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup792 : lowerEarlyTerminalBound lowerEarlyTerminalState1 792 = eb792 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 41 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup795 : lowerEarlyTerminalBound lowerEarlyTerminalState1 795 = eb795 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 44 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup797 : lowerEarlyTerminalBound lowerEarlyTerminalState1 797 = eb797 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 46 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup798 : lowerEarlyTerminalBound lowerEarlyTerminalState1 798 = eb798 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 47 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup801 : lowerEarlyTerminalBound lowerEarlyTerminalState1 801 = eb801 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 50 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup802 : lowerEarlyTerminalBound lowerEarlyTerminalState1 802 = eb802 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 51 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup803 : lowerEarlyTerminalBound lowerEarlyTerminalState1 803 = eb803 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 52 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup808 : lowerEarlyTerminalBound lowerEarlyTerminalState1 808 = eb808 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 57 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup810 : lowerEarlyTerminalBound lowerEarlyTerminalState1 810 = eb810 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 59 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup813 : lowerEarlyTerminalBound lowerEarlyTerminalState1 813 = eb813 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 62 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup815 : lowerEarlyTerminalBound lowerEarlyTerminalState1 815 = eb815 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 64 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup816 : lowerEarlyTerminalBound lowerEarlyTerminalState1 816 = eb816 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 65 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup819 : lowerEarlyTerminalBound lowerEarlyTerminalState1 819 = eb819 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 68 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup820 : lowerEarlyTerminalBound lowerEarlyTerminalState1 820 = eb820 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 69 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup821 : lowerEarlyTerminalBound lowerEarlyTerminalState1 821 = eb821 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 70 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup827 : lowerEarlyTerminalBound lowerEarlyTerminalState1 827 = eb827 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 76 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup830 : lowerEarlyTerminalBound lowerEarlyTerminalState1 830 = eb830 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 79 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup834 : lowerEarlyTerminalBound lowerEarlyTerminalState1 834 = eb834 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 83 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup838 : lowerEarlyTerminalBound lowerEarlyTerminalState1 838 = eb838 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 87 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup842 : lowerEarlyTerminalBound lowerEarlyTerminalState1 842 = eb842 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 91 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup845 : lowerEarlyTerminalBound lowerEarlyTerminalState1 845 = eb845 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 94 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup847 : lowerEarlyTerminalBound lowerEarlyTerminalState1 847 = eb847 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 96 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup851 : lowerEarlyTerminalBound lowerEarlyTerminalState1 851 = eb851 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 100 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup852 : lowerEarlyTerminalBound lowerEarlyTerminalState1 852 = eb852 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 101 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup857 : lowerEarlyTerminalBound lowerEarlyTerminalState1 857 = eb857 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 106 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup858 : lowerEarlyTerminalBound lowerEarlyTerminalState1 858 = eb858 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 107 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup859 : lowerEarlyTerminalBound lowerEarlyTerminalState1 859 = eb859 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 108 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup862 : lowerEarlyTerminalBound lowerEarlyTerminalState1 862 = eb862 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 111 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup864 : lowerEarlyTerminalBound lowerEarlyTerminalState1 864 = eb864 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 113 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup872 : lowerEarlyTerminalBound lowerEarlyTerminalState1 872 = eb872 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 121 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup876 : lowerEarlyTerminalBound lowerEarlyTerminalState1 876 = eb876 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 125 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup880 : lowerEarlyTerminalBound lowerEarlyTerminalState1 880 = eb880 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 129 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup885 : lowerEarlyTerminalBound lowerEarlyTerminalState1 885 = eb885 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 134 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup889 : lowerEarlyTerminalBound lowerEarlyTerminalState1 889 = eb889 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 138 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup890 : lowerEarlyTerminalBound lowerEarlyTerminalState1 890 = eb890 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 139 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup891 : lowerEarlyTerminalBound lowerEarlyTerminalState1 891 = eb891 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 140 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup894 : lowerEarlyTerminalBound lowerEarlyTerminalState1 894 = eb894 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 143 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup896 : lowerEarlyTerminalBound lowerEarlyTerminalState1 896 = eb896 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 145 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup904 : lowerEarlyTerminalBound lowerEarlyTerminalState1 904 = eb904 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 3 (by omega)).trans LookupFast17.selected7.1

private theorem lookup908 : lowerEarlyTerminalBound lowerEarlyTerminalState1 908 = eb908 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 7 (by omega)).trans LookupFast17.selected7.2.1

private theorem lookup912 : lowerEarlyTerminalBound lowerEarlyTerminalState1 912 = eb912 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 11 (by omega)).trans LookupFast17.selected7.2.2.1

private theorem lookup914 : lowerEarlyTerminalBound lowerEarlyTerminalState1 914 = eb914 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 13 (by omega)).trans LookupFast17.selected7.2.2.2.1

private theorem lookup915 : lowerEarlyTerminalBound lowerEarlyTerminalState1 915 = eb915 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 14 (by omega)).trans LookupFast17.selected7.2.2.2.2.1

private theorem lookup918 : lowerEarlyTerminalBound lowerEarlyTerminalState1 918 = eb918 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 17 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.1

private theorem lookup923 : lowerEarlyTerminalBound lowerEarlyTerminalState1 923 = eb923 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 22 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.1

private theorem lookup927 : lowerEarlyTerminalBound lowerEarlyTerminalState1 927 = eb927 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 26 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.1

private theorem lookup928 : lowerEarlyTerminalBound lowerEarlyTerminalState1 928 = eb928 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 27 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.1

private theorem lookup929 : lowerEarlyTerminalBound lowerEarlyTerminalState1 929 = eb929 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 28 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.1

private theorem lookup930 : lowerEarlyTerminalBound lowerEarlyTerminalState1 930 = eb930 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 29 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup937 : lowerEarlyTerminalBound lowerEarlyTerminalState1 937 = eb937 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 36 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup943 : lowerEarlyTerminalBound lowerEarlyTerminalState1 943 = eb943 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 42 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup948 : lowerEarlyTerminalBound lowerEarlyTerminalState1 948 = eb948 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 47 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup952 : lowerEarlyTerminalBound lowerEarlyTerminalState1 952 = eb952 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 51 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup960 : lowerEarlyTerminalBound lowerEarlyTerminalState1 960 = eb960 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 59 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup962 : lowerEarlyTerminalBound lowerEarlyTerminalState1 962 = eb962 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 61 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup968 : lowerEarlyTerminalBound lowerEarlyTerminalState1 968 = eb968 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 67 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup972 : lowerEarlyTerminalBound lowerEarlyTerminalState1 972 = eb972 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 71 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup973 : lowerEarlyTerminalBound lowerEarlyTerminalState1 973 = eb973 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 72 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup974 : lowerEarlyTerminalBound lowerEarlyTerminalState1 974 = eb974 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 73 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup975 : lowerEarlyTerminalBound lowerEarlyTerminalState1 975 = eb975 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 74 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup976 : lowerEarlyTerminalBound lowerEarlyTerminalState1 976 = eb976 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 75 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup983 : lowerEarlyTerminalBound lowerEarlyTerminalState1 983 = eb983 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 82 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup984 : lowerEarlyTerminalBound lowerEarlyTerminalState1 984 = eb984 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 83 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup986 : lowerEarlyTerminalBound lowerEarlyTerminalState1 986 = eb986 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 85 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup994 : lowerEarlyTerminalBound lowerEarlyTerminalState1 994 = eb994 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 93 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup996 : lowerEarlyTerminalBound lowerEarlyTerminalState1 996 = eb996 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 95 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup997 : lowerEarlyTerminalBound lowerEarlyTerminalState1 997 = eb997 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 96 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1000 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1000 = eb1000 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 99 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1006 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1006 = eb1006 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 105 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1010 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1010 = eb1010 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 109 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1011 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1011 = eb1011 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 110 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1012 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1012 = eb1012 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 111 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1013 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1013 = eb1013 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 112 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1014 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1014 = eb1014 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 113 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1021 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1021 = eb1021 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 120 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1027 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1027 = eb1027 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 126 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1032 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1032 = eb1032 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 131 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1036 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1036 = eb1036 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 135 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1037 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1037 = eb1037 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 136 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1044 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1044 = eb1044 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 143 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1046 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1046 = eb1046 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 145 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1047 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1047 = eb1047 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 146 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1050 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1050 = eb1050 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 149 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup1056 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1056 = eb1056 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 5 (by omega)).trans LookupFast17.selected8.1

private theorem lookup1060 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1060 = eb1060 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 9 (by omega)).trans LookupFast17.selected8.2.1

private theorem lookup1061 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1061 = eb1061 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 10 (by omega)).trans LookupFast17.selected8.2.2.1

private theorem lookup1062 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1062 = eb1062 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 11 (by omega)).trans LookupFast17.selected8.2.2.2.1

private theorem lookup1063 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1063 = eb1063 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 12 (by omega)).trans LookupFast17.selected8.2.2.2.2.1

private theorem lookup1064 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1064 = eb1064 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 13 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.1

private theorem lookup1071 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1071 = eb1071 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 20 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.1

private theorem lookup1077 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1077 = eb1077 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 26 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.1

private theorem lookup1082 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1082 = eb1082 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 31 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.1

private theorem lookup1086 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1086 = eb1086 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 35 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.1

private theorem lookup1087 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1087 = eb1087 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 36 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1092 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1092 = eb1092 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 41 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1094 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1094 = eb1094 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 43 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1095 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1095 = eb1095 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 44 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1098 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1098 = eb1098 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 47 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1099 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1099 = eb1099 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 48 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1100 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1100 = eb1100 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 49 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1104 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1104 = eb1104 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 53 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1105 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1105 = eb1105 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 54 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1106 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1106 = eb1106 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 55 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1107 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1107 = eb1107 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 56 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1108 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1108 = eb1108 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 57 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1116 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1116 = eb1116 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 65 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1121 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1121 = eb1121 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 70 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1122 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1122 = eb1122 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 71 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1123 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1123 = eb1123 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 72 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1124 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1124 = eb1124 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 73 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1125 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1125 = eb1125 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 74 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1127 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1127 = eb1127 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 76 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1131 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1131 = eb1131 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 80 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1135 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1135 = eb1135 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 84 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1136 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1136 = eb1136 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 85 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1141 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1141 = eb1141 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 90 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1142 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1142 = eb1142 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 91 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1143 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1143 = eb1143 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 92 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1144 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1144 = eb1144 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 93 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1146 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1146 = eb1146 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 95 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1148 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1148 = eb1148 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 97 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1157 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1157 = eb1157 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 106 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1160 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1160 = eb1160 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 109 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1164 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1164 = eb1164 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 113 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1169 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1169 = eb1169 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 118 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1174 : lowerEarlyTerminalBound lowerEarlyTerminalState1 1174 = eb1174 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 123 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem endpointNonneg1 : 0 ≤ certFieldLower (⟨(5/22),(1/22),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg2 : 0 ≤ certFieldLower (⟨2,-1,0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg3 : 0 ≤ certFieldLower (⟨(10/23),(-1/69),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg4 : 0 ≤ certFieldLower (⟨(5/11),(-1/11),0,0⟩ : CertField) := by
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

private theorem endpointNonneg27 : 0 ≤ certFieldLower (⟨(15/37),(-1/37),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg28 : 0 ≤ certFieldLower (⟨(-1/10),0,0,(1/10)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg29 : 0 ≤ certFieldLower (⟨(63/170),0,0,(-1/510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg30 : 0 ≤ certFieldLower (⟨(9/10),0,0,(-1/10)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg31 : 0 ≤ certFieldLower (⟨(35/94),(1/94),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg32 : 0 ≤ certFieldLower (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg33 : 0 ≤ certFieldLower (⟨(105/262),0,0,(-1/262)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg34 : 0 ≤ certFieldLower (⟨(247/649),(1/649),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg35 : 0 ≤ certFieldLower (⟨(177/454),(-1/454),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg36 : 0 ≤ certFieldLower (⟨(251/670),0,0,(1/670)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg37 : 0 ≤ certFieldLower (⟨(31/82),0,0,(1/574)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg38 : 0 ≤ certFieldLower (⟨(83/202),0,0,(-1/202)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg39 : 0 ≤ certFieldLower (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg40 : 0 ≤ certFieldLower (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg41 : 0 ≤ certFieldLower (⟨(31/94),0,0,(1/94)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg42 : 0 ≤ certFieldLower (⟨(1/2),0,0,(-1/42)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg43 : 0 ≤ certFieldLower (⟨(32/83),(-1/249),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg44 : 0 ≤ certFieldLower (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg45 : 0 ≤ certFieldLower (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg46 : 0 ≤ certFieldLower (⟨(523/1354),0,0,(1/1354)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg47 : 0 ≤ certFieldLower (⟨(3734/9757),(1/9757),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg48 : 0 ≤ certFieldLower (⟨(227/590),0,0,(1/1770)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg49 : 0 ≤ certFieldLower (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg50 : 0 ≤ certFieldLower (⟨(353/914),(1/2742),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg51 : 0 ≤ certFieldLower (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg52 : 0 ≤ certFieldLower (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg53 : 0 ≤ certFieldLower (⟨(579/1510),0,0,(1/1510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg54 : 0 ≤ certFieldLower (⟨(167/430),0,0,(-1/3010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg55 : 0 ≤ certFieldLower (⟨(553/1429),(1/1429),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg56 : 0 ≤ certFieldLower (⟨(2589/6674),(1/20022),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg57 : 0 ≤ certFieldLower (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg58 : 0 ≤ certFieldLower (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg59 : 0 ≤ certFieldLower (⟨(1932/4957),(1/4957),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg60 : 0 ≤ certFieldLower (⟨(779/1994),(-1/5982),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg61 : 0 ≤ certFieldLower (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg62 : 0 ≤ certFieldLower (⟨(167/430),0,0,(1/3010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg63 : 0 ≤ certFieldLower (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg64 : 0 ≤ certFieldLower (⟨(13260/33937),(1/33937),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg65 : 0 ≤ certFieldLower (⟨(278/709),(-1/709),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg66 : 0 ≤ certFieldLower (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg67 : 0 ≤ certFieldLower (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg68 : 0 ≤ certFieldLower (⟨(-1/2),(1/2),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg69 : 0 ≤ certFieldLower (⟨(4/13),(1/13),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg70 : 0 ≤ certFieldLower (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg71 : 0 ≤ certFieldLower (⟨(93/262),(1/262),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg72 : 0 ≤ certFieldLower (⟨(1859/5158),0,0,(1/5158)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg73 : 0 ≤ certFieldLower (⟨(1991/5521),(1/5521),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg74 : 0 ≤ certFieldLower (⟨(61/169),(1/169),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg75 : 0 ≤ certFieldLower (⟨(1089/2950),0,0,(1/2950)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg76 : 0 ≤ certFieldLower (⟨(29/74),0,0,(-1/222)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg77 : 0 ≤ certFieldLower (⟨(3/10),0,0,(1/70)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg78 : 0 ≤ certFieldLower (⟨(1161/3142),(1/3142),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg79 : 0 ≤ certFieldLower (⟨(66/179),(-1/537),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg80 : 0 ≤ certFieldLower (⟨(2615/7138),0,0,(-1/7138)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg81 : 0 ≤ certFieldLower (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg82 : 0 ≤ certFieldLower (⟨(251/670),0,0,(-1/670)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg83 : 0 ≤ certFieldLower (⟨(2463/6350),0,0,(1/19050)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg84 : 0 ≤ certFieldLower (⟨(483/1318),(1/1318),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg85 : 0 ≤ certFieldLower (⟨(7081/19270),0,0,(1/19270)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg86 : 0 ≤ certFieldLower (⟨(457/1258),0,0,(1/1258)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg87 : 0 ≤ certFieldLower (⟨(7480/20353),(1/20353),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg88 : 0 ≤ certFieldLower (⟨(11835/32926),0,0,(1/32926)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg89 : 0 ≤ certFieldLower (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg90 : 0 ≤ certFieldLower (⟨(797/2221),(1/2221),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg91 : 0 ≤ certFieldLower (⟨(667/1846),(-1/1846),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg92 : 0 ≤ certFieldLower (⟨(723/2026),0,0,(1/2026)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg93 : 0 ≤ certFieldLower (⟨(665/1858),0,0,(1/1858)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg94 : 0 ≤ certFieldLower (⟨(411/1126),0,0,(-1/1126)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg95 : 0 ≤ certFieldLower (⟨(1557/4318),0,0,(-1/30226)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg96 : 0 ≤ certFieldLower (⟨(11574/32101),(-1/32101),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg97 : 0 ≤ certFieldLower (⟨(383/1033),(-1/1033),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg98 : 0 ≤ certFieldLower (⟨(411/1126),0,0,(1/1126)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg99 : 0 ≤ certFieldLower (⟨(31/82),0,0,(-1/574)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg100 : 0 ≤ certFieldLower (⟨(6361/17218),0,0,(-1/17218)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg101 : 0 ≤ certFieldLower (⟨(6760/18301),(-1/18301),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg102 : 0 ≤ certFieldLower (⟨(12510/34801),(1/34801),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg103 : 0 ≤ certFieldLower (⟨(2587/6806),0,0,(1/20418)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg104 : 0 ≤ certFieldLower (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg105 : 0 ≤ certFieldLower (⟨(446/1177),(1/1177),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg106 : 0 ≤ certFieldLower (⟨(651/1702),(-1/1702),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg107 : 0 ≤ certFieldLower (⟨(63/170),0,0,(1/510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg108 : 0 ≤ certFieldLower (⟨(3247/8507),(-1/25521),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg109 : 0 ≤ certFieldLower (⟨(17703/45778),0,0,(1/45778)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg110 : 0 ≤ certFieldLower (⟨(21015/54241),(-1/54241),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg111 : 0 ≤ certFieldLower (⟨(3079/8066),0,0,(-1/24198)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg112 : 0 ≤ certFieldLower (⟨(227/590),0,0,(-1/1770)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg113 : 0 ≤ certFieldLower (⟨(2755/7247),(1/21741),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg114 : 0 ≤ certFieldLower (⟨(18819/48661),(1/48661),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg115 : 0 ≤ certFieldLower (⟨(33653/86281),(1/86281),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg116 : 0 ≤ certFieldLower (⟨(5033/13742),0,0,(1/41226)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg117 : 0 ≤ certFieldLower (⟨(167/454),0,0,(-1/3178)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg118 : 0 ≤ certFieldLower (⟨(856/2341),(1/2341),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg119 : 0 ≤ certFieldLower (⟨(1301/3541),(-1/3541),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg120 : 0 ≤ certFieldLower (⟨(109/302),0,0,(1/906)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg121 : 0 ≤ certFieldLower (⟨(6101/16622),0,0,(-1/49866)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg122 : 0 ≤ certFieldLower (⟨(6431/17522),(-1/52566),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem threshold1 : certThresholdDataValid eb1.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg2⟩

private theorem indexOk1 : 0 < 1 ∧ 1 ≤ 1238 := by norm_num

private theorem threshold2 : certThresholdDataValid eb2.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg4⟩

private theorem indexOk2 : 0 < 2 ∧ 2 ≤ 1238 := by norm_num

private theorem threshold6 : certThresholdDataValid eb6.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg6⟩

private theorem indexOk6 : 0 < 6 ∧ 6 ≤ 1238 := by norm_num

private theorem threshold7 : certThresholdDataValid eb7.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem indexOk7 : 0 < 7 ∧ 7 ≤ 1238 := by norm_num

private theorem threshold8 : certThresholdDataValid eb8.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg6⟩

private theorem indexOk8 : 0 < 8 ∧ 8 ≤ 1238 := by norm_num

private theorem threshold12 : certThresholdDataValid eb12.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem indexOk12 : 0 < 12 ∧ 12 ≤ 1238 := by norm_num

private theorem threshold13 : certThresholdDataValid eb13.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg11⟩

private theorem indexOk13 : 0 < 13 ∧ 13 ≤ 1238 := by norm_num

private theorem threshold14 : certThresholdDataValid eb14.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg12⟩

private theorem indexOk14 : 0 < 14 ∧ 14 ≤ 1238 := by norm_num

private theorem threshold15 : certThresholdDataValid eb15.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg13⟩

private theorem indexOk15 : 0 < 15 ∧ 15 ≤ 1238 := by norm_num

private theorem threshold23 : certThresholdDataValid eb23.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg6⟩

private theorem indexOk23 : 0 < 23 ∧ 23 ≤ 1238 := by norm_num

private theorem threshold27 : certThresholdDataValid eb27.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem indexOk27 : 0 < 27 ∧ 27 ≤ 1238 := by norm_num

private theorem threshold28 : certThresholdDataValid eb28.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg3⟩

private theorem indexOk28 : 0 < 28 ∧ 28 ≤ 1238 := by norm_num

private theorem threshold33 : certThresholdDataValid eb33.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk33 : 0 < 33 ∧ 33 ≤ 1238 := by norm_num

private theorem threshold35 : certThresholdDataValid eb35.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk35 : 0 < 35 ∧ 35 ≤ 1238 := by norm_num

private theorem threshold36 : certThresholdDataValid eb36.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem indexOk36 : 0 < 36 ∧ 36 ≤ 1238 := by norm_num

private theorem threshold39 : certThresholdDataValid eb39.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg3⟩

private theorem indexOk39 : 0 < 39 ∧ 39 ≤ 1238 := by norm_num

private theorem threshold43 : certThresholdDataValid eb43.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem indexOk43 : 0 < 43 ∧ 43 ≤ 1238 := by norm_num

private theorem threshold45 : certThresholdDataValid eb45.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg3⟩

private theorem indexOk45 : 0 < 45 ∧ 45 ≤ 1238 := by norm_num

private theorem threshold50 : certThresholdDataValid eb50.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg11⟩

private theorem indexOk50 : 0 < 50 ∧ 50 ≤ 1238 := by norm_num

private theorem threshold51 : certThresholdDataValid eb51.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem indexOk51 : 0 < 51 ∧ 51 ≤ 1238 := by norm_num

private theorem threshold52 : certThresholdDataValid eb52.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg18⟩

private theorem indexOk52 : 0 < 52 ∧ 52 ≤ 1238 := by norm_num

private theorem threshold53 : certThresholdDataValid eb53.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg6⟩

private theorem indexOk53 : 0 < 53 ∧ 53 ≤ 1238 := by norm_num

private theorem threshold60 : certThresholdDataValid eb60.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg11⟩

private theorem indexOk60 : 0 < 60 ∧ 60 ≤ 1238 := by norm_num

private theorem threshold61 : certThresholdDataValid eb61.threshold := by
  exact ⟨endpointNonneg10, endpointNonneg12⟩

private theorem indexOk61 : 0 < 61 ∧ 61 ≤ 1238 := by norm_num

private theorem threshold66 : certThresholdDataValid eb66.threshold := by
  exact ⟨endpointNonneg7, endpointNonneg8⟩

private theorem indexOk66 : 0 < 66 ∧ 66 ≤ 1238 := by norm_num

private theorem threshold69 : certThresholdDataValid eb69.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg6⟩

private theorem indexOk69 : 0 < 69 ∧ 69 ≤ 1238 := by norm_num

private theorem threshold70 : certThresholdDataValid eb70.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg6⟩

private theorem indexOk70 : 0 < 70 ∧ 70 ≤ 1238 := by norm_num

private theorem threshold71 : certThresholdDataValid eb71.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg8⟩

private theorem indexOk71 : 0 < 71 ∧ 71 ≤ 1238 := by norm_num

private theorem threshold75 : certThresholdDataValid eb75.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem indexOk75 : 0 < 75 ∧ 75 ≤ 1238 := by norm_num

private theorem threshold76 : certThresholdDataValid eb76.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg3⟩

private theorem indexOk76 : 0 < 76 ∧ 76 ≤ 1238 := by norm_num

private theorem threshold84 : certThresholdDataValid eb84.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk84 : 0 < 84 ∧ 84 ≤ 1238 := by norm_num

private theorem threshold86 : certThresholdDataValid eb86.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk86 : 0 < 86 ∧ 86 ≤ 1238 := by norm_num

private theorem threshold87 : certThresholdDataValid eb87.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem indexOk87 : 0 < 87 ∧ 87 ≤ 1238 := by norm_num

private theorem threshold90 : certThresholdDataValid eb90.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg3⟩

private theorem indexOk90 : 0 < 90 ∧ 90 ≤ 1238 := by norm_num

private theorem threshold96 : certThresholdDataValid eb96.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg3⟩

private theorem indexOk96 : 0 < 96 ∧ 96 ≤ 1238 := by norm_num

private theorem threshold100 : certThresholdDataValid eb100.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg12⟩

private theorem indexOk100 : 0 < 100 ∧ 100 ≤ 1238 := by norm_num

private theorem threshold101 : certThresholdDataValid eb101.threshold := by
  exact ⟨endpointNonneg20, endpointNonneg21⟩

private theorem indexOk101 : 0 < 101 ∧ 101 ≤ 1238 := by norm_num

private theorem threshold102 : certThresholdDataValid eb102.threshold := by
  exact ⟨endpointNonneg22, endpointNonneg21⟩

private theorem indexOk102 : 0 < 102 ∧ 102 ≤ 1238 := by norm_num

private theorem threshold103 : certThresholdDataValid eb103.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg3⟩

private theorem indexOk103 : 0 < 103 ∧ 103 ≤ 1238 := by norm_num

private theorem threshold105 : certThresholdDataValid eb105.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk105 : 0 < 105 ∧ 105 ≤ 1238 := by norm_num

private theorem threshold106 : certThresholdDataValid eb106.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg3⟩

private theorem indexOk106 : 0 < 106 ∧ 106 ≤ 1238 := by norm_num

private theorem threshold107 : certThresholdDataValid eb107.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk107 : 0 < 107 ∧ 107 ≤ 1238 := by norm_num

private theorem threshold109 : certThresholdDataValid eb109.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg23⟩

private theorem indexOk109 : 0 < 109 ∧ 109 ≤ 1238 := by norm_num

private theorem threshold110 : certThresholdDataValid eb110.threshold := by
  exact ⟨endpointNonneg20, endpointNonneg21⟩

private theorem indexOk110 : 0 < 110 ∧ 110 ≤ 1238 := by norm_num

private theorem threshold114 : certThresholdDataValid eb114.threshold := by
  exact ⟨endpointNonneg20, endpointNonneg21⟩

private theorem indexOk114 : 0 < 114 ∧ 114 ≤ 1238 := by norm_num

private theorem threshold115 : certThresholdDataValid eb115.threshold := by
  exact ⟨endpointNonneg22, endpointNonneg21⟩

private theorem indexOk115 : 0 < 115 ∧ 115 ≤ 1238 := by norm_num

private theorem threshold116 : certThresholdDataValid eb116.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg3⟩

private theorem indexOk116 : 0 < 116 ∧ 116 ≤ 1238 := by norm_num

private theorem threshold118 : certThresholdDataValid eb118.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg3⟩

private theorem indexOk118 : 0 < 118 ∧ 118 ≤ 1238 := by norm_num

private theorem threshold119 : certThresholdDataValid eb119.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg23⟩

private theorem indexOk119 : 0 < 119 ∧ 119 ≤ 1238 := by norm_num

private theorem threshold120 : certThresholdDataValid eb120.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg15⟩

private theorem indexOk120 : 0 < 120 ∧ 120 ≤ 1238 := by norm_num

private theorem threshold121 : certThresholdDataValid eb121.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg12⟩

private theorem indexOk121 : 0 < 121 ∧ 121 ≤ 1238 := by norm_num

private theorem threshold122 : certThresholdDataValid eb122.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg15⟩

private theorem indexOk122 : 0 < 122 ∧ 122 ≤ 1238 := by norm_num

private theorem threshold125 : certThresholdDataValid eb125.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg17⟩

private theorem indexOk125 : 0 < 125 ∧ 125 ≤ 1238 := by norm_num

private theorem threshold127 : certThresholdDataValid eb127.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg3⟩

private theorem indexOk127 : 0 < 127 ∧ 127 ≤ 1238 := by norm_num

private theorem threshold129 : certThresholdDataValid eb129.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk129 : 0 < 129 ∧ 129 ≤ 1238 := by norm_num

private theorem threshold131 : certThresholdDataValid eb131.threshold := by
  exact ⟨endpointNonneg14, endpointNonneg16⟩

private theorem indexOk131 : 0 < 131 ∧ 131 ≤ 1238 := by norm_num

private theorem threshold134 : certThresholdDataValid eb134.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg3⟩

private theorem indexOk134 : 0 < 134 ∧ 134 ≤ 1238 := by norm_num

private theorem threshold137 : certThresholdDataValid eb137.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg3⟩

private theorem indexOk137 : 0 < 137 ∧ 137 ≤ 1238 := by norm_num

private theorem threshold140 : certThresholdDataValid eb140.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg15⟩

private theorem indexOk140 : 0 < 140 ∧ 140 ≤ 1238 := by norm_num

private theorem threshold144 : certThresholdDataValid eb144.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg15⟩

private theorem indexOk144 : 0 < 144 ∧ 144 ≤ 1238 := by norm_num

private theorem threshold145 : certThresholdDataValid eb145.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk145 : 0 < 145 ∧ 145 ≤ 1238 := by norm_num

private theorem threshold146 : certThresholdDataValid eb146.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk146 : 0 < 146 ∧ 146 ≤ 1238 := by norm_num

private theorem threshold147 : certThresholdDataValid eb147.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg30⟩

private theorem indexOk147 : 0 < 147 ∧ 147 ≤ 1238 := by norm_num

private theorem threshold150 : certThresholdDataValid eb150.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg12⟩

private theorem indexOk150 : 0 < 150 ∧ 150 ≤ 1238 := by norm_num

private theorem threshold154 : certThresholdDataValid eb154.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg12⟩

private theorem indexOk154 : 0 < 154 ∧ 154 ≤ 1238 := by norm_num

private theorem threshold159 : certThresholdDataValid eb159.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg31⟩

private theorem indexOk159 : 0 < 159 ∧ 159 ≤ 1238 := by norm_num

private theorem threshold160 : certThresholdDataValid eb160.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg4⟩

private theorem indexOk160 : 0 < 160 ∧ 160 ≤ 1238 := by norm_num

private theorem threshold162 : certThresholdDataValid eb162.threshold := by
  exact ⟨endpointNonneg32, endpointNonneg33⟩

private theorem indexOk162 : 0 < 162 ∧ 162 ≤ 1238 := by norm_num

private theorem threshold163 : certThresholdDataValid eb163.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk163 : 0 < 163 ∧ 163 ≤ 1238 := by norm_num

private theorem threshold164 : certThresholdDataValid eb164.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg33⟩

private theorem indexOk164 : 0 < 164 ∧ 164 ≤ 1238 := by norm_num

private theorem threshold165 : certThresholdDataValid eb165.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk165 : 0 < 165 ∧ 165 ≤ 1238 := by norm_num

private theorem threshold170 : certThresholdDataValid eb170.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk170 : 0 < 170 ∧ 170 ≤ 1238 := by norm_num

private theorem threshold171 : certThresholdDataValid eb171.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk171 : 0 < 171 ∧ 171 ≤ 1238 := by norm_num

private theorem threshold172 : certThresholdDataValid eb172.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk172 : 0 < 172 ∧ 172 ≤ 1238 := by norm_num

private theorem threshold173 : certThresholdDataValid eb173.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk173 : 0 < 173 ∧ 173 ≤ 1238 := by norm_num

private theorem threshold174 : certThresholdDataValid eb174.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg40⟩

private theorem indexOk174 : 0 < 174 ∧ 174 ≤ 1238 := by norm_num

private theorem threshold183 : certThresholdDataValid eb183.threshold := by
  exact ⟨endpointNonneg32, endpointNonneg33⟩

private theorem indexOk183 : 0 < 183 ∧ 183 ≤ 1238 := by norm_num

private theorem threshold186 : certThresholdDataValid eb186.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk186 : 0 < 186 ∧ 186 ≤ 1238 := by norm_num

private theorem threshold187 : certThresholdDataValid eb187.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg42⟩

private theorem indexOk187 : 0 < 187 ∧ 187 ≤ 1238 := by norm_num

private theorem threshold188 : certThresholdDataValid eb188.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg43⟩

private theorem indexOk188 : 0 < 188 ∧ 188 ≤ 1238 := by norm_num

private theorem threshold193 : certThresholdDataValid eb193.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg43⟩

private theorem indexOk193 : 0 < 193 ∧ 193 ≤ 1238 := by norm_num

private theorem threshold194 : certThresholdDataValid eb194.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk194 : 0 < 194 ∧ 194 ≤ 1238 := by norm_num

private theorem threshold195 : certThresholdDataValid eb195.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk195 : 0 < 195 ∧ 195 ≤ 1238 := by norm_num

private theorem threshold196 : certThresholdDataValid eb196.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk196 : 0 < 196 ∧ 196 ≤ 1238 := by norm_num

private theorem threshold197 : certThresholdDataValid eb197.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg45⟩

private theorem indexOk197 : 0 < 197 ∧ 197 ≤ 1238 := by norm_num

private theorem threshold199 : certThresholdDataValid eb199.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg42⟩

private theorem indexOk199 : 0 < 199 ∧ 199 ≤ 1238 := by norm_num

private theorem threshold203 : certThresholdDataValid eb203.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk203 : 0 < 203 ∧ 203 ≤ 1238 := by norm_num

private theorem threshold207 : certThresholdDataValid eb207.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk207 : 0 < 207 ∧ 207 ≤ 1238 := by norm_num

private theorem threshold208 : certThresholdDataValid eb208.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg42⟩

private theorem indexOk208 : 0 < 208 ∧ 208 ≤ 1238 := by norm_num

private theorem threshold214 : certThresholdDataValid eb214.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk214 : 0 < 214 ∧ 214 ≤ 1238 := by norm_num

private theorem threshold215 : certThresholdDataValid eb215.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk215 : 0 < 215 ∧ 215 ≤ 1238 := by norm_num

private theorem threshold216 : certThresholdDataValid eb216.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk216 : 0 < 216 ∧ 216 ≤ 1238 := by norm_num

private theorem threshold217 : certThresholdDataValid eb217.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk217 : 0 < 217 ∧ 217 ≤ 1238 := by norm_num

private theorem threshold218 : certThresholdDataValid eb218.threshold := by
  exact ⟨endpointNonneg32, endpointNonneg33⟩

private theorem indexOk218 : 0 < 218 ∧ 218 ≤ 1238 := by norm_num

private theorem threshold223 : certThresholdDataValid eb223.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk223 : 0 < 223 ∧ 223 ≤ 1238 := by norm_num

private theorem threshold226 : certThresholdDataValid eb226.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk226 : 0 < 226 ∧ 226 ≤ 1238 := by norm_num

private theorem threshold229 : certThresholdDataValid eb229.threshold := by
  exact ⟨endpointNonneg32, endpointNonneg33⟩

private theorem indexOk229 : 0 < 229 ∧ 229 ≤ 1238 := by norm_num

private theorem threshold230 : certThresholdDataValid eb230.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk230 : 0 < 230 ∧ 230 ≤ 1238 := by norm_num

private theorem threshold231 : certThresholdDataValid eb231.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg35⟩

private theorem indexOk231 : 0 < 231 ∧ 231 ≤ 1238 := by norm_num

private theorem threshold235 : certThresholdDataValid eb235.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg42⟩

private theorem indexOk235 : 0 < 235 ∧ 235 ≤ 1238 := by norm_num

private theorem threshold236 : certThresholdDataValid eb236.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg43⟩

private theorem indexOk236 : 0 < 236 ∧ 236 ≤ 1238 := by norm_num

private theorem threshold241 : certThresholdDataValid eb241.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg43⟩

private theorem indexOk241 : 0 < 241 ∧ 241 ≤ 1238 := by norm_num

private theorem threshold242 : certThresholdDataValid eb242.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk242 : 0 < 242 ∧ 242 ≤ 1238 := by norm_num

private theorem threshold243 : certThresholdDataValid eb243.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg42⟩

private theorem indexOk243 : 0 < 243 ∧ 243 ≤ 1238 := by norm_num

private theorem threshold244 : certThresholdDataValid eb244.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk244 : 0 < 244 ∧ 244 ≤ 1238 := by norm_num

private theorem threshold245 : certThresholdDataValid eb245.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg45⟩

private theorem indexOk245 : 0 < 245 ∧ 245 ≤ 1238 := by norm_num

private theorem threshold247 : certThresholdDataValid eb247.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk247 : 0 < 247 ∧ 247 ≤ 1238 := by norm_num

private theorem threshold251 : certThresholdDataValid eb251.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk251 : 0 < 251 ∧ 251 ≤ 1238 := by norm_num

private theorem threshold252 : certThresholdDataValid eb252.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg42⟩

private theorem indexOk252 : 0 < 252 ∧ 252 ≤ 1238 := by norm_num

private theorem threshold257 : certThresholdDataValid eb257.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk257 : 0 < 257 ∧ 257 ≤ 1238 := by norm_num

private theorem threshold258 : certThresholdDataValid eb258.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg49⟩

private theorem indexOk258 : 0 < 258 ∧ 258 ≤ 1238 := by norm_num

private theorem threshold259 : certThresholdDataValid eb259.threshold := by
  exact ⟨endpointNonneg50, endpointNonneg51⟩

private theorem indexOk259 : 0 < 259 ∧ 259 ≤ 1238 := by norm_num

private theorem threshold260 : certThresholdDataValid eb260.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg52⟩

private theorem indexOk260 : 0 < 260 ∧ 260 ≤ 1238 := by norm_num

private theorem threshold261 : certThresholdDataValid eb261.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg54⟩

private theorem indexOk261 : 0 < 261 ∧ 261 ≤ 1238 := by norm_num

private theorem threshold268 : certThresholdDataValid eb268.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg49⟩

private theorem indexOk268 : 0 < 268 ∧ 268 ≤ 1238 := by norm_num

private theorem threshold272 : certThresholdDataValid eb272.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg35⟩

private theorem indexOk272 : 0 < 272 ∧ 272 ≤ 1238 := by norm_num

private theorem threshold280 : certThresholdDataValid eb280.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk280 : 0 < 280 ∧ 280 ≤ 1238 := by norm_num

private theorem threshold282 : certThresholdDataValid eb282.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk282 : 0 < 282 ∧ 282 ≤ 1238 := by norm_num

private theorem threshold283 : certThresholdDataValid eb283.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk283 : 0 < 283 ∧ 283 ≤ 1238 := by norm_num

private theorem threshold286 : certThresholdDataValid eb286.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg35⟩

private theorem indexOk286 : 0 < 286 ∧ 286 ≤ 1238 := by norm_num

private theorem threshold292 : certThresholdDataValid eb292.threshold := by
  exact ⟨endpointNonneg56, endpointNonneg35⟩

private theorem indexOk292 : 0 < 292 ∧ 292 ≤ 1238 := by norm_num

private theorem threshold296 : certThresholdDataValid eb296.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk296 : 0 < 296 ∧ 296 ≤ 1238 := by norm_num

private theorem threshold297 : certThresholdDataValid eb297.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk297 : 0 < 297 ∧ 297 ≤ 1238 := by norm_num

private theorem threshold298 : certThresholdDataValid eb298.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg58⟩

private theorem indexOk298 : 0 < 298 ∧ 298 ≤ 1238 := by norm_num

private theorem threshold299 : certThresholdDataValid eb299.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg60⟩

private theorem indexOk299 : 0 < 299 ∧ 299 ≤ 1238 := by norm_num

private theorem threshold300 : certThresholdDataValid eb300.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg61⟩

private theorem indexOk300 : 0 < 300 ∧ 300 ≤ 1238 := by norm_num

private theorem threshold301 : certThresholdDataValid eb301.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg63⟩

private theorem indexOk301 : 0 < 301 ∧ 301 ≤ 1238 := by norm_num

private theorem threshold308 : certThresholdDataValid eb308.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg58⟩

private theorem indexOk308 : 0 < 308 ∧ 308 ≤ 1238 := by norm_num

private theorem threshold312 : certThresholdDataValid eb312.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg65⟩

private theorem indexOk312 : 0 < 312 ∧ 312 ≤ 1238 := by norm_num

private theorem threshold318 : certThresholdDataValid eb318.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk318 : 0 < 318 ∧ 318 ≤ 1238 := by norm_num

private theorem threshold320 : certThresholdDataValid eb320.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk320 : 0 < 320 ∧ 320 ≤ 1238 := by norm_num

private theorem threshold321 : certThresholdDataValid eb321.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk321 : 0 < 321 ∧ 321 ≤ 1238 := by norm_num

private theorem threshold324 : certThresholdDataValid eb324.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk324 : 0 < 324 ∧ 324 ≤ 1238 := by norm_num

private theorem threshold325 : certThresholdDataValid eb325.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg43⟩

private theorem indexOk325 : 0 < 325 ∧ 325 ≤ 1238 := by norm_num

private theorem threshold327 : certThresholdDataValid eb327.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk327 : 0 < 327 ∧ 327 ≤ 1238 := by norm_num

private theorem threshold328 : certThresholdDataValid eb328.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg43⟩

private theorem indexOk328 : 0 < 328 ∧ 328 ≤ 1238 := by norm_num

private theorem threshold329 : certThresholdDataValid eb329.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk329 : 0 < 329 ∧ 329 ≤ 1238 := by norm_num

private theorem threshold331 : certThresholdDataValid eb331.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg45⟩

private theorem indexOk331 : 0 < 331 ∧ 331 ≤ 1238 := by norm_num

private theorem threshold332 : certThresholdDataValid eb332.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg43⟩

private theorem indexOk332 : 0 < 332 ∧ 332 ≤ 1238 := by norm_num

private theorem threshold333 : certThresholdDataValid eb333.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg43⟩

private theorem indexOk333 : 0 < 333 ∧ 333 ≤ 1238 := by norm_num

private theorem threshold334 : certThresholdDataValid eb334.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg45⟩

private theorem indexOk334 : 0 < 334 ∧ 334 ≤ 1238 := by norm_num

private theorem threshold335 : certThresholdDataValid eb335.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg43⟩

private theorem indexOk335 : 0 < 335 ∧ 335 ≤ 1238 := by norm_num

private theorem threshold336 : certThresholdDataValid eb336.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg43⟩

private theorem indexOk336 : 0 < 336 ∧ 336 ≤ 1238 := by norm_num

private theorem threshold337 : certThresholdDataValid eb337.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg45⟩

private theorem indexOk337 : 0 < 337 ∧ 337 ≤ 1238 := by norm_num

private theorem threshold338 : certThresholdDataValid eb338.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg31⟩

private theorem indexOk338 : 0 < 338 ∧ 338 ≤ 1238 := by norm_num

private theorem threshold340 : certThresholdDataValid eb340.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg31⟩

private theorem indexOk340 : 0 < 340 ∧ 340 ≤ 1238 := by norm_num

private theorem threshold341 : certThresholdDataValid eb341.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk341 : 0 < 341 ∧ 341 ≤ 1238 := by norm_num

private theorem threshold342 : certThresholdDataValid eb342.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk342 : 0 < 342 ∧ 342 ≤ 1238 := by norm_num

private theorem threshold345 : certThresholdDataValid eb345.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg43⟩

private theorem indexOk345 : 0 < 345 ∧ 345 ≤ 1238 := by norm_num

private theorem threshold346 : certThresholdDataValid eb346.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk346 : 0 < 346 ∧ 346 ≤ 1238 := by norm_num

private theorem threshold347 : certThresholdDataValid eb347.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg43⟩

private theorem indexOk347 : 0 < 347 ∧ 347 ≤ 1238 := by norm_num

private theorem threshold348 : certThresholdDataValid eb348.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk348 : 0 < 348 ∧ 348 ≤ 1238 := by norm_num

private theorem threshold349 : certThresholdDataValid eb349.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk349 : 0 < 349 ∧ 349 ≤ 1238 := by norm_num

private theorem threshold350 : certThresholdDataValid eb350.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg45⟩

private theorem indexOk350 : 0 < 350 ∧ 350 ≤ 1238 := by norm_num

private theorem threshold355 : certThresholdDataValid eb355.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk355 : 0 < 355 ∧ 355 ≤ 1238 := by norm_num

private theorem threshold356 : certThresholdDataValid eb356.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk356 : 0 < 356 ∧ 356 ≤ 1238 := by norm_num

private theorem threshold357 : certThresholdDataValid eb357.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk357 : 0 < 357 ∧ 357 ≤ 1238 := by norm_num

private theorem threshold358 : certThresholdDataValid eb358.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg35⟩

private theorem indexOk358 : 0 < 358 ∧ 358 ≤ 1238 := by norm_num

private theorem threshold359 : certThresholdDataValid eb359.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk359 : 0 < 359 ∧ 359 ≤ 1238 := by norm_num

private theorem threshold360 : certThresholdDataValid eb360.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg35⟩

private theorem indexOk360 : 0 < 360 ∧ 360 ≤ 1238 := by norm_num

private theorem threshold363 : certThresholdDataValid eb363.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg40⟩

private theorem indexOk363 : 0 < 363 ∧ 363 ≤ 1238 := by norm_num

private theorem threshold366 : certThresholdDataValid eb366.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk366 : 0 < 366 ∧ 366 ≤ 1238 := by norm_num

private theorem threshold370 : certThresholdDataValid eb370.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk370 : 0 < 370 ∧ 370 ≤ 1238 := by norm_num

private theorem threshold375 : certThresholdDataValid eb375.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk375 : 0 < 375 ∧ 375 ≤ 1238 := by norm_num

private theorem threshold376 : certThresholdDataValid eb376.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg65⟩

private theorem indexOk376 : 0 < 376 ∧ 376 ≤ 1238 := by norm_num

private theorem threshold380 : certThresholdDataValid eb380.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk380 : 0 < 380 ∧ 380 ≤ 1238 := by norm_num

private theorem threshold382 : certThresholdDataValid eb382.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg3⟩

private theorem indexOk382 : 0 < 382 ∧ 382 ≤ 1238 := by norm_num

private theorem threshold383 : certThresholdDataValid eb383.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg3⟩

private theorem indexOk383 : 0 < 383 ∧ 383 ≤ 1238 := by norm_num

private theorem threshold384 : certThresholdDataValid eb384.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg23⟩

private theorem indexOk384 : 0 < 384 ∧ 384 ≤ 1238 := by norm_num

private theorem threshold385 : certThresholdDataValid eb385.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg15⟩

private theorem indexOk385 : 0 < 385 ∧ 385 ≤ 1238 := by norm_num

private theorem threshold386 : certThresholdDataValid eb386.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg15⟩

private theorem indexOk386 : 0 < 386 ∧ 386 ≤ 1238 := by norm_num

private theorem threshold387 : certThresholdDataValid eb387.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg15⟩

private theorem indexOk387 : 0 < 387 ∧ 387 ≤ 1238 := by norm_num

private theorem threshold388 : certThresholdDataValid eb388.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg15⟩

private theorem indexOk388 : 0 < 388 ∧ 388 ≤ 1238 := by norm_num

private theorem threshold389 : certThresholdDataValid eb389.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg15⟩

private theorem indexOk389 : 0 < 389 ∧ 389 ≤ 1238 := by norm_num

private theorem threshold390 : certThresholdDataValid eb390.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg15⟩

private theorem indexOk390 : 0 < 390 ∧ 390 ≤ 1238 := by norm_num

private theorem threshold391 : certThresholdDataValid eb391.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg17⟩

private theorem indexOk391 : 0 < 391 ∧ 391 ≤ 1238 := by norm_num

private theorem threshold392 : certThresholdDataValid eb392.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg17⟩

private theorem indexOk392 : 0 < 392 ∧ 392 ≤ 1238 := by norm_num

private theorem threshold393 : certThresholdDataValid eb393.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg17⟩

private theorem indexOk393 : 0 < 393 ∧ 393 ≤ 1238 := by norm_num

private theorem threshold394 : certThresholdDataValid eb394.threshold := by
  exact ⟨endpointNonneg68, endpointNonneg69⟩

private theorem indexOk394 : 0 < 394 ∧ 394 ≤ 1238 := by norm_num

private theorem threshold395 : certThresholdDataValid eb395.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg31⟩

private theorem indexOk395 : 0 < 395 ∧ 395 ≤ 1238 := by norm_num

private theorem threshold396 : certThresholdDataValid eb396.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg70⟩

private theorem indexOk396 : 0 < 396 ∧ 396 ≤ 1238 := by norm_num

private theorem threshold397 : certThresholdDataValid eb397.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg70⟩

private theorem indexOk397 : 0 < 397 ∧ 397 ≤ 1238 := by norm_num

private theorem threshold398 : certThresholdDataValid eb398.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg70⟩

private theorem indexOk398 : 0 < 398 ∧ 398 ≤ 1238 := by norm_num

private theorem threshold399 : certThresholdDataValid eb399.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg71⟩

private theorem indexOk399 : 0 < 399 ∧ 399 ≤ 1238 := by norm_num

private theorem threshold402 : certThresholdDataValid eb402.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg71⟩

private theorem indexOk402 : 0 < 402 ∧ 402 ≤ 1238 := by norm_num

private theorem threshold403 : certThresholdDataValid eb403.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk403 : 0 < 403 ∧ 403 ≤ 1238 := by norm_num

private theorem threshold404 : certThresholdDataValid eb404.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk404 : 0 < 404 ∧ 404 ≤ 1238 := by norm_num

private theorem threshold405 : certThresholdDataValid eb405.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk405 : 0 < 405 ∧ 405 ≤ 1238 := by norm_num

private theorem threshold406 : certThresholdDataValid eb406.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg73⟩

private theorem indexOk406 : 0 < 406 ∧ 406 ≤ 1238 := by norm_num

private theorem threshold408 : certThresholdDataValid eb408.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg70⟩

private theorem indexOk408 : 0 < 408 ∧ 408 ≤ 1238 := by norm_num

private theorem threshold411 : certThresholdDataValid eb411.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg74⟩

private theorem indexOk411 : 0 < 411 ∧ 411 ≤ 1238 := by norm_num

private theorem threshold412 : certThresholdDataValid eb412.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk412 : 0 < 412 ∧ 412 ≤ 1238 := by norm_num

private theorem threshold414 : certThresholdDataValid eb414.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk414 : 0 < 414 ∧ 414 ≤ 1238 := by norm_num

private theorem threshold415 : certThresholdDataValid eb415.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk415 : 0 < 415 ∧ 415 ≤ 1238 := by norm_num

private theorem threshold416 : certThresholdDataValid eb416.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg74⟩

private theorem indexOk416 : 0 < 416 ∧ 416 ≤ 1238 := by norm_num

private theorem threshold419 : certThresholdDataValid eb419.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk419 : 0 < 419 ∧ 419 ≤ 1238 := by norm_num

private theorem threshold420 : certThresholdDataValid eb420.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg78⟩

private theorem indexOk420 : 0 < 420 ∧ 420 ≤ 1238 := by norm_num

private theorem threshold422 : certThresholdDataValid eb422.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk422 : 0 < 422 ∧ 422 ≤ 1238 := by norm_num

private theorem threshold424 : certThresholdDataValid eb424.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk424 : 0 < 424 ∧ 424 ≤ 1238 := by norm_num

private theorem threshold425 : certThresholdDataValid eb425.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk425 : 0 < 425 ∧ 425 ≤ 1238 := by norm_num

private theorem threshold426 : certThresholdDataValid eb426.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk426 : 0 < 426 ∧ 426 ≤ 1238 := by norm_num

private theorem threshold427 : certThresholdDataValid eb427.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg81⟩

private theorem indexOk427 : 0 < 427 ∧ 427 ≤ 1238 := by norm_num

private theorem threshold431 : certThresholdDataValid eb431.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk431 : 0 < 431 ∧ 431 ≤ 1238 := by norm_num

private theorem threshold432 : certThresholdDataValid eb432.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk432 : 0 < 432 ∧ 432 ≤ 1238 := by norm_num

private theorem threshold433 : certThresholdDataValid eb433.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk433 : 0 < 433 ∧ 433 ≤ 1238 := by norm_num

private theorem threshold434 : certThresholdDataValid eb434.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg81⟩

private theorem indexOk434 : 0 < 434 ∧ 434 ≤ 1238 := by norm_num

private theorem threshold435 : certThresholdDataValid eb435.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk435 : 0 < 435 ∧ 435 ≤ 1238 := by norm_num

private theorem threshold436 : certThresholdDataValid eb436.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk436 : 0 < 436 ∧ 436 ≤ 1238 := by norm_num

private theorem threshold437 : certThresholdDataValid eb437.threshold := by
  exact ⟨endpointNonneg73, endpointNonneg79⟩

private theorem indexOk437 : 0 < 437 ∧ 437 ≤ 1238 := by norm_num

private theorem threshold439 : certThresholdDataValid eb439.threshold := by
  exact ⟨endpointNonneg73, endpointNonneg79⟩

private theorem indexOk439 : 0 < 439 ∧ 439 ≤ 1238 := by norm_num

private theorem threshold440 : certThresholdDataValid eb440.threshold := by
  exact ⟨endpointNonneg73, endpointNonneg81⟩

private theorem indexOk440 : 0 < 440 ∧ 440 ≤ 1238 := by norm_num

private theorem threshold441 : certThresholdDataValid eb441.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg70⟩

private theorem indexOk441 : 0 < 441 ∧ 441 ≤ 1238 := by norm_num

private theorem threshold443 : certThresholdDataValid eb443.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk443 : 0 < 443 ∧ 443 ≤ 1238 := by norm_num

private theorem threshold446 : certThresholdDataValid eb446.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk446 : 0 < 446 ∧ 446 ≤ 1238 := by norm_num

private theorem threshold447 : certThresholdDataValid eb447.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg82⟩

private theorem indexOk447 : 0 < 447 ∧ 447 ≤ 1238 := by norm_num

private theorem threshold449 : certThresholdDataValid eb449.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk449 : 0 < 449 ∧ 449 ≤ 1238 := by norm_num

private theorem threshold450 : certThresholdDataValid eb450.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk450 : 0 < 450 ∧ 450 ≤ 1238 := by norm_num

private theorem threshold452 : certThresholdDataValid eb452.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk452 : 0 < 452 ∧ 452 ≤ 1238 := by norm_num

private theorem threshold454 : certThresholdDataValid eb454.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg81⟩

private theorem indexOk454 : 0 < 454 ∧ 454 ≤ 1238 := by norm_num

private theorem threshold455 : certThresholdDataValid eb455.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk455 : 0 < 455 ∧ 455 ≤ 1238 := by norm_num

private theorem threshold456 : certThresholdDataValid eb456.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk456 : 0 < 456 ∧ 456 ≤ 1238 := by norm_num

private theorem threshold457 : certThresholdDataValid eb457.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg74⟩

private theorem indexOk457 : 0 < 457 ∧ 457 ≤ 1238 := by norm_num

private theorem threshold460 : certThresholdDataValid eb460.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg74⟩

private theorem indexOk460 : 0 < 460 ∧ 460 ≤ 1238 := by norm_num

private theorem threshold461 : certThresholdDataValid eb461.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk461 : 0 < 461 ∧ 461 ≤ 1238 := by norm_num

private theorem threshold462 : certThresholdDataValid eb462.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk462 : 0 < 462 ∧ 462 ≤ 1238 := by norm_num

private theorem threshold463 : certThresholdDataValid eb463.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk463 : 0 < 463 ∧ 463 ≤ 1238 := by norm_num

private theorem threshold464 : certThresholdDataValid eb464.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg78⟩

private theorem indexOk464 : 0 < 464 ∧ 464 ≤ 1238 := by norm_num

private theorem threshold466 : certThresholdDataValid eb466.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg43⟩

private theorem indexOk466 : 0 < 466 ∧ 466 ≤ 1238 := by norm_num

private theorem threshold468 : certThresholdDataValid eb468.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg43⟩

private theorem indexOk468 : 0 < 468 ∧ 468 ≤ 1238 := by norm_num

private theorem threshold469 : certThresholdDataValid eb469.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk469 : 0 < 469 ∧ 469 ≤ 1238 := by norm_num

private theorem threshold470 : certThresholdDataValid eb470.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg45⟩

private theorem indexOk470 : 0 < 470 ∧ 470 ≤ 1238 := by norm_num

private theorem threshold471 : certThresholdDataValid eb471.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg43⟩

private theorem indexOk471 : 0 < 471 ∧ 471 ≤ 1238 := by norm_num

private theorem threshold472 : certThresholdDataValid eb472.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg43⟩

private theorem indexOk472 : 0 < 472 ∧ 472 ≤ 1238 := by norm_num

private theorem threshold473 : certThresholdDataValid eb473.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg45⟩

private theorem indexOk473 : 0 < 473 ∧ 473 ≤ 1238 := by norm_num

private theorem threshold474 : certThresholdDataValid eb474.threshold := by
  exact ⟨endpointNonneg78, endpointNonneg43⟩

private theorem indexOk474 : 0 < 474 ∧ 474 ≤ 1238 := by norm_num

private theorem threshold475 : certThresholdDataValid eb475.threshold := by
  exact ⟨endpointNonneg78, endpointNonneg43⟩

private theorem indexOk475 : 0 < 475 ∧ 475 ≤ 1238 := by norm_num

private theorem threshold476 : certThresholdDataValid eb476.threshold := by
  exact ⟨endpointNonneg78, endpointNonneg45⟩

private theorem indexOk476 : 0 < 476 ∧ 476 ≤ 1238 := by norm_num

private theorem threshold477 : certThresholdDataValid eb477.threshold := by
  exact ⟨endpointNonneg79, endpointNonneg34⟩

private theorem indexOk477 : 0 < 477 ∧ 477 ≤ 1238 := by norm_num

private theorem threshold478 : certThresholdDataValid eb478.threshold := by
  exact ⟨endpointNonneg79, endpointNonneg34⟩

private theorem indexOk478 : 0 < 478 ∧ 478 ≤ 1238 := by norm_num

private theorem threshold479 : certThresholdDataValid eb479.threshold := by
  exact ⟨endpointNonneg81, endpointNonneg34⟩

private theorem indexOk479 : 0 < 479 ∧ 479 ≤ 1238 := by norm_num

private theorem threshold480 : certThresholdDataValid eb480.threshold := by
  exact ⟨endpointNonneg79, endpointNonneg34⟩

private theorem indexOk480 : 0 < 480 ∧ 480 ≤ 1238 := by norm_num

private theorem threshold481 : certThresholdDataValid eb481.threshold := by
  exact ⟨endpointNonneg79, endpointNonneg34⟩

private theorem indexOk481 : 0 < 481 ∧ 481 ≤ 1238 := by norm_num

private theorem threshold482 : certThresholdDataValid eb482.threshold := by
  exact ⟨endpointNonneg81, endpointNonneg34⟩

private theorem indexOk482 : 0 < 482 ∧ 482 ≤ 1238 := by norm_num

private theorem threshold483 : certThresholdDataValid eb483.threshold := by
  exact ⟨endpointNonneg79, endpointNonneg47⟩

private theorem indexOk483 : 0 < 483 ∧ 483 ≤ 1238 := by norm_num

private theorem threshold484 : certThresholdDataValid eb484.threshold := by
  exact ⟨endpointNonneg79, endpointNonneg47⟩

private theorem indexOk484 : 0 < 484 ∧ 484 ≤ 1238 := by norm_num

private theorem threshold485 : certThresholdDataValid eb485.threshold := by
  exact ⟨endpointNonneg81, endpointNonneg47⟩

private theorem indexOk485 : 0 < 485 ∧ 485 ≤ 1238 := by norm_num

private theorem threshold486 : certThresholdDataValid eb486.threshold := by
  exact ⟨endpointNonneg83, endpointNonneg38⟩

private theorem indexOk486 : 0 < 486 ∧ 486 ≤ 1238 := by norm_num

private theorem threshold487 : certThresholdDataValid eb487.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg38⟩

private theorem indexOk487 : 0 < 487 ∧ 487 ≤ 1238 := by norm_num

private theorem threshold488 : certThresholdDataValid eb488.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk488 : 0 < 488 ∧ 488 ≤ 1238 := by norm_num

private theorem threshold490 : certThresholdDataValid eb490.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk490 : 0 < 490 ∧ 490 ≤ 1238 := by norm_num

private theorem threshold491 : certThresholdDataValid eb491.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk491 : 0 < 491 ∧ 491 ≤ 1238 := by norm_num

private theorem threshold494 : certThresholdDataValid eb494.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg56⟩

private theorem indexOk494 : 0 < 494 ∧ 494 ≤ 1238 := by norm_num

private theorem threshold495 : certThresholdDataValid eb495.threshold := by
  exact ⟨endpointNonneg83, endpointNonneg38⟩

private theorem indexOk495 : 0 < 495 ∧ 495 ≤ 1238 := by norm_num

private theorem threshold496 : certThresholdDataValid eb496.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg56⟩

private theorem indexOk496 : 0 < 496 ∧ 496 ≤ 1238 := by norm_num

private theorem threshold497 : certThresholdDataValid eb497.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg56⟩

private theorem indexOk497 : 0 < 497 ∧ 497 ≤ 1238 := by norm_num

private theorem threshold498 : certThresholdDataValid eb498.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk498 : 0 < 498 ∧ 498 ≤ 1238 := by norm_num

private theorem threshold499 : certThresholdDataValid eb499.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk499 : 0 < 499 ∧ 499 ≤ 1238 := by norm_num

private theorem threshold500 : certThresholdDataValid eb500.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg40⟩

private theorem indexOk500 : 0 < 500 ∧ 500 ≤ 1238 := by norm_num

private theorem threshold501 : certThresholdDataValid eb501.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk501 : 0 < 501 ∧ 501 ≤ 1238 := by norm_num

private theorem threshold502 : certThresholdDataValid eb502.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk502 : 0 < 502 ∧ 502 ≤ 1238 := by norm_num

private theorem threshold503 : certThresholdDataValid eb503.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg40⟩

private theorem indexOk503 : 0 < 503 ∧ 503 ≤ 1238 := by norm_num

private theorem threshold504 : certThresholdDataValid eb504.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg35⟩

private theorem indexOk504 : 0 < 504 ∧ 504 ≤ 1238 := by norm_num

private theorem threshold505 : certThresholdDataValid eb505.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg35⟩

private theorem indexOk505 : 0 < 505 ∧ 505 ≤ 1238 := by norm_num

private theorem threshold506 : certThresholdDataValid eb506.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg40⟩

private theorem indexOk506 : 0 < 506 ∧ 506 ≤ 1238 := by norm_num

private theorem threshold507 : certThresholdDataValid eb507.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk507 : 0 < 507 ∧ 507 ≤ 1238 := by norm_num

private theorem threshold510 : certThresholdDataValid eb510.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk510 : 0 < 510 ∧ 510 ≤ 1238 := by norm_num

private theorem threshold512 : certThresholdDataValid eb512.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk512 : 0 < 512 ∧ 512 ≤ 1238 := by norm_num

private theorem threshold513 : certThresholdDataValid eb513.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk513 : 0 < 513 ∧ 513 ≤ 1238 := by norm_num

private theorem threshold516 : certThresholdDataValid eb516.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk516 : 0 < 516 ∧ 516 ≤ 1238 := by norm_num

private theorem threshold519 : certThresholdDataValid eb519.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg43⟩

private theorem indexOk519 : 0 < 519 ∧ 519 ≤ 1238 := by norm_num

private theorem threshold522 : certThresholdDataValid eb522.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk522 : 0 < 522 ∧ 522 ≤ 1238 := by norm_num

private theorem threshold523 : certThresholdDataValid eb523.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk523 : 0 < 523 ∧ 523 ≤ 1238 := by norm_num

private theorem threshold524 : certThresholdDataValid eb524.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg40⟩

private theorem indexOk524 : 0 < 524 ∧ 524 ≤ 1238 := by norm_num

private theorem threshold525 : certThresholdDataValid eb525.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk525 : 0 < 525 ∧ 525 ≤ 1238 := by norm_num

private theorem threshold526 : certThresholdDataValid eb526.threshold := by
  exact ⟨endpointNonneg83, endpointNonneg38⟩

private theorem indexOk526 : 0 < 526 ∧ 526 ≤ 1238 := by norm_num

private theorem threshold527 : certThresholdDataValid eb527.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk527 : 0 < 527 ∧ 527 ≤ 1238 := by norm_num

private theorem threshold528 : certThresholdDataValid eb528.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk528 : 0 < 528 ∧ 528 ≤ 1238 := by norm_num

private theorem threshold529 : certThresholdDataValid eb529.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk529 : 0 < 529 ∧ 529 ≤ 1238 := by norm_num

private theorem threshold531 : certThresholdDataValid eb531.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg55⟩

private theorem indexOk531 : 0 < 531 ∧ 531 ≤ 1238 := by norm_num

private theorem threshold532 : certThresholdDataValid eb532.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk532 : 0 < 532 ∧ 532 ≤ 1238 := by norm_num

private theorem threshold534 : certThresholdDataValid eb534.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg56⟩

private theorem indexOk534 : 0 < 534 ∧ 534 ≤ 1238 := by norm_num

private theorem threshold535 : certThresholdDataValid eb535.threshold := by
  exact ⟨endpointNonneg83, endpointNonneg38⟩

private theorem indexOk535 : 0 < 535 ∧ 535 ≤ 1238 := by norm_num

private theorem threshold536 : certThresholdDataValid eb536.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg56⟩

private theorem indexOk536 : 0 < 536 ∧ 536 ≤ 1238 := by norm_num

private theorem threshold537 : certThresholdDataValid eb537.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg56⟩

private theorem indexOk537 : 0 < 537 ∧ 537 ≤ 1238 := by norm_num

private theorem threshold538 : certThresholdDataValid eb538.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk538 : 0 < 538 ∧ 538 ≤ 1238 := by norm_num

private theorem threshold539 : certThresholdDataValid eb539.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk539 : 0 < 539 ∧ 539 ≤ 1238 := by norm_num

private theorem threshold540 : certThresholdDataValid eb540.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg65⟩

private theorem indexOk540 : 0 < 540 ∧ 540 ≤ 1238 := by norm_num

private theorem threshold545 : certThresholdDataValid eb545.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk545 : 0 < 545 ∧ 545 ≤ 1238 := by norm_num

private theorem threshold547 : certThresholdDataValid eb547.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg65⟩

private theorem indexOk547 : 0 < 547 ∧ 547 ≤ 1238 := by norm_num

private theorem threshold550 : certThresholdDataValid eb550.threshold := by
  exact ⟨endpointNonneg56, endpointNonneg65⟩

private theorem indexOk550 : 0 < 550 ∧ 550 ≤ 1238 := by norm_num

private theorem threshold553 : certThresholdDataValid eb553.threshold := by
  exact ⟨endpointNonneg35, endpointNonneg64⟩

private theorem indexOk553 : 0 < 553 ∧ 553 ≤ 1238 := by norm_num

private theorem threshold554 : certThresholdDataValid eb554.threshold := by
  exact ⟨endpointNonneg35, endpointNonneg64⟩

private theorem indexOk554 : 0 < 554 ∧ 554 ≤ 1238 := by norm_num

private theorem threshold555 : certThresholdDataValid eb555.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg64⟩

private theorem indexOk555 : 0 < 555 ∧ 555 ≤ 1238 := by norm_num

private theorem threshold556 : certThresholdDataValid eb556.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg65⟩

private theorem indexOk556 : 0 < 556 ∧ 556 ≤ 1238 := by norm_num

private theorem threshold557 : certThresholdDataValid eb557.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg65⟩

private theorem indexOk557 : 0 < 557 ∧ 557 ≤ 1238 := by norm_num

private theorem threshold558 : certThresholdDataValid eb558.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg67⟩

private theorem indexOk558 : 0 < 558 ∧ 558 ≤ 1238 := by norm_num

private theorem threshold559 : certThresholdDataValid eb559.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg77⟩

private theorem indexOk559 : 0 < 559 ∧ 559 ≤ 1238 := by norm_num

private theorem threshold560 : certThresholdDataValid eb560.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk560 : 0 < 560 ∧ 560 ≤ 1238 := by norm_num

private theorem threshold564 : certThresholdDataValid eb564.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg82⟩

private theorem indexOk564 : 0 < 564 ∧ 564 ≤ 1238 := by norm_num

private theorem threshold567 : certThresholdDataValid eb567.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk567 : 0 < 567 ∧ 567 ≤ 1238 := by norm_num

private theorem threshold568 : certThresholdDataValid eb568.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk568 : 0 < 568 ∧ 568 ≤ 1238 := by norm_num

private theorem threshold569 : certThresholdDataValid eb569.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk569 : 0 < 569 ∧ 569 ≤ 1238 := by norm_num

private theorem threshold570 : certThresholdDataValid eb570.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg82⟩

private theorem indexOk570 : 0 < 570 ∧ 570 ≤ 1238 := by norm_num

private theorem threshold571 : certThresholdDataValid eb571.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg81⟩

private theorem indexOk571 : 0 < 571 ∧ 571 ≤ 1238 := by norm_num

private theorem threshold573 : certThresholdDataValid eb573.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk573 : 0 < 573 ∧ 573 ≤ 1238 := by norm_num

private theorem threshold575 : certThresholdDataValid eb575.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg79⟩

private theorem indexOk575 : 0 < 575 ∧ 575 ≤ 1238 := by norm_num

private theorem threshold576 : certThresholdDataValid eb576.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg81⟩

private theorem indexOk576 : 0 < 576 ∧ 576 ≤ 1238 := by norm_num

private theorem threshold577 : certThresholdDataValid eb577.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk577 : 0 < 577 ∧ 577 ≤ 1238 := by norm_num

private theorem threshold578 : certThresholdDataValid eb578.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk578 : 0 < 578 ∧ 578 ≤ 1238 := by norm_num

private theorem threshold579 : certThresholdDataValid eb579.threshold := by
  exact ⟨endpointNonneg73, endpointNonneg79⟩

private theorem indexOk579 : 0 < 579 ∧ 579 ≤ 1238 := by norm_num

private theorem threshold581 : certThresholdDataValid eb581.threshold := by
  exact ⟨endpointNonneg73, endpointNonneg79⟩

private theorem indexOk581 : 0 < 581 ∧ 581 ≤ 1238 := by norm_num

private theorem threshold582 : certThresholdDataValid eb582.threshold := by
  exact ⟨endpointNonneg73, endpointNonneg81⟩

private theorem indexOk582 : 0 < 582 ∧ 582 ≤ 1238 := by norm_num

private theorem threshold583 : certThresholdDataValid eb583.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg84⟩

private theorem indexOk583 : 0 < 583 ∧ 583 ≤ 1238 := by norm_num

private theorem threshold584 : certThresholdDataValid eb584.threshold := by
  exact ⟨endpointNonneg85, endpointNonneg82⟩

private theorem indexOk584 : 0 < 584 ∧ 584 ≤ 1238 := by norm_num

private theorem threshold585 : certThresholdDataValid eb585.threshold := by
  exact ⟨endpointNonneg86, endpointNonneg82⟩

private theorem indexOk585 : 0 < 585 ∧ 585 ≤ 1238 := by norm_num

private theorem threshold586 : certThresholdDataValid eb586.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg84⟩

private theorem indexOk586 : 0 < 586 ∧ 586 ≤ 1238 := by norm_num

private theorem threshold590 : certThresholdDataValid eb590.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg87⟩

private theorem indexOk590 : 0 < 590 ∧ 590 ≤ 1238 := by norm_num

private theorem threshold591 : certThresholdDataValid eb591.threshold := by
  exact ⟨endpointNonneg85, endpointNonneg82⟩

private theorem indexOk591 : 0 < 591 ∧ 591 ≤ 1238 := by norm_num

private theorem threshold592 : certThresholdDataValid eb592.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg79⟩

private theorem indexOk592 : 0 < 592 ∧ 592 ≤ 1238 := by norm_num

private theorem threshold595 : certThresholdDataValid eb595.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg79⟩

private theorem indexOk595 : 0 < 595 ∧ 595 ≤ 1238 := by norm_num

private theorem threshold598 : certThresholdDataValid eb598.threshold := by
  exact ⟨endpointNonneg87, endpointNonneg79⟩

private theorem indexOk598 : 0 < 598 ∧ 598 ≤ 1238 := by norm_num

private theorem threshold601 : certThresholdDataValid eb601.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg77⟩

private theorem indexOk601 : 0 < 601 ∧ 601 ≤ 1238 := by norm_num

private theorem threshold603 : certThresholdDataValid eb603.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk603 : 0 < 603 ∧ 603 ≤ 1238 := by norm_num

private theorem threshold604 : certThresholdDataValid eb604.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg74⟩

private theorem indexOk604 : 0 < 604 ∧ 604 ≤ 1238 := by norm_num

private theorem threshold606 : certThresholdDataValid eb606.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg74⟩

private theorem indexOk606 : 0 < 606 ∧ 606 ≤ 1238 := by norm_num

private theorem threshold607 : certThresholdDataValid eb607.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk607 : 0 < 607 ∧ 607 ≤ 1238 := by norm_num

private theorem threshold608 : certThresholdDataValid eb608.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk608 : 0 < 608 ∧ 608 ≤ 1238 := by norm_num

private theorem threshold609 : certThresholdDataValid eb609.threshold := by
  exact ⟨endpointNonneg70, endpointNonneg78⟩

private theorem indexOk609 : 0 < 609 ∧ 609 ≤ 1238 := by norm_num

private theorem threshold611 : certThresholdDataValid eb611.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk611 : 0 < 611 ∧ 611 ≤ 1238 := by norm_num

private theorem threshold612 : certThresholdDataValid eb612.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk612 : 0 < 612 ∧ 612 ≤ 1238 := by norm_num

private theorem threshold613 : certThresholdDataValid eb613.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg81⟩

private theorem indexOk613 : 0 < 613 ∧ 613 ≤ 1238 := by norm_num

private theorem threshold620 : certThresholdDataValid eb620.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk620 : 0 < 620 ∧ 620 ≤ 1238 := by norm_num

private theorem threshold621 : certThresholdDataValid eb621.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk621 : 0 < 621 ∧ 621 ≤ 1238 := by norm_num

private theorem threshold627 : certThresholdDataValid eb627.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg43⟩

private theorem indexOk627 : 0 < 627 ∧ 627 ≤ 1238 := by norm_num

private theorem threshold630 : certThresholdDataValid eb630.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk630 : 0 < 630 ∧ 630 ≤ 1238 := by norm_num

private theorem threshold631 : certThresholdDataValid eb631.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk631 : 0 < 631 ∧ 631 ≤ 1238 := by norm_num

private theorem threshold632 : certThresholdDataValid eb632.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg40⟩

private theorem indexOk632 : 0 < 632 ∧ 632 ≤ 1238 := by norm_num

private theorem threshold639 : certThresholdDataValid eb639.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg27⟩

private theorem indexOk639 : 0 < 639 ∧ 639 ≤ 1238 := by norm_num

private theorem threshold642 : certThresholdDataValid eb642.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg27⟩

private theorem indexOk642 : 0 < 642 ∧ 642 ≤ 1238 := by norm_num

private theorem threshold645 : certThresholdDataValid eb645.threshold := by
  exact ⟨endpointNonneg88, endpointNonneg89⟩

private theorem indexOk645 : 0 < 645 ∧ 645 ≤ 1238 := by norm_num

private theorem threshold646 : certThresholdDataValid eb646.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk646 : 0 < 646 ∧ 646 ≤ 1238 := by norm_num

private theorem threshold647 : certThresholdDataValid eb647.threshold := by
  exact ⟨endpointNonneg92, endpointNonneg89⟩

private theorem indexOk647 : 0 < 647 ∧ 647 ≤ 1238 := by norm_num

private theorem threshold648 : certThresholdDataValid eb648.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg94⟩

private theorem indexOk648 : 0 < 648 ∧ 648 ≤ 1238 := by norm_num

private theorem threshold654 : certThresholdDataValid eb654.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk654 : 0 < 654 ∧ 654 ≤ 1238 := by norm_num

private theorem threshold655 : certThresholdDataValid eb655.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg95⟩

private theorem indexOk655 : 0 < 655 ∧ 655 ≤ 1238 := by norm_num

private theorem threshold656 : certThresholdDataValid eb656.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg94⟩

private theorem indexOk656 : 0 < 656 ∧ 656 ≤ 1238 := by norm_num

private theorem threshold657 : certThresholdDataValid eb657.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg96⟩

private theorem indexOk657 : 0 < 657 ∧ 657 ≤ 1238 := by norm_num

private theorem threshold666 : certThresholdDataValid eb666.threshold := by
  exact ⟨endpointNonneg88, endpointNonneg89⟩

private theorem indexOk666 : 0 < 666 ∧ 666 ≤ 1238 := by norm_num

private theorem threshold669 : certThresholdDataValid eb669.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg89⟩

private theorem indexOk669 : 0 < 669 ∧ 669 ≤ 1238 := by norm_num

private theorem threshold670 : certThresholdDataValid eb670.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg70⟩

private theorem indexOk670 : 0 < 670 ∧ 670 ≤ 1238 := by norm_num

private theorem threshold673 : certThresholdDataValid eb673.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk673 : 0 < 673 ∧ 673 ≤ 1238 := by norm_num

private theorem threshold677 : certThresholdDataValid eb677.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk677 : 0 < 677 ∧ 677 ≤ 1238 := by norm_num

private theorem threshold679 : certThresholdDataValid eb679.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk679 : 0 < 679 ∧ 679 ≤ 1238 := by norm_num

private theorem threshold680 : certThresholdDataValid eb680.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk680 : 0 < 680 ∧ 680 ≤ 1238 := by norm_num

private theorem threshold683 : certThresholdDataValid eb683.threshold := by
  exact ⟨endpointNonneg88, endpointNonneg89⟩

private theorem indexOk683 : 0 < 683 ∧ 683 ≤ 1238 := by norm_num

private theorem threshold684 : certThresholdDataValid eb684.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk684 : 0 < 684 ∧ 684 ≤ 1238 := by norm_num

private theorem threshold685 : certThresholdDataValid eb685.threshold := by
  exact ⟨endpointNonneg92, endpointNonneg89⟩

private theorem indexOk685 : 0 < 685 ∧ 685 ≤ 1238 := by norm_num

private theorem threshold686 : certThresholdDataValid eb686.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg94⟩

private theorem indexOk686 : 0 < 686 ∧ 686 ≤ 1238 := by norm_num

private theorem threshold692 : certThresholdDataValid eb692.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk692 : 0 < 692 ∧ 692 ≤ 1238 := by norm_num

private theorem threshold695 : certThresholdDataValid eb695.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg96⟩

private theorem indexOk695 : 0 < 695 ∧ 695 ≤ 1238 := by norm_num

private theorem threshold704 : certThresholdDataValid eb704.threshold := by
  exact ⟨endpointNonneg88, endpointNonneg89⟩

private theorem indexOk704 : 0 < 704 ∧ 704 ≤ 1238 := by norm_num

private theorem threshold708 : certThresholdDataValid eb708.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg70⟩

private theorem indexOk708 : 0 < 708 ∧ 708 ≤ 1238 := by norm_num

private theorem threshold711 : certThresholdDataValid eb711.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk711 : 0 < 711 ∧ 711 ≤ 1238 := by norm_num

private theorem threshold715 : certThresholdDataValid eb715.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk715 : 0 < 715 ∧ 715 ≤ 1238 := by norm_num

private theorem threshold717 : certThresholdDataValid eb717.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk717 : 0 < 717 ∧ 717 ≤ 1238 := by norm_num

private theorem threshold718 : certThresholdDataValid eb718.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk718 : 0 < 718 ∧ 718 ≤ 1238 := by norm_num

private theorem threshold721 : certThresholdDataValid eb721.threshold := by
  exact ⟨endpointNonneg85, endpointNonneg82⟩

private theorem indexOk721 : 0 < 721 ∧ 721 ≤ 1238 := by norm_num

private theorem threshold722 : certThresholdDataValid eb722.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg97⟩

private theorem indexOk722 : 0 < 722 ∧ 722 ≤ 1238 := by norm_num

private theorem threshold723 : certThresholdDataValid eb723.threshold := by
  exact ⟨endpointNonneg86, endpointNonneg82⟩

private theorem indexOk723 : 0 < 723 ∧ 723 ≤ 1238 := by norm_num

private theorem threshold724 : certThresholdDataValid eb724.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg99⟩

private theorem indexOk724 : 0 < 724 ∧ 724 ≤ 1238 := by norm_num

private theorem threshold730 : certThresholdDataValid eb730.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg97⟩

private theorem indexOk730 : 0 < 730 ∧ 730 ≤ 1238 := by norm_num

private theorem threshold731 : certThresholdDataValid eb731.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg100⟩

private theorem indexOk731 : 0 < 731 ∧ 731 ≤ 1238 := by norm_num

private theorem threshold733 : certThresholdDataValid eb733.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg101⟩

private theorem indexOk733 : 0 < 733 ∧ 733 ≤ 1238 := by norm_num

private theorem threshold742 : certThresholdDataValid eb742.threshold := by
  exact ⟨endpointNonneg85, endpointNonneg82⟩

private theorem indexOk742 : 0 < 742 ∧ 742 ≤ 1238 := by norm_num

private theorem threshold746 : certThresholdDataValid eb746.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk746 : 0 < 746 ∧ 746 ≤ 1238 := by norm_num

private theorem threshold751 : certThresholdDataValid eb751.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk751 : 0 < 751 ∧ 751 ≤ 1238 := by norm_num

private theorem threshold755 : certThresholdDataValid eb755.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg81⟩

private theorem indexOk755 : 0 < 755 ∧ 755 ≤ 1238 := by norm_num

private theorem threshold757 : certThresholdDataValid eb757.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk757 : 0 < 757 ∧ 757 ≤ 1238 := by norm_num

private theorem threshold761 : certThresholdDataValid eb761.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk761 : 0 < 761 ∧ 761 ≤ 1238 := by norm_num

private theorem threshold765 : certThresholdDataValid eb765.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk765 : 0 < 765 ∧ 765 ≤ 1238 := by norm_num

private theorem threshold766 : certThresholdDataValid eb766.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk766 : 0 < 766 ∧ 766 ≤ 1238 := by norm_num

private theorem threshold771 : certThresholdDataValid eb771.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg95⟩

private theorem indexOk771 : 0 < 771 ∧ 771 ≤ 1238 := by norm_num

private theorem threshold772 : certThresholdDataValid eb772.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk772 : 0 < 772 ∧ 772 ≤ 1238 := by norm_num

private theorem threshold773 : certThresholdDataValid eb773.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg94⟩

private theorem indexOk773 : 0 < 773 ∧ 773 ≤ 1238 := by norm_num

private theorem threshold780 : certThresholdDataValid eb780.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg95⟩

private theorem indexOk780 : 0 < 780 ∧ 780 ≤ 1238 := by norm_num

private theorem threshold783 : certThresholdDataValid eb783.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk783 : 0 < 783 ∧ 783 ≤ 1238 := by norm_num

private theorem threshold788 : certThresholdDataValid eb788.threshold := by
  exact ⟨endpointNonneg102, endpointNonneg91⟩

private theorem indexOk788 : 0 < 788 ∧ 788 ≤ 1238 := by norm_num

private theorem threshold792 : certThresholdDataValid eb792.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg70⟩

private theorem indexOk792 : 0 < 792 ∧ 792 ≤ 1238 := by norm_num

private theorem threshold795 : certThresholdDataValid eb795.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk795 : 0 < 795 ∧ 795 ≤ 1238 := by norm_num

private theorem threshold797 : certThresholdDataValid eb797.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk797 : 0 < 797 ∧ 797 ≤ 1238 := by norm_num

private theorem threshold798 : certThresholdDataValid eb798.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk798 : 0 < 798 ∧ 798 ≤ 1238 := by norm_num

private theorem threshold801 : certThresholdDataValid eb801.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg95⟩

private theorem indexOk801 : 0 < 801 ∧ 801 ≤ 1238 := by norm_num

private theorem threshold802 : certThresholdDataValid eb802.threshold := by
  exact ⟨endpointNonneg90, endpointNonneg91⟩

private theorem indexOk802 : 0 < 802 ∧ 802 ≤ 1238 := by norm_num

private theorem threshold803 : certThresholdDataValid eb803.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg94⟩

private theorem indexOk803 : 0 < 803 ∧ 803 ≤ 1238 := by norm_num

private theorem threshold808 : certThresholdDataValid eb808.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg95⟩

private theorem indexOk808 : 0 < 808 ∧ 808 ≤ 1238 := by norm_num

private theorem threshold810 : certThresholdDataValid eb810.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg70⟩

private theorem indexOk810 : 0 < 810 ∧ 810 ≤ 1238 := by norm_num

private theorem threshold813 : certThresholdDataValid eb813.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk813 : 0 < 813 ∧ 813 ≤ 1238 := by norm_num

private theorem threshold815 : certThresholdDataValid eb815.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg29⟩

private theorem indexOk815 : 0 < 815 ∧ 815 ≤ 1238 := by norm_num

private theorem threshold816 : certThresholdDataValid eb816.threshold := by
  exact ⟨endpointNonneg28, endpointNonneg29⟩

private theorem indexOk816 : 0 < 816 ∧ 816 ≤ 1238 := by norm_num

private theorem threshold819 : certThresholdDataValid eb819.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg100⟩

private theorem indexOk819 : 0 < 819 ∧ 819 ≤ 1238 := by norm_num

private theorem threshold820 : certThresholdDataValid eb820.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg97⟩

private theorem indexOk820 : 0 < 820 ∧ 820 ≤ 1238 := by norm_num

private theorem threshold821 : certThresholdDataValid eb821.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg99⟩

private theorem indexOk821 : 0 < 821 ∧ 821 ≤ 1238 := by norm_num

private theorem threshold827 : certThresholdDataValid eb827.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg100⟩

private theorem indexOk827 : 0 < 827 ∧ 827 ≤ 1238 := by norm_num

private theorem threshold830 : certThresholdDataValid eb830.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg97⟩

private theorem indexOk830 : 0 < 830 ∧ 830 ≤ 1238 := by norm_num

private theorem threshold834 : certThresholdDataValid eb834.threshold := by
  exact ⟨endpointNonneg87, endpointNonneg97⟩

private theorem indexOk834 : 0 < 834 ∧ 834 ≤ 1238 := by norm_num

private theorem threshold838 : certThresholdDataValid eb838.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk838 : 0 < 838 ∧ 838 ≤ 1238 := by norm_num

private theorem threshold842 : certThresholdDataValid eb842.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk842 : 0 < 842 ∧ 842 ≤ 1238 := by norm_num

private theorem threshold845 : certThresholdDataValid eb845.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg81⟩

private theorem indexOk845 : 0 < 845 ∧ 845 ≤ 1238 := by norm_num

private theorem threshold847 : certThresholdDataValid eb847.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk847 : 0 < 847 ∧ 847 ≤ 1238 := by norm_num

private theorem threshold851 : certThresholdDataValid eb851.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk851 : 0 < 851 ∧ 851 ≤ 1238 := by norm_num

private theorem threshold852 : certThresholdDataValid eb852.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk852 : 0 < 852 ∧ 852 ≤ 1238 := by norm_num

private theorem threshold857 : certThresholdDataValid eb857.threshold := by
  exact ⟨endpointNonneg103, endpointNonneg104⟩

private theorem indexOk857 : 0 < 857 ∧ 857 ≤ 1238 := by norm_num

private theorem threshold858 : certThresholdDataValid eb858.threshold := by
  exact ⟨endpointNonneg105, endpointNonneg106⟩

private theorem indexOk858 : 0 < 858 ∧ 858 ≤ 1238 := by norm_num

private theorem threshold859 : certThresholdDataValid eb859.threshold := by
  exact ⟨endpointNonneg107, endpointNonneg104⟩

private theorem indexOk859 : 0 < 859 ∧ 859 ≤ 1238 := by norm_num

private theorem threshold862 : certThresholdDataValid eb862.threshold := by
  exact ⟨endpointNonneg105, endpointNonneg106⟩

private theorem indexOk862 : 0 < 862 ∧ 862 ≤ 1238 := by norm_num

private theorem threshold864 : certThresholdDataValid eb864.threshold := by
  exact ⟨endpointNonneg105, endpointNonneg108⟩

private theorem indexOk864 : 0 < 864 ∧ 864 ≤ 1238 := by norm_num

private theorem threshold872 : certThresholdDataValid eb872.threshold := by
  exact ⟨endpointNonneg103, endpointNonneg104⟩

private theorem indexOk872 : 0 < 872 ∧ 872 ≤ 1238 := by norm_num

private theorem threshold876 : certThresholdDataValid eb876.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk876 : 0 < 876 ∧ 876 ≤ 1238 := by norm_num

private theorem threshold880 : certThresholdDataValid eb880.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk880 : 0 < 880 ∧ 880 ≤ 1238 := by norm_num

private theorem threshold885 : certThresholdDataValid eb885.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg43⟩

private theorem indexOk885 : 0 < 885 ∧ 885 ≤ 1238 := by norm_num

private theorem threshold889 : certThresholdDataValid eb889.threshold := by
  exact ⟨endpointNonneg109, endpointNonneg54⟩

private theorem indexOk889 : 0 < 889 ∧ 889 ≤ 1238 := by norm_num

private theorem threshold890 : certThresholdDataValid eb890.threshold := by
  exact ⟨endpointNonneg50, endpointNonneg51⟩

private theorem indexOk890 : 0 < 890 ∧ 890 ≤ 1238 := by norm_num

private theorem threshold891 : certThresholdDataValid eb891.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg54⟩

private theorem indexOk891 : 0 < 891 ∧ 891 ≤ 1238 := by norm_num

private theorem threshold894 : certThresholdDataValid eb894.threshold := by
  exact ⟨endpointNonneg50, endpointNonneg51⟩

private theorem indexOk894 : 0 < 894 ∧ 894 ≤ 1238 := by norm_num

private theorem threshold896 : certThresholdDataValid eb896.threshold := by
  exact ⟨endpointNonneg50, endpointNonneg110⟩

private theorem indexOk896 : 0 < 896 ∧ 896 ≤ 1238 := by norm_num

private theorem threshold904 : certThresholdDataValid eb904.threshold := by
  exact ⟨endpointNonneg109, endpointNonneg54⟩

private theorem indexOk904 : 0 < 904 ∧ 904 ≤ 1238 := by norm_num

private theorem threshold908 : certThresholdDataValid eb908.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg35⟩

private theorem indexOk908 : 0 < 908 ∧ 908 ≤ 1238 := by norm_num

private theorem threshold912 : certThresholdDataValid eb912.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk912 : 0 < 912 ∧ 912 ≤ 1238 := by norm_num

private theorem threshold914 : certThresholdDataValid eb914.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk914 : 0 < 914 ∧ 914 ≤ 1238 := by norm_num

private theorem threshold915 : certThresholdDataValid eb915.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk915 : 0 < 915 ∧ 915 ≤ 1238 := by norm_num

private theorem threshold918 : certThresholdDataValid eb918.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg35⟩

private theorem indexOk918 : 0 < 918 ∧ 918 ≤ 1238 := by norm_num

private theorem threshold923 : certThresholdDataValid eb923.threshold := by
  exact ⟨endpointNonneg56, endpointNonneg35⟩

private theorem indexOk923 : 0 < 923 ∧ 923 ≤ 1238 := by norm_num

private theorem threshold927 : certThresholdDataValid eb927.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg111⟩

private theorem indexOk927 : 0 < 927 ∧ 927 ≤ 1238 := by norm_num

private theorem threshold928 : certThresholdDataValid eb928.threshold := by
  exact ⟨endpointNonneg105, endpointNonneg106⟩

private theorem indexOk928 : 0 < 928 ∧ 928 ≤ 1238 := by norm_num

private theorem threshold929 : certThresholdDataValid eb929.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg112⟩

private theorem indexOk929 : 0 < 929 ∧ 929 ≤ 1238 := by norm_num

private theorem threshold930 : certThresholdDataValid eb930.threshold := by
  exact ⟨endpointNonneg107, endpointNonneg104⟩

private theorem indexOk930 : 0 < 930 ∧ 930 ≤ 1238 := by norm_num

private theorem threshold937 : certThresholdDataValid eb937.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg111⟩

private theorem indexOk937 : 0 < 937 ∧ 937 ≤ 1238 := by norm_num

private theorem threshold943 : certThresholdDataValid eb943.threshold := by
  exact ⟨endpointNonneg105, endpointNonneg106⟩

private theorem indexOk943 : 0 < 943 ∧ 943 ≤ 1238 := by norm_num

private theorem threshold948 : certThresholdDataValid eb948.threshold := by
  exact ⟨endpointNonneg113, endpointNonneg106⟩

private theorem indexOk948 : 0 < 948 ∧ 948 ≤ 1238 := by norm_num

private theorem threshold952 : certThresholdDataValid eb952.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk952 : 0 < 952 ∧ 952 ≤ 1238 := by norm_num

private theorem threshold960 : certThresholdDataValid eb960.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk960 : 0 < 960 ∧ 960 ≤ 1238 := by norm_num

private theorem threshold962 : certThresholdDataValid eb962.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk962 : 0 < 962 ∧ 962 ≤ 1238 := by norm_num

private theorem threshold968 : certThresholdDataValid eb968.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg43⟩

private theorem indexOk968 : 0 < 968 ∧ 968 ≤ 1238 := by norm_num

private theorem threshold972 : certThresholdDataValid eb972.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk972 : 0 < 972 ∧ 972 ≤ 1238 := by norm_num

private theorem threshold973 : certThresholdDataValid eb973.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg111⟩

private theorem indexOk973 : 0 < 973 ∧ 973 ≤ 1238 := by norm_num

private theorem threshold974 : certThresholdDataValid eb974.threshold := by
  exact ⟨endpointNonneg105, endpointNonneg106⟩

private theorem indexOk974 : 0 < 974 ∧ 974 ≤ 1238 := by norm_num

private theorem threshold975 : certThresholdDataValid eb975.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg112⟩

private theorem indexOk975 : 0 < 975 ∧ 975 ≤ 1238 := by norm_num

private theorem threshold976 : certThresholdDataValid eb976.threshold := by
  exact ⟨endpointNonneg107, endpointNonneg104⟩

private theorem indexOk976 : 0 < 976 ∧ 976 ≤ 1238 := by norm_num

private theorem threshold983 : certThresholdDataValid eb983.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg111⟩

private theorem indexOk983 : 0 < 983 ∧ 983 ≤ 1238 := by norm_num

private theorem threshold984 : certThresholdDataValid eb984.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg33⟩

private theorem indexOk984 : 0 < 984 ∧ 984 ≤ 1238 := by norm_num

private theorem threshold986 : certThresholdDataValid eb986.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk986 : 0 < 986 ∧ 986 ≤ 1238 := by norm_num

private theorem threshold994 : certThresholdDataValid eb994.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk994 : 0 < 994 ∧ 994 ≤ 1238 := by norm_num

private theorem threshold996 : certThresholdDataValid eb996.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg44⟩

private theorem indexOk996 : 0 < 996 ∧ 996 ≤ 1238 := by norm_num

private theorem threshold997 : certThresholdDataValid eb997.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk997 : 0 < 997 ∧ 997 ≤ 1238 := by norm_num

private theorem threshold1000 : certThresholdDataValid eb1000.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg43⟩

private theorem indexOk1000 : 0 < 1000 ∧ 1000 ≤ 1238 := by norm_num

private theorem threshold1006 : certThresholdDataValid eb1006.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg43⟩

private theorem indexOk1006 : 0 < 1006 ∧ 1006 ≤ 1238 := by norm_num

private theorem threshold1010 : certThresholdDataValid eb1010.threshold := by
  exact ⟨endpointNonneg41, endpointNonneg33⟩

private theorem indexOk1010 : 0 < 1010 ∧ 1010 ≤ 1238 := by norm_num

private theorem threshold1011 : certThresholdDataValid eb1011.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg49⟩

private theorem indexOk1011 : 0 < 1011 ∧ 1011 ≤ 1238 := by norm_num

private theorem threshold1012 : certThresholdDataValid eb1012.threshold := by
  exact ⟨endpointNonneg50, endpointNonneg51⟩

private theorem indexOk1012 : 0 < 1012 ∧ 1012 ≤ 1238 := by norm_num

private theorem threshold1013 : certThresholdDataValid eb1013.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg52⟩

private theorem indexOk1013 : 0 < 1013 ∧ 1013 ≤ 1238 := by norm_num

private theorem threshold1014 : certThresholdDataValid eb1014.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg54⟩

private theorem indexOk1014 : 0 < 1014 ∧ 1014 ≤ 1238 := by norm_num

private theorem threshold1021 : certThresholdDataValid eb1021.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg49⟩

private theorem indexOk1021 : 0 < 1021 ∧ 1021 ≤ 1238 := by norm_num

private theorem threshold1027 : certThresholdDataValid eb1027.threshold := by
  exact ⟨endpointNonneg50, endpointNonneg51⟩

private theorem indexOk1027 : 0 < 1027 ∧ 1027 ≤ 1238 := by norm_num

private theorem threshold1032 : certThresholdDataValid eb1032.threshold := by
  exact ⟨endpointNonneg114, endpointNonneg51⟩

private theorem indexOk1032 : 0 < 1032 ∧ 1032 ≤ 1238 := by norm_num

private theorem threshold1036 : certThresholdDataValid eb1036.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg35⟩

private theorem indexOk1036 : 0 < 1036 ∧ 1036 ≤ 1238 := by norm_num

private theorem threshold1037 : certThresholdDataValid eb1037.threshold := by
  exact ⟨endpointNonneg83, endpointNonneg38⟩

private theorem indexOk1037 : 0 < 1037 ∧ 1037 ≤ 1238 := by norm_num

private theorem threshold1044 : certThresholdDataValid eb1044.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk1044 : 0 < 1044 ∧ 1044 ≤ 1238 := by norm_num

private theorem threshold1046 : certThresholdDataValid eb1046.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg39⟩

private theorem indexOk1046 : 0 < 1046 ∧ 1046 ≤ 1238 := by norm_num

private theorem threshold1047 : certThresholdDataValid eb1047.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk1047 : 0 < 1047 ∧ 1047 ≤ 1238 := by norm_num

private theorem threshold1050 : certThresholdDataValid eb1050.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg35⟩

private theorem indexOk1050 : 0 < 1050 ∧ 1050 ≤ 1238 := by norm_num

private theorem threshold1056 : certThresholdDataValid eb1056.threshold := by
  exact ⟨endpointNonneg56, endpointNonneg35⟩

private theorem indexOk1056 : 0 < 1056 ∧ 1056 ≤ 1238 := by norm_num

private theorem threshold1060 : certThresholdDataValid eb1060.threshold := by
  exact ⟨endpointNonneg37, endpointNonneg38⟩

private theorem indexOk1060 : 0 < 1060 ∧ 1060 ≤ 1238 := by norm_num

private theorem threshold1061 : certThresholdDataValid eb1061.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg58⟩

private theorem indexOk1061 : 0 < 1061 ∧ 1061 ≤ 1238 := by norm_num

private theorem threshold1062 : certThresholdDataValid eb1062.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg60⟩

private theorem indexOk1062 : 0 < 1062 ∧ 1062 ≤ 1238 := by norm_num

private theorem threshold1063 : certThresholdDataValid eb1063.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg61⟩

private theorem indexOk1063 : 0 < 1063 ∧ 1063 ≤ 1238 := by norm_num

private theorem threshold1064 : certThresholdDataValid eb1064.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg63⟩

private theorem indexOk1064 : 0 < 1064 ∧ 1064 ≤ 1238 := by norm_num

private theorem threshold1071 : certThresholdDataValid eb1071.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg58⟩

private theorem indexOk1071 : 0 < 1071 ∧ 1071 ≤ 1238 := by norm_num

private theorem threshold1077 : certThresholdDataValid eb1077.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg60⟩

private theorem indexOk1077 : 0 < 1077 ∧ 1077 ≤ 1238 := by norm_num

private theorem threshold1082 : certThresholdDataValid eb1082.threshold := by
  exact ⟨endpointNonneg115, endpointNonneg60⟩

private theorem indexOk1082 : 0 < 1082 ∧ 1082 ≤ 1238 := by norm_num

private theorem threshold1086 : certThresholdDataValid eb1086.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg65⟩

private theorem indexOk1086 : 0 < 1086 ∧ 1086 ≤ 1238 := by norm_num

private theorem threshold1087 : certThresholdDataValid eb1087.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk1087 : 0 < 1087 ∧ 1087 ≤ 1238 := by norm_num

private theorem threshold1092 : certThresholdDataValid eb1092.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk1092 : 0 < 1092 ∧ 1092 ≤ 1238 := by norm_num

private theorem threshold1094 : certThresholdDataValid eb1094.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg66⟩

private theorem indexOk1094 : 0 < 1094 ∧ 1094 ≤ 1238 := by norm_num

private theorem threshold1095 : certThresholdDataValid eb1095.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk1095 : 0 < 1095 ∧ 1095 ≤ 1238 := by norm_num

private theorem threshold1098 : certThresholdDataValid eb1098.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg42⟩

private theorem indexOk1098 : 0 < 1098 ∧ 1098 ≤ 1238 := by norm_num

private theorem threshold1099 : certThresholdDataValid eb1099.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg97⟩

private theorem indexOk1099 : 0 < 1099 ∧ 1099 ≤ 1238 := by norm_num

private theorem threshold1100 : certThresholdDataValid eb1100.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg99⟩

private theorem indexOk1100 : 0 < 1100 ∧ 1100 ≤ 1238 := by norm_num

private theorem threshold1104 : certThresholdDataValid eb1104.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg100⟩

private theorem indexOk1104 : 0 < 1104 ∧ 1104 ≤ 1238 := by norm_num

private theorem threshold1105 : certThresholdDataValid eb1105.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg97⟩

private theorem indexOk1105 : 0 < 1105 ∧ 1105 ≤ 1238 := by norm_num

private theorem threshold1106 : certThresholdDataValid eb1106.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg100⟩

private theorem indexOk1106 : 0 < 1106 ∧ 1106 ≤ 1238 := by norm_num

private theorem threshold1107 : certThresholdDataValid eb1107.threshold := by
  exact ⟨endpointNonneg98, endpointNonneg99⟩

private theorem indexOk1107 : 0 < 1107 ∧ 1107 ≤ 1238 := by norm_num

private theorem threshold1108 : certThresholdDataValid eb1108.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg101⟩

private theorem indexOk1108 : 0 < 1108 ∧ 1108 ≤ 1238 := by norm_num

private theorem threshold1116 : certThresholdDataValid eb1116.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk1116 : 0 < 1116 ∧ 1116 ≤ 1238 := by norm_num

private theorem threshold1121 : certThresholdDataValid eb1121.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg79⟩

private theorem indexOk1121 : 0 < 1121 ∧ 1121 ≤ 1238 := by norm_num

private theorem threshold1122 : certThresholdDataValid eb1122.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk1122 : 0 < 1122 ∧ 1122 ≤ 1238 := by norm_num

private theorem threshold1123 : certThresholdDataValid eb1123.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg82⟩

private theorem indexOk1123 : 0 < 1123 ∧ 1123 ≤ 1238 := by norm_num

private theorem threshold1124 : certThresholdDataValid eb1124.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg80⟩

private theorem indexOk1124 : 0 < 1124 ∧ 1124 ≤ 1238 := by norm_num

private theorem threshold1125 : certThresholdDataValid eb1125.threshold := by
  exact ⟨endpointNonneg74, endpointNonneg81⟩

private theorem indexOk1125 : 0 < 1125 ∧ 1125 ≤ 1238 := by norm_num

private theorem threshold1127 : certThresholdDataValid eb1127.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk1127 : 0 < 1127 ∧ 1127 ≤ 1238 := by norm_num

private theorem threshold1131 : certThresholdDataValid eb1131.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk1131 : 0 < 1131 ∧ 1131 ≤ 1238 := by norm_num

private theorem threshold1135 : certThresholdDataValid eb1135.threshold := by
  exact ⟨endpointNonneg75, endpointNonneg76⟩

private theorem indexOk1135 : 0 < 1135 ∧ 1135 ≤ 1238 := by norm_num

private theorem threshold1136 : certThresholdDataValid eb1136.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg76⟩

private theorem indexOk1136 : 0 < 1136 ∧ 1136 ≤ 1238 := by norm_num

private theorem threshold1141 : certThresholdDataValid eb1141.threshold := by
  exact ⟨endpointNonneg116, endpointNonneg117⟩

private theorem indexOk1141 : 0 < 1141 ∧ 1141 ≤ 1238 := by norm_num

private theorem threshold1142 : certThresholdDataValid eb1142.threshold := by
  exact ⟨endpointNonneg118, endpointNonneg119⟩

private theorem indexOk1142 : 0 < 1142 ∧ 1142 ≤ 1238 := by norm_num

private theorem threshold1143 : certThresholdDataValid eb1143.threshold := by
  exact ⟨endpointNonneg120, endpointNonneg117⟩

private theorem indexOk1143 : 0 < 1143 ∧ 1143 ≤ 1238 := by norm_num

private theorem threshold1144 : certThresholdDataValid eb1144.threshold := by
  exact ⟨endpointNonneg86, endpointNonneg121⟩

private theorem indexOk1144 : 0 < 1144 ∧ 1144 ≤ 1238 := by norm_num

private theorem threshold1146 : certThresholdDataValid eb1146.threshold := by
  exact ⟨endpointNonneg118, endpointNonneg119⟩

private theorem indexOk1146 : 0 < 1146 ∧ 1146 ≤ 1238 := by norm_num

private theorem threshold1148 : certThresholdDataValid eb1148.threshold := by
  exact ⟨endpointNonneg118, endpointNonneg122⟩

private theorem indexOk1148 : 0 < 1148 ∧ 1148 ≤ 1238 := by norm_num

private theorem threshold1157 : certThresholdDataValid eb1157.threshold := by
  exact ⟨endpointNonneg116, endpointNonneg117⟩

private theorem indexOk1157 : 0 < 1157 ∧ 1157 ≤ 1238 := by norm_num

private theorem threshold1160 : certThresholdDataValid eb1160.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg79⟩

private theorem indexOk1160 : 0 < 1160 ∧ 1160 ≤ 1238 := by norm_num

private theorem threshold1164 : certThresholdDataValid eb1164.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg79⟩

private theorem indexOk1164 : 0 < 1164 ∧ 1164 ≤ 1238 := by norm_num

private theorem threshold1169 : certThresholdDataValid eb1169.threshold := by
  exact ⟨endpointNonneg87, endpointNonneg79⟩

private theorem indexOk1169 : 0 < 1169 ∧ 1169 ≤ 1238 := by norm_num

private theorem threshold1174 : certThresholdDataValid eb1174.threshold := by
  exact ⟨endpointNonneg32, endpointNonneg32⟩

private theorem indexOk1174 : 0 < 1174 ∧ 1174 ≤ 1238 := by norm_num

private theorem explicit_pair_valid (lid uid : ℕ) (q : ℚ) (l u : CertBound)
    (hlid : 0 < lid) (hlength : lid ≤ 1238)
    (huid : 0 < uid) (hulength : uid ≤ 1238)
    (hl : lowerEarlyTerminalBound lowerEarlyTerminalState1 lid = l)
    (hu : lowerEarlyTerminalBound lowerEarlyTerminalState1 uid = u)
    (hll : l.lower = true) (hul : u.lower = false)
    (hlt : certThresholdDataValid l.threshold)
    (hut : certThresholdDataValid u.threshold)
    (hc : ∀ i j : Fin 3, certCoefficientBoundValid
      ((certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) earlyRect) i j) q)
    (hq : 0 < q ∨ l.strict = true ∨ u.strict = true) :
    lowerEarlyTerminalPairValid lowerEarlyTerminalState1 ⟨lid,uid,q⟩ := by
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
    rcases hq with hq | hq
    · exact Or.inl (fun _ _ => hq)
    · exact Or.inr hq



private def bk1 : BoundKit true :=
  ⟨1,eb1,indexOk1.1,indexOk1.2,lookup1,rfl,threshold1,
   n281,100,pos281,cp281,ivec127,dvec127,dpos127,vp127,ivec17,dvec17,dpos17,vp17⟩

private def bk2 : BoundKit true :=
  ⟨2,eb2,indexOk2.1,indexOk2.2,lookup2,rfl,threshold2,
   n1,253,pos1,cp1,ivec3,dvec3,dpos3,vp3,ivec2,dvec2,dpos2,vp2⟩

private def bk6 : BoundKit false :=
  ⟨6,eb6,indexOk6.1,indexOk6.2,lookup6,rfl,threshold6,
   n2,10878294,pos2,cp2,ivec1,dvec1,dpos1,vp1,ivec4,dvec4,dpos4,vp4⟩

private def bk7 : BoundKit false :=
  ⟨7,eb7,indexOk7.1,indexOk7.2,lookup7,rfl,threshold7,
   n20,2379971,pos20,cp20,ivec10,dvec10,dpos10,vp10,ivec11,dvec11,dpos11,vp11⟩

private def bk8 : BoundKit false :=
  ⟨8,eb8,indexOk8.1,indexOk8.2,lookup8,rfl,threshold8,
   n18,50394,pos18,cp18,ivec9,dvec9,dpos9,vp9,ivec7,dvec7,dpos7,vp7⟩

private def bk12 : BoundKit false :=
  ⟨12,eb12,indexOk12.1,indexOk12.2,lookup12,rfl,threshold12,
   n25,11250772,pos25,cp25,ivec10,dvec10,dpos10,vp10,ivec12,dvec12,dpos12,vp12⟩

private def bk13 : BoundKit true :=
  ⟨13,eb13,indexOk13.1,indexOk13.2,lookup13,rfl,threshold13,
   n11,5050050,pos11,cp11,ivec6,dvec6,dpos6,vp6,ivec5,dvec5,dpos5,vp5⟩

private def bk14 : BoundKit true :=
  ⟨14,eb14,indexOk14.1,indexOk14.2,lookup14,rfl,threshold14,
   n16,4454,pos16,cp16,ivec8,dvec8,dpos8,vp8,ivec7,dvec7,dpos7,vp7⟩

private def bk15 : BoundKit false :=
  ⟨15,eb15,indexOk15.1,indexOk15.2,lookup15,rfl,threshold15,
   n27,6105143,pos27,cp27,ivec13,dvec13,dpos13,vp13,ivec11,dvec11,dpos11,vp11⟩

private def bk23 : BoundKit false :=
  ⟨23,eb23,indexOk23.1,indexOk23.2,lookup23,rfl,threshold23,
   n29,1110030,pos29,cp29,ivec1,dvec1,dpos1,vp1,ivec4,dvec4,dpos4,vp4⟩

private def bk27 : BoundKit true :=
  ⟨27,eb27,indexOk27.1,indexOk27.2,lookup27,rfl,threshold27,
   n88,697,pos88,cp88,ivec21,dvec21,dpos21,vp21,ivec7,dvec7,dpos7,vp7⟩

private def bk28 : BoundKit true :=
  ⟨28,eb28,indexOk28.1,indexOk28.2,lookup28,rfl,threshold28,
   n30,191958,pos30,cp30,ivec16,dvec16,dpos16,vp16,ivec15,dvec15,dpos15,vp15⟩

private def bk33 : BoundKit true :=
  ⟨33,eb33,indexOk33.1,indexOk33.2,lookup33,rfl,threshold33,
   n37,336938,pos37,cp37,ivec19,dvec19,dpos19,vp19,ivec18,dvec18,dpos18,vp18⟩

private def bk35 : BoundKit true :=
  ⟨35,eb35,indexOk35.1,indexOk35.2,lookup35,rfl,threshold35,
   n42,48134,pos42,cp42,ivec19,dvec19,dpos19,vp19,ivec18,dvec18,dpos18,vp18⟩

private def bk36 : BoundKit true :=
  ⟨36,eb36,indexOk36.1,indexOk36.2,lookup36,rfl,threshold36,
   n43,1394,pos43,cp43,ivec21,dvec21,dpos21,vp21,ivec20,dvec20,dpos20,vp20⟩

private def bk39 : BoundKit true :=
  ⟨39,eb39,indexOk39.1,indexOk39.2,lookup39,rfl,threshold39,
   n45,386377,pos45,cp45,ivec16,dvec16,dpos16,vp16,ivec22,dvec22,dpos22,vp22⟩

private def bk43 : BoundKit true :=
  ⟨43,eb43,indexOk43.1,indexOk43.2,lookup43,rfl,threshold43,
   n91,1394,pos91,cp91,ivec21,dvec21,dpos21,vp21,ivec39,dvec39,dpos39,vp39⟩

private def bk45 : BoundKit true :=
  ⟨45,eb45,indexOk45.1,indexOk45.2,lookup45,rfl,threshold45,
   n47,117507,pos47,cp47,ivec23,dvec23,dpos23,vp23,ivec15,dvec15,dpos15,vp15⟩

private def bk50 : BoundKit false :=
  ⟨50,eb50,indexOk50.1,indexOk50.2,lookup50,rfl,threshold50,
   n49,471338,pos49,cp49,ivec6,dvec6,dpos6,vp6,ivec24,dvec24,dpos24,vp24⟩

private def bk51 : BoundKit false :=
  ⟨51,eb51,indexOk51.1,indexOk51.2,lookup51,rfl,threshold51,
   n57,2379971,pos57,cp57,ivec10,dvec10,dpos10,vp10,ivec27,dvec27,dpos27,vp27⟩

private def bk52 : BoundKit false :=
  ⟨52,eb52,indexOk52.1,indexOk52.2,lookup52,rfl,threshold52,
   n52,22270,pos52,cp52,ivec25,dvec25,dpos25,vp25,ivec26,dvec26,dpos26,vp26⟩

private def bk53 : BoundKit false :=
  ⟨53,eb53,indexOk53.1,indexOk53.2,lookup53,rfl,threshold53,
   n55,16798,pos55,cp55,ivec9,dvec9,dpos9,vp9,ivec26,dvec26,dpos26,vp26⟩

private def bk60 : BoundKit false :=
  ⟨60,eb60,indexOk60.1,indexOk60.2,lookup60,rfl,threshold60,
   n60,67334,pos60,cp60,ivec6,dvec6,dpos6,vp6,ivec24,dvec24,dpos24,vp24⟩

private def bk61 : BoundKit true :=
  ⟨61,eb61,indexOk61.1,indexOk61.2,lookup61,rfl,threshold61,
   n56,2227,pos56,cp56,ivec8,dvec8,dpos8,vp8,ivec26,dvec26,dpos26,vp26⟩

private def bk66 : BoundKit false :=
  ⟨66,eb66,indexOk66.1,indexOk66.2,lookup66,rfl,threshold66,
   n61,5625386,pos61,cp61,ivec10,dvec10,dpos10,vp10,ivec28,dvec28,dpos28,vp28⟩

private def bk69 : BoundKit true :=
  ⟨69,eb69,indexOk69.1,indexOk69.2,lookup69,rfl,threshold69,
   n63,555015,pos63,cp63,ivec1,dvec1,dpos1,vp1,ivec29,dvec29,dpos29,vp29⟩

private def bk70 : BoundKit true :=
  ⟨70,eb70,indexOk70.1,indexOk70.2,lookup70,rfl,threshold70,
   n65,25197,pos65,cp65,ivec9,dvec9,dpos9,vp9,ivec30,dvec30,dpos30,vp30⟩

private def bk71 : BoundKit false :=
  ⟨71,eb71,indexOk71.1,indexOk71.2,lookup71,rfl,threshold71,
   n67,7058447,pos67,cp67,ivec31,dvec31,dpos31,vp31,ivec27,dvec27,dpos27,vp27⟩

private def bk75 : BoundKit true :=
  ⟨75,eb75,indexOk75.1,indexOk75.2,lookup75,rfl,threshold75,
   n116,1394,pos116,cp116,ivec21,dvec21,dpos21,vp21,ivec26,dvec26,dpos26,vp26⟩

private def bk76 : BoundKit true :=
  ⟨76,eb76,indexOk76.1,indexOk76.2,lookup76,rfl,threshold76,
   n69,95979,pos69,cp69,ivec16,dvec16,dpos16,vp16,ivec32,dvec32,dpos32,vp32⟩

private def bk84 : BoundKit true :=
  ⟨84,eb84,indexOk84.1,indexOk84.2,lookup84,rfl,threshold84,
   n72,168469,pos72,cp72,ivec19,dvec19,dpos19,vp19,ivec33,dvec33,dpos33,vp33⟩

private def bk86 : BoundKit true :=
  ⟨86,eb86,indexOk86.1,indexOk86.2,lookup86,rfl,threshold86,
   n74,120335,pos74,cp74,ivec19,dvec19,dpos19,vp19,ivec33,dvec33,dpos33,vp33⟩

private def bk87 : BoundKit true :=
  ⟨87,eb87,indexOk87.1,indexOk87.2,lookup87,rfl,threshold87,
   n75,697,pos75,cp75,ivec21,dvec21,dpos21,vp21,ivec34,dvec34,dpos34,vp34⟩

private def bk90 : BoundKit true :=
  ⟨90,eb90,indexOk90.1,indexOk90.2,lookup90,rfl,threshold90,
   n77,2318262,pos77,cp77,ivec16,dvec16,dpos16,vp16,ivec35,dvec35,dpos35,vp35⟩

private def bk96 : BoundKit true :=
  ⟨96,eb96,indexOk96.1,indexOk96.2,lookup96,rfl,threshold96,
   n79,117507,pos79,cp79,ivec23,dvec23,dpos23,vp23,ivec32,dvec32,dpos32,vp32⟩

private def bk100 : BoundKit true :=
  ⟨100,eb100,indexOk100.1,indexOk100.2,lookup100,rfl,threshold100,
   n80,1394,pos80,cp80,ivec21,dvec21,dpos21,vp21,ivec36,dvec36,dpos36,vp36⟩

private def bk101 : BoundKit false :=
  ⟨101,eb101,indexOk101.1,indexOk101.2,lookup101,rfl,threshold101,
   n83,47838,pos83,cp83,ivec37,dvec37,dpos37,vp37,ivec38,dvec38,dpos38,vp38⟩

private def bk102 : BoundKit false :=
  ⟨102,eb102,indexOk102.1,indexOk102.2,lookup102,rfl,threshold102,
   n93,102,pos93,cp93,ivec40,dvec40,dpos40,vp40,ivec41,dvec41,dpos41,vp41⟩

private def bk103 : BoundKit false :=
  ⟨103,eb103,indexOk103.1,indexOk103.2,lookup103,rfl,threshold103,
   n97,28083,pos97,cp97,ivec42,dvec42,dpos42,vp42,ivec43,dvec43,dpos43,vp43⟩

private def bk105 : BoundKit true :=
  ⟨105,eb105,indexOk105.1,indexOk105.2,lookup105,rfl,threshold105,
   n89,336938,pos89,cp89,ivec19,dvec19,dpos19,vp19,ivec5,dvec5,dpos5,vp5⟩

private def bk106 : BoundKit false :=
  ⟨106,eb106,indexOk106.1,indexOk106.2,lookup106,rfl,threshold106,
   n99,585948,pos99,cp99,ivec42,dvec42,dpos42,vp42,ivec44,dvec44,dpos44,vp44⟩

private def bk107 : BoundKit true :=
  ⟨107,eb107,indexOk107.1,indexOk107.2,lookup107,rfl,threshold107,
   n90,240670,pos90,cp90,ivec19,dvec19,dpos19,vp19,ivec5,dvec5,dpos5,vp5⟩

private def bk109 : BoundKit false :=
  ⟨109,eb109,indexOk109.1,indexOk109.2,lookup109,rfl,threshold109,
   n100,1525029,pos100,cp100,ivec45,dvec45,dpos45,vp45,ivec43,dvec43,dpos43,vp43⟩

private def bk110 : BoundKit true :=
  ⟨110,eb110,indexOk110.1,indexOk110.2,lookup110,rfl,threshold110,
   n83,47838,pos83,cp83,ivec37,dvec37,dpos37,vp37,ivec38,dvec38,dpos38,vp38⟩

private def bk114 : BoundKit true :=
  ⟨114,eb114,indexOk114.1,indexOk114.2,lookup114,rfl,threshold114,
   n96,34170,pos96,cp96,ivec37,dvec37,dpos37,vp37,ivec38,dvec38,dpos38,vp38⟩

private def bk115 : BoundKit true :=
  ⟨115,eb115,indexOk115.1,indexOk115.2,lookup115,rfl,threshold115,
   n93,102,pos93,cp93,ivec40,dvec40,dpos40,vp40,ivec41,dvec41,dpos41,vp41⟩

private def bk116 : BoundKit false :=
  ⟨116,eb116,indexOk116.1,indexOk116.2,lookup116,rfl,threshold116,
   n102,365079,pos102,cp102,ivec46,dvec46,dpos46,vp46,ivec43,dvec43,dpos43,vp43⟩

private def bk118 : BoundKit false :=
  ⟨118,eb118,indexOk118.1,indexOk118.2,lookup118,rfl,threshold118,
   n103,3808662,pos103,cp103,ivec46,dvec46,dpos46,vp46,ivec44,dvec44,dpos44,vp44⟩

private def bk119 : BoundKit false :=
  ⟨119,eb119,indexOk119.1,indexOk119.2,lookup119,rfl,threshold119,
   n104,19825377,pos104,cp104,ivec47,dvec47,dpos47,vp47,ivec43,dvec43,dpos43,vp43⟩

private def bk120 : BoundKit true :=
  ⟨120,eb120,indexOk120.1,indexOk120.2,lookup120,rfl,threshold120,
   n105,5220637,pos105,cp105,ivec50,dvec50,dpos50,vp50,ivec49,dvec49,dpos49,vp49⟩

private def bk121 : BoundKit false :=
  ⟨121,eb121,indexOk121.1,indexOk121.2,lookup121,rfl,threshold121,
   n106,341054,pos106,cp106,ivec48,dvec48,dpos48,vp48,ivec4,dvec4,dpos4,vp4⟩

private def bk122 : BoundKit true :=
  ⟨122,eb122,indexOk122.1,indexOk122.2,lookup122,rfl,threshold122,
   n110,37567058,pos110,cp110,ivec50,dvec50,dpos50,vp50,ivec51,dvec51,dpos51,vp51⟩

private def bk125 : BoundKit true :=
  ⟨125,eb125,indexOk125.1,indexOk125.2,lookup125,rfl,threshold125,
   n112,294014566,pos112,cp112,ivec52,dvec52,dpos52,vp52,ivec49,dvec49,dpos49,vp49⟩

private def bk127 : BoundKit true :=
  ⟨127,eb127,indexOk127.1,indexOk127.2,lookup127,rfl,threshold127,
   n113,31993,pos113,cp113,ivec16,dvec16,dpos16,vp16,ivec53,dvec53,dpos53,vp53⟩

private def bk129 : BoundKit true :=
  ⟨129,eb129,indexOk129.1,indexOk129.2,lookup129,rfl,threshold129,
   n114,336938,pos114,cp114,ivec19,dvec19,dpos19,vp19,ivec24,dvec24,dpos24,vp24⟩

private def bk131 : BoundKit true :=
  ⟨131,eb131,indexOk131.1,indexOk131.2,lookup131,rfl,threshold131,
   n115,48134,pos115,cp115,ivec19,dvec19,dpos19,vp19,ivec24,dvec24,dpos24,vp24⟩

private def bk134 : BoundKit true :=
  ⟨134,eb134,indexOk134.1,indexOk134.2,lookup134,rfl,threshold134,
   n117,1159131,pos117,cp117,ivec16,dvec16,dpos16,vp16,ivec54,dvec54,dpos54,vp54⟩

private def bk137 : BoundKit true :=
  ⟨137,eb137,indexOk137.1,indexOk137.2,lookup137,rfl,threshold137,
   n118,39169,pos118,cp118,ivec23,dvec23,dpos23,vp23,ivec53,dvec53,dpos53,vp53⟩

private def bk140 : BoundKit true :=
  ⟨140,eb140,indexOk140.1,indexOk140.2,lookup140,rfl,threshold140,
   n119,33598,pos119,cp119,ivec56,dvec56,dpos56,vp56,ivec55,dvec55,dpos55,vp55⟩

private def bk144 : BoundKit true :=
  ⟨144,eb144,indexOk144.1,indexOk144.2,lookup144,rfl,threshold144,
   n120,1694452,pos120,cp120,ivec56,dvec56,dpos56,vp56,ivec57,dvec57,dpos57,vp57⟩

private def bk145 : BoundKit true :=
  ⟨145,eb145,indexOk145.1,indexOk145.2,lookup145,rfl,threshold145,
   n465,7,pos465,cp465,ivec59,dvec59,dpos59,vp59,ivec58,dvec58,dpos58,vp58⟩

private def bk146 : BoundKit true :=
  ⟨146,eb146,indexOk146.1,indexOk146.2,lookup146,rfl,threshold146,
   n122,5,pos122,cp122,ivec59,dvec59,dpos59,vp59,ivec58,dvec58,dpos58,vp58⟩

private def bk147 : BoundKit true :=
  ⟨147,eb147,indexOk147.1,indexOk147.2,lookup147,rfl,threshold147,
   n124,1,pos124,cp124,ivec60,dvec60,dpos60,vp60,ivec41,dvec41,dpos41,vp41⟩

private def bk150 : BoundKit true :=
  ⟨150,eb150,indexOk150.1,indexOk150.2,lookup150,rfl,threshold150,
   n125,341054,pos125,cp125,ivec48,dvec48,dpos48,vp48,ivec29,dvec29,dpos29,vp29⟩

private def bk154 : BoundKit true :=
  ⟨154,eb154,indexOk154.1,indexOk154.2,lookup154,rfl,threshold154,
   n126,243610,pos126,cp126,ivec48,dvec48,dpos48,vp48,ivec29,dvec29,dpos29,vp29⟩

private def bk159 : BoundKit true :=
  ⟨159,eb159,indexOk159.1,indexOk159.2,lookup159,rfl,threshold159,
   n127,250,pos127,cp127,ivec63,dvec63,dpos63,vp63,ivec62,dvec62,dpos62,vp62⟩

private def bk160 : BoundKit false :=
  ⟨160,eb160,indexOk160.1,indexOk160.2,lookup160,rfl,threshold160,
   n1,253,pos1,cp1,ivec3,dvec3,dpos3,vp3,ivec2,dvec2,dpos2,vp2⟩

private def bk162 : BoundKit false :=
  ⟨162,eb162,indexOk162.1,indexOk162.2,lookup162,rfl,threshold162,
   n128,848225,pos128,cp128,ivec61,dvec61,dpos61,vp61,ivec4,dvec4,dpos4,vp4⟩

private def bk163 : BoundKit false :=
  ⟨163,eb163,indexOk163.1,indexOk163.2,lookup163,rfl,threshold163,
   n140,147323,pos140,cp140,ivec67,dvec67,dpos67,vp67,ivec11,dvec11,dpos11,vp11⟩

private def bk164 : BoundKit false :=
  ⟨164,eb164,indexOk164.1,indexOk164.2,lookup164,rfl,threshold164,
   n137,43885,pos137,cp137,ivec66,dvec66,dpos66,vp66,ivec7,dvec7,dpos7,vp7⟩

private def bk165 : BoundKit false :=
  ⟨165,eb165,indexOk165.1,indexOk165.2,lookup165,rfl,threshold165,
   n139,57974,pos139,cp139,ivec65,dvec65,dpos65,vp65,ivec7,dvec7,dpos7,vp7⟩

private def bk170 : BoundKit true :=
  ⟨170,eb170,indexOk170.1,indexOk170.2,lookup170,rfl,threshold170,
   n379,7881307,pos379,cp379,ivec64,dvec64,dpos64,vp64,ivec5,dvec5,dpos5,vp5⟩

private def bk171 : BoundKit false :=
  ⟨171,eb171,indexOk171.1,indexOk171.2,lookup171,rfl,threshold171,
   n143,7660796,pos143,cp143,ivec67,dvec67,dpos67,vp67,ivec12,dvec12,dpos12,vp12⟩

private def bk172 : BoundKit true :=
  ⟨172,eb172,indexOk172.1,indexOk172.2,lookup172,rfl,threshold172,
   n132,804215,pos132,cp132,ivec64,dvec64,dpos64,vp64,ivec5,dvec5,dpos5,vp5⟩

private def bk173 : BoundKit true :=
  ⟨173,eb173,indexOk173.1,indexOk173.2,lookup173,rfl,threshold173,
   n135,28987,pos135,cp135,ivec65,dvec65,dpos65,vp65,ivec39,dvec39,dpos39,vp39⟩

private def bk174 : BoundKit false :=
  ⟨174,eb174,indexOk174.1,indexOk174.2,lookup174,rfl,threshold174,
   n144,5421097,pos144,cp144,ivec68,dvec68,dpos68,vp68,ivec11,dvec11,dpos11,vp11⟩

private def bk183 : BoundKit false :=
  ⟨183,eb183,indexOk183.1,indexOk183.2,lookup183,rfl,threshold183,
   n146,3029375,pos146,cp146,ivec61,dvec61,dpos61,vp61,ivec4,dvec4,dpos4,vp4⟩

private def bk186 : BoundKit true :=
  ⟨186,eb186,indexOk186.1,indexOk186.2,lookup186,rfl,threshold186,
   n147,12314,pos147,cp147,ivec69,dvec69,dpos69,vp69,ivec7,dvec7,dpos7,vp7⟩

private def bk187 : BoundKit true :=
  ⟨187,eb187,indexOk187.1,indexOk187.2,lookup187,rfl,threshold187,
   n235,1974,pos235,cp235,ivec73,dvec73,dpos73,vp73,ivec7,dvec7,dpos7,vp7⟩

private def bk188 : BoundKit true :=
  ⟨188,eb188,indexOk188.1,indexOk188.2,lookup188,rfl,threshold188,
   n149,304278,pos149,cp149,ivec70,dvec70,dpos70,vp70,ivec15,dvec15,dpos15,vp15⟩

private def bk193 : BoundKit true :=
  ⟨193,eb193,indexOk193.1,indexOk193.2,lookup193,rfl,threshold193,
   n151,612457,pos151,cp151,ivec70,dvec70,dpos70,vp70,ivec71,dvec71,dpos71,vp71⟩

private def bk194 : BoundKit true :=
  ⟨194,eb194,indexOk194.1,indexOk194.2,lookup194,rfl,threshold194,
   n574,580027,pos574,cp574,ivec100,dvec100,dpos100,vp100,ivec18,dvec18,dpos18,vp18⟩

private def bk195 : BoundKit true :=
  ⟨195,eb195,indexOk195.1,indexOk195.2,lookup195,rfl,threshold195,
   n576,6157,pos576,cp576,ivec69,dvec69,dpos69,vp69,ivec20,dvec20,dpos20,vp20⟩

private def bk196 : BoundKit true :=
  ⟨196,eb196,indexOk196.1,indexOk196.2,lookup196,rfl,threshold196,
   n575,82861,pos575,cp575,ivec100,dvec100,dpos100,vp100,ivec18,dvec18,dpos18,vp18⟩

private def bk197 : BoundKit true :=
  ⟨197,eb197,indexOk197.1,indexOk197.2,lookup197,rfl,threshold197,
   n153,1135849,pos153,cp153,ivec72,dvec72,dpos72,vp72,ivec15,dvec15,dpos15,vp15⟩

private def bk199 : BoundKit true :=
  ⟨199,eb199,indexOk199.1,indexOk199.2,lookup199,rfl,threshold199,
   n155,658,pos155,cp155,ivec73,dvec73,dpos73,vp73,ivec20,dvec20,dpos20,vp20⟩

private def bk203 : BoundKit true :=
  ⟨203,eb203,indexOk203.1,indexOk203.2,lookup203,rfl,threshold203,
   n157,9478,pos157,cp157,ivec75,dvec75,dpos75,vp75,ivec74,dvec74,dpos74,vp74⟩

private def bk207 : BoundKit true :=
  ⟨207,eb207,indexOk207.1,indexOk207.2,lookup207,rfl,threshold207,
   n160,6770,pos160,cp160,ivec75,dvec75,dpos75,vp75,ivec74,dvec74,dpos74,vp74⟩

private def bk208 : BoundKit true :=
  ⟨208,eb208,indexOk208.1,indexOk208.2,lookup208,rfl,threshold208,
   n161,658,pos161,cp161,ivec73,dvec73,dpos73,vp73,ivec76,dvec76,dpos76,vp76⟩

private def bk214 : BoundKit false :=
  ⟨214,eb214,indexOk214.1,indexOk214.2,lookup214,rfl,threshold214,
   n163,7881307,pos163,cp163,ivec64,dvec64,dpos64,vp64,ivec24,dvec24,dpos24,vp24⟩

private def bk215 : BoundKit false :=
  ⟨215,eb215,indexOk215.1,indexOk215.2,lookup215,rfl,threshold215,
   n165,147323,pos165,cp165,ivec67,dvec67,dpos67,vp67,ivec27,dvec27,dpos27,vp27⟩

private def bk216 : BoundKit false :=
  ⟨216,eb216,indexOk216.1,indexOk216.2,lookup216,rfl,threshold216,
   n164,707,pos164,cp164,ivec65,dvec65,dpos65,vp65,ivec26,dvec26,dpos26,vp26⟩

private def bk217 : BoundKit false :=
  ⟨217,eb217,indexOk217.1,indexOk217.2,lookup217,rfl,threshold217,
   n169,12314,pos169,cp169,ivec69,dvec69,dpos69,vp69,ivec26,dvec26,dpos26,vp26⟩

private def bk218 : BoundKit false :=
  ⟨218,eb218,indexOk218.1,indexOk218.2,lookup218,rfl,threshold218,
   n389,1696450,pos389,cp389,ivec61,dvec61,dpos61,vp61,ivec29,dvec29,dpos29,vp29⟩

private def bk223 : BoundKit false :=
  ⟨223,eb223,indexOk223.1,indexOk223.2,lookup223,rfl,threshold223,
   n166,160843,pos166,cp166,ivec64,dvec64,dpos64,vp64,ivec24,dvec24,dpos24,vp24⟩

private def bk226 : BoundKit false :=
  ⟨226,eb226,indexOk226.1,indexOk226.2,lookup226,rfl,threshold226,
   n167,348218,pos167,cp167,ivec67,dvec67,dpos67,vp67,ivec28,dvec28,dpos28,vp28⟩

private def bk229 : BoundKit true :=
  ⟨229,eb229,indexOk229.1,indexOk229.2,lookup229,rfl,threshold229,
   n168,6058750,pos168,cp168,ivec61,dvec61,dpos61,vp61,ivec29,dvec29,dpos29,vp29⟩

private def bk230 : BoundKit true :=
  ⟨230,eb230,indexOk230.1,indexOk230.2,lookup230,rfl,threshold230,
   n169,12314,pos169,cp169,ivec69,dvec69,dpos69,vp69,ivec26,dvec26,dpos26,vp26⟩

private def bk231 : BoundKit false :=
  ⟨231,eb231,indexOk231.1,indexOk231.2,lookup231,rfl,threshold231,
   n170,2214839,pos170,cp170,ivec77,dvec77,dpos77,vp77,ivec27,dvec27,dpos27,vp27⟩

private def bk235 : BoundKit true :=
  ⟨235,eb235,indexOk235.1,indexOk235.2,lookup235,rfl,threshold235,
   n253,329,pos253,cp253,ivec73,dvec73,dpos73,vp73,ivec26,dvec26,dpos26,vp26⟩

private def bk236 : BoundKit true :=
  ⟨236,eb236,indexOk236.1,indexOk236.2,lookup236,rfl,threshold236,
   n172,152139,pos172,cp172,ivec70,dvec70,dpos70,vp70,ivec32,dvec32,dpos32,vp32⟩

private def bk241 : BoundKit true :=
  ⟨241,eb241,indexOk241.1,indexOk241.2,lookup241,rfl,threshold241,
   n173,1837371,pos173,cp173,ivec70,dvec70,dpos70,vp70,ivec78,dvec78,dpos78,vp78⟩

private def bk242 : BoundKit true :=
  ⟨242,eb242,indexOk242.1,indexOk242.2,lookup242,rfl,threshold242,
   n604,1160054,pos604,cp604,ivec100,dvec100,dpos100,vp100,ivec33,dvec33,dpos33,vp33⟩

private def bk243 : BoundKit true :=
  ⟨243,eb243,indexOk243.1,indexOk243.2,lookup243,rfl,threshold243,
   n263,1974,pos263,cp263,ivec73,dvec73,dpos73,vp73,ivec30,dvec30,dpos30,vp30⟩

private def bk244 : BoundKit true :=
  ⟨244,eb244,indexOk244.1,indexOk244.2,lookup244,rfl,threshold244,
   n605,828610,pos605,cp605,ivec100,dvec100,dpos100,vp100,ivec33,dvec33,dpos33,vp33⟩

private def bk245 : BoundKit true :=
  ⟨245,eb245,indexOk245.1,indexOk245.2,lookup245,rfl,threshold245,
   n175,103259,pos175,cp175,ivec72,dvec72,dpos72,vp72,ivec32,dvec32,dpos32,vp32⟩

private def bk247 : BoundKit true :=
  ⟨247,eb247,indexOk247.1,indexOk247.2,lookup247,rfl,threshold247,
   n176,99519,pos176,cp176,ivec75,dvec75,dpos75,vp75,ivec79,dvec79,dpos79,vp79⟩

private def bk251 : BoundKit true :=
  ⟨251,eb251,indexOk251.1,indexOk251.2,lookup251,rfl,threshold251,
   n178,10155,pos178,cp178,ivec75,dvec75,dpos75,vp75,ivec79,dvec79,dpos79,vp79⟩

private def bk252 : BoundKit true :=
  ⟨252,eb252,indexOk252.1,indexOk252.2,lookup252,rfl,threshold252,
   n179,987,pos179,cp179,ivec73,dvec73,dpos73,vp73,ivec36,dvec36,dpos36,vp36⟩

private def bk257 : BoundKit false :=
  ⟨257,eb257,indexOk257.1,indexOk257.2,lookup257,rfl,threshold257,
   n258,57974,pos258,cp258,ivec65,dvec65,dpos65,vp65,ivec83,dvec83,dpos83,vp83⟩

private def bk258 : BoundKit false :=
  ⟨258,eb258,indexOk258.1,indexOk258.2,lookup258,rfl,threshold258,
   n180,21210854,pos180,cp180,ivec80,dvec80,dpos80,vp80,ivec81,dvec81,dpos81,vp81⟩

private def bk259 : BoundKit false :=
  ⟨259,eb259,indexOk259.1,indexOk259.2,lookup259,rfl,threshold259,
   n189,250733964,pos189,cp189,ivec85,dvec85,dpos85,vp85,ivec86,dvec86,dpos86,vp86⟩

private def bk260 : BoundKit false :=
  ⟨260,eb260,indexOk260.1,indexOk260.2,lookup260,rfl,threshold260,
   n184,198830,pos184,cp184,ivec82,dvec82,dpos82,vp82,ivec83,dvec83,dpos83,vp83⟩

private def bk261 : BoundKit false :=
  ⟨261,eb261,indexOk261.1,indexOk261.2,lookup261,rfl,threshold261,
   n186,454510,pos186,cp186,ivec84,dvec84,dpos84,vp84,ivec83,dvec83,dpos83,vp83⟩

private def bk268 : BoundKit false :=
  ⟨268,eb268,indexOk268.1,indexOk268.2,lookup268,rfl,threshold268,
   n194,75753050,pos194,cp194,ivec80,dvec80,dpos80,vp80,ivec81,dvec81,dpos81,vp81⟩

private def bk272 : BoundKit true :=
  ⟨272,eb272,indexOk272.1,indexOk272.2,lookup272,rfl,threshold272,
   n195,4216979,pos195,cp195,ivec88,dvec88,dpos88,vp88,ivec87,dvec87,dpos87,vp87⟩

private def bk280 : BoundKit true :=
  ⟨280,eb280,indexOk280.1,indexOk280.2,lookup280,rfl,threshold280,
   n199,7881307,pos199,cp199,ivec64,dvec64,dpos64,vp64,ivec89,dvec89,dpos89,vp89⟩

private def bk282 : BoundKit true :=
  ⟨282,eb282,indexOk282.1,indexOk282.2,lookup282,rfl,threshold282,
   n202,804215,pos202,cp202,ivec64,dvec64,dpos64,vp64,ivec89,dvec89,dpos89,vp89⟩

private def bk283 : BoundKit true :=
  ⟨283,eb283,indexOk283.1,indexOk283.2,lookup283,rfl,threshold283,
   n203,4141,pos203,cp203,ivec65,dvec65,dpos65,vp65,ivec90,dvec90,dpos90,vp90⟩

private def bk286 : BoundKit true :=
  ⟨286,eb286,indexOk286.1,indexOk286.2,lookup286,rfl,threshold286,
   n205,50928131,pos205,cp205,ivec88,dvec88,dpos88,vp88,ivec91,dvec91,dpos91,vp91⟩

private def bk292 : BoundKit true :=
  ⟨292,eb292,indexOk292.1,indexOk292.2,lookup292,rfl,threshold292,
   n207,29542461,pos207,cp207,ivec92,dvec92,dpos92,vp92,ivec87,dvec87,dpos87,vp87⟩

private def bk296 : BoundKit true :=
  ⟨296,eb296,indexOk296.1,indexOk296.2,lookup296,rfl,threshold296,
   n209,57974,pos209,cp209,ivec65,dvec65,dpos65,vp65,ivec93,dvec93,dpos93,vp93⟩

private def bk297 : BoundKit false :=
  ⟨297,eb297,indexOk297.1,indexOk297.2,lookup297,rfl,threshold297,
   n265,4739,pos265,cp265,ivec75,dvec75,dpos75,vp75,ivec83,dvec83,dpos83,vp83⟩

private def bk298 : BoundKit false :=
  ⟨298,eb298,indexOk298.1,indexOk298.2,lookup298,rfl,threshold298,
   n212,209049862,pos212,cp212,ivec94,dvec94,dpos94,vp94,ivec81,dvec81,dpos81,vp81⟩

private def bk299 : BoundKit false :=
  ⟨299,eb299,indexOk299.1,indexOk299.2,lookup299,rfl,threshold299,
   n220,770972124,pos220,cp220,ivec97,dvec97,dpos97,vp97,ivec86,dvec86,dpos86,vp86⟩

private def bk300 : BoundKit false :=
  ⟨300,eb300,indexOk300.1,indexOk300.2,lookup300,rfl,threshold300,
   n215,1843390,pos215,cp215,ivec95,dvec95,dpos95,vp95,ivec83,dvec83,dpos83,vp83⟩

private def bk301 : BoundKit false :=
  ⟨301,eb301,indexOk301.1,indexOk301.2,lookup301,rfl,threshold301,
   n217,502670,pos217,cp217,ivec96,dvec96,dpos96,vp96,ivec83,dvec83,dpos83,vp83⟩

private def bk308 : BoundKit false :=
  ⟨308,eb308,indexOk308.1,indexOk308.2,lookup308,rfl,threshold308,
   n223,746606650,pos223,cp223,ivec94,dvec94,dpos94,vp94,ivec81,dvec81,dpos81,vp81⟩

private def bk312 : BoundKit true :=
  ⟨312,eb312,indexOk312.1,indexOk312.2,lookup312,rfl,threshold312,
   n224,312797329,pos224,cp224,ivec98,dvec98,dpos98,vp98,ivec87,dvec87,dpos87,vp87⟩

private def bk318 : BoundKit true :=
  ⟨318,eb318,indexOk318.1,indexOk318.2,lookup318,rfl,threshold318,
   n227,65710974,pos227,cp227,ivec99,dvec99,dpos99,vp99,ivec89,dvec89,dpos89,vp89⟩

private def bk320 : BoundKit true :=
  ⟨320,eb320,indexOk320.1,indexOk320.2,lookup320,rfl,threshold320,
   n229,46936410,pos229,cp229,ivec99,dvec99,dpos99,vp99,ivec89,dvec89,dpos89,vp89⟩

private def bk321 : BoundKit true :=
  ⟨321,eb321,indexOk321.1,indexOk321.2,lookup321,rfl,threshold321,
   n230,4062,pos230,cp230,ivec75,dvec75,dpos75,vp75,ivec90,dvec90,dpos90,vp90⟩

private def bk324 : BoundKit true :=
  ⟨324,eb324,indexOk324.1,indexOk324.2,lookup324,rfl,threshold324,
   n231,28434,pos231,cp231,ivec75,dvec75,dpos75,vp75,ivec93,dvec93,dpos93,vp93⟩

private def bk325 : BoundKit false :=
  ⟨325,eb325,indexOk325.1,indexOk325.2,lookup325,rfl,threshold325,
   n239,101343,pos239,cp239,ivec101,dvec101,dpos101,vp101,ivec43,dvec43,dpos43,vp43⟩

private def bk327 : BoundKit true :=
  ⟨327,eb327,indexOk327.1,indexOk327.2,lookup327,rfl,threshold327,
   n232,1160054,pos232,cp232,ivec100,dvec100,dpos100,vp100,ivec5,dvec5,dpos5,vp5⟩

private def bk328 : BoundKit false :=
  ⟨328,eb328,indexOk328.1,indexOk328.2,lookup328,rfl,threshold328,
   n240,2114508,pos240,cp240,ivec101,dvec101,dpos101,vp101,ivec44,dvec44,dpos44,vp44⟩

private def bk329 : BoundKit true :=
  ⟨329,eb329,indexOk329.1,indexOk329.2,lookup329,rfl,threshold329,
   n234,828610,pos234,cp234,ivec100,dvec100,dpos100,vp100,ivec5,dvec5,dpos5,vp5⟩

private def bk331 : BoundKit false :=
  ⟨331,eb331,indexOk331.1,indexOk331.2,lookup331,rfl,threshold331,
   n241,15873,pos241,cp241,ivec104,dvec104,dpos104,vp104,ivec43,dvec43,dpos43,vp43⟩

private def bk332 : BoundKit false :=
  ⟨332,eb332,indexOk332.1,indexOk332.2,lookup332,rfl,threshold332,
   n236,2634918,pos236,cp236,ivec101,dvec101,dpos101,vp101,ivec102,dvec102,dpos102,vp102⟩

private def bk333 : BoundKit false :=
  ⟨333,eb333,indexOk333.1,indexOk333.2,lookup333,rfl,threshold333,
   n237,81646851,pos237,cp237,ivec101,dvec101,dpos101,vp101,ivec103,dvec103,dpos103,vp103⟩

private def bk334 : BoundKit false :=
  ⟨334,eb334,indexOk334.1,indexOk334.2,lookup334,rfl,threshold334,
   n238,894179,pos238,cp238,ivec104,dvec104,dpos104,vp104,ivec102,dvec102,dpos102,vp102⟩

private def bk335 : BoundKit false :=
  ⟨335,eb335,indexOk335.1,indexOk335.2,lookup335,rfl,threshold335,
   n242,1317459,pos242,cp242,ivec105,dvec105,dpos105,vp105,ivec43,dvec43,dpos43,vp43⟩

private def bk336 : BoundKit false :=
  ⟨336,eb336,indexOk336.1,indexOk336.2,lookup336,rfl,threshold336,
   n243,6872151,pos243,cp243,ivec105,dvec105,dpos105,vp105,ivec44,dvec44,dpos44,vp44⟩

private def bk337 : BoundKit false :=
  ⟨337,eb337,indexOk337.1,indexOk337.2,lookup337,rfl,threshold337,
   n244,15873,pos244,cp244,ivec106,dvec106,dpos106,vp106,ivec43,dvec43,dpos43,vp43⟩

private def bk338 : BoundKit true :=
  ⟨338,eb338,indexOk338.1,indexOk338.2,lookup338,rfl,threshold338,
   n245,2293177,pos245,cp245,ivec107,dvec107,dpos107,vp107,ivec49,dvec49,dpos49,vp49⟩

private def bk340 : BoundKit true :=
  ⟨340,eb340,indexOk340.1,indexOk340.2,lookup340,rfl,threshold340,
   n246,16501418,pos246,cp246,ivec107,dvec107,dpos107,vp107,ivec51,dvec51,dpos51,vp51⟩

private def bk341 : BoundKit true :=
  ⟨341,eb341,indexOk341.1,indexOk341.2,lookup341,rfl,threshold341,
   n254,199038,pos254,cp254,ivec75,dvec75,dpos75,vp75,ivec4,dvec4,dpos4,vp4⟩

private def bk342 : BoundKit true :=
  ⟨342,eb342,indexOk342.1,indexOk342.2,lookup342,rfl,threshold342,
   n247,20310,pos247,cp247,ivec75,dvec75,dpos75,vp75,ivec4,dvec4,dpos4,vp4⟩

private def bk345 : BoundKit true :=
  ⟨345,eb345,indexOk345.1,indexOk345.2,lookup345,rfl,threshold345,
   n248,50713,pos248,cp248,ivec70,dvec70,dpos70,vp70,ivec53,dvec53,dpos53,vp53⟩

private def bk346 : BoundKit false :=
  ⟨346,eb346,indexOk346.1,indexOk346.2,lookup346,rfl,threshold346,
   n249,1160054,pos249,cp249,ivec100,dvec100,dpos100,vp100,ivec24,dvec24,dpos24,vp24⟩

private def bk347 : BoundKit true :=
  ⟨347,eb347,indexOk347.1,indexOk347.2,lookup347,rfl,threshold347,
   n250,1224914,pos250,cp250,ivec70,dvec70,dpos70,vp70,ivec108,dvec108,dpos108,vp108⟩

private def bk348 : BoundKit true :=
  ⟨348,eb348,indexOk348.1,indexOk348.2,lookup348,rfl,threshold348,
   n249,1160054,pos249,cp249,ivec100,dvec100,dpos100,vp100,ivec24,dvec24,dpos24,vp24⟩

private def bk349 : BoundKit true :=
  ⟨349,eb349,indexOk349.1,indexOk349.2,lookup349,rfl,threshold349,
   n372,165722,pos372,cp372,ivec100,dvec100,dpos100,vp100,ivec24,dvec24,dpos24,vp24⟩

private def bk350 : BoundKit true :=
  ⟨350,eb350,indexOk350.1,indexOk350.2,lookup350,rfl,threshold350,
   n252,1135849,pos252,cp252,ivec72,dvec72,dpos72,vp72,ivec53,dvec53,dpos53,vp53⟩

private def bk355 : BoundKit true :=
  ⟨355,eb355,indexOk355.1,indexOk355.2,lookup355,rfl,threshold355,
   n364,1541891,pos364,cp364,ivec167,dvec167,dpos167,vp167,ivec53,dvec53,dpos53,vp53⟩

private def bk356 : BoundKit true :=
  ⟨356,eb356,indexOk356.1,indexOk356.2,lookup356,rfl,threshold356,
   n367,18621299,pos367,cp367,ivec167,dvec167,dpos167,vp167,ivec108,dvec108,dpos108,vp108⟩

private def bk357 : BoundKit true :=
  ⟨357,eb357,indexOk357.1,indexOk357.2,lookup357,rfl,threshold357,
   n368,34534643,pos368,cp368,ivec168,dvec168,dpos168,vp168,ivec53,dvec53,dpos53,vp53⟩

private def bk358 : BoundKit true :=
  ⟨358,eb358,indexOk358.1,indexOk358.2,lookup358,rfl,threshold358,
   n255,138697,pos255,cp255,ivec110,dvec110,dpos110,vp110,ivec109,dvec109,dpos109,vp109⟩

private def bk359 : BoundKit false :=
  ⟨359,eb359,indexOk359.1,indexOk359.2,lookup359,rfl,threshold359,
   n256,2251802,pos256,cp256,ivec64,dvec64,dpos64,vp64,ivec81,dvec81,dpos81,vp81⟩

private def bk360 : BoundKit true :=
  ⟨360,eb360,indexOk360.1,indexOk360.2,lookup360,rfl,threshold360,
   n257,1675033,pos257,cp257,ivec110,dvec110,dpos110,vp110,ivec111,dvec111,dpos111,vp111⟩

private def bk363 : BoundKit true :=
  ⟨363,eb363,indexOk363.1,indexOk363.2,lookup363,rfl,threshold363,
   n260,10207366,pos260,cp260,ivec112,dvec112,dpos112,vp112,ivec109,dvec109,dpos109,vp109⟩

private def bk366 : BoundKit true :=
  ⟨366,eb366,indexOk366.1,indexOk366.2,lookup366,rfl,threshold366,
   n261,199038,pos261,cp261,ivec75,dvec75,dpos75,vp75,ivec29,dvec29,dpos29,vp29⟩

private def bk370 : BoundKit true :=
  ⟨370,eb370,indexOk370.1,indexOk370.2,lookup370,rfl,threshold370,
   n262,20310,pos262,cp262,ivec75,dvec75,dpos75,vp75,ivec29,dvec29,dpos29,vp29⟩

private def bk375 : BoundKit false :=
  ⟨375,eb375,indexOk375.1,indexOk375.2,lookup375,rfl,threshold375,
   n264,10951829,pos264,cp264,ivec99,dvec99,dpos99,vp99,ivec81,dvec81,dpos81,vp81⟩

private def bk376 : BoundKit false :=
  ⟨376,eb376,indexOk376.1,indexOk376.2,lookup376,rfl,threshold376,
   n266,52684372,pos266,cp266,ivec113,dvec113,dpos113,vp113,ivec86,dvec86,dpos86,vp86⟩

private def bk380 : BoundKit false :=
  ⟨380,eb380,indexOk380.1,indexOk380.2,lookup380,rfl,threshold380,
   n267,7822735,pos267,cp267,ivec99,dvec99,dpos99,vp99,ivec81,dvec81,dpos81,vp81⟩

private def bk382 : BoundKit false :=
  ⟨382,eb382,indexOk382.1,indexOk382.2,lookup382,rfl,threshold382,
   n268,3004340799,pos268,cp268,ivec114,dvec114,dpos114,vp114,ivec115,dvec115,dpos115,vp115⟩

private def bk383 : BoundKit false :=
  ⟨383,eb383,indexOk383.1,indexOk383.2,lookup383,rfl,threshold383,
   n269,165650874873,pos269,cp269,ivec114,dvec114,dpos114,vp114,ivec116,dvec116,dpos116,vp116⟩

private def bk384 : BoundKit false :=
  ⟨384,eb384,indexOk384.1,indexOk384.2,lookup384,rfl,threshold384,
   n270,163148767737,pos270,cp270,ivec117,dvec117,dpos117,vp117,ivec115,dvec115,dpos115,vp115⟩

private def bk385 : BoundKit true :=
  ⟨385,eb385,indexOk385.1,indexOk385.2,lookup385,rfl,threshold385,
   n271,1062082,pos271,cp271,ivec119,dvec119,dpos119,vp119,ivec118,dvec118,dpos118,vp118⟩

private def bk386 : BoundKit true :=
  ⟨386,eb386,indexOk386.1,indexOk386.2,lookup386,rfl,threshold386,
   n272,59249003,pos272,cp272,ivec119,dvec119,dpos119,vp119,ivec120,dvec120,dpos120,vp120⟩

private def bk387 : BoundKit true :=
  ⟨387,eb387,indexOk387.1,indexOk387.2,lookup387,rfl,threshold387,
   n273,1852277,pos273,cp273,ivec121,dvec121,dpos121,vp121,ivec118,dvec118,dpos118,vp118⟩

private def bk388 : BoundKit true :=
  ⟨388,eb388,indexOk388.1,indexOk388.2,lookup388,rfl,threshold388,
   n275,14262244,pos275,cp275,ivec119,dvec119,dpos119,vp119,ivec122,dvec122,dpos122,vp122⟩

private def bk389 : BoundKit true :=
  ⟨389,eb389,indexOk389.1,indexOk389.2,lookup389,rfl,threshold389,
   n276,586345127,pos276,cp276,ivec119,dvec119,dpos119,vp119,ivec123,dvec123,dpos123,vp123⟩

private def bk390 : BoundKit true :=
  ⟨390,eb390,indexOk390.1,indexOk390.2,lookup390,rfl,threshold390,
   n277,74620302,pos277,cp277,ivec121,dvec121,dpos121,vp121,ivec122,dvec122,dpos122,vp122⟩

private def bk391 : BoundKit true :=
  ⟨391,eb391,indexOk391.1,indexOk391.2,lookup391,rfl,threshold391,
   n278,14953519,pos278,cp278,ivec124,dvec124,dpos124,vp124,ivec118,dvec118,dpos118,vp118⟩

private def bk392 : BoundKit true :=
  ⟨392,eb392,indexOk392.1,indexOk392.2,lookup392,rfl,threshold392,
   n279,1668385477,pos279,cp279,ivec124,dvec124,dpos124,vp124,ivec120,dvec120,dpos120,vp120⟩

private def bk393 : BoundKit true :=
  ⟨393,eb393,indexOk393.1,indexOk393.2,lookup393,rfl,threshold393,
   n280,104316086,pos280,cp280,ivec125,dvec125,dpos125,vp125,ivec118,dvec118,dpos118,vp118⟩

private def bk394 : BoundKit false :=
  ⟨394,eb394,indexOk394.1,indexOk394.2,lookup394,rfl,threshold394,
   n31,2,pos31,cp31,ivec14,dvec14,dpos14,vp14,ivec17,dvec17,dpos17,vp17⟩

private def bk395 : BoundKit false :=
  ⟨395,eb395,indexOk395.1,indexOk395.2,lookup395,rfl,threshold395,
   n127,250,pos127,cp127,ivec63,dvec63,dpos63,vp63,ivec62,dvec62,dpos62,vp62⟩

private def bk396 : BoundKit false :=
  ⟨396,eb396,indexOk396.1,indexOk396.2,lookup396,rfl,threshold396,
   n282,15174291,pos282,cp282,ivec126,dvec126,dpos126,vp126,ivec128,dvec128,dpos128,vp128⟩

private def bk397 : BoundKit false :=
  ⟨397,eb397,indexOk397.1,indexOk397.2,lookup397,rfl,threshold397,
   n285,7968235,pos285,cp285,ivec126,dvec126,dpos126,vp126,ivec129,dvec129,dpos129,vp129⟩

private def bk398 : BoundKit false :=
  ⟨398,eb398,indexOk398.1,indexOk398.2,lookup398,rfl,threshold398,
   n286,197265783,pos286,cp286,ivec130,dvec130,dpos130,vp130,ivec128,dvec128,dpos128,vp128⟩

private def bk399 : BoundKit true :=
  ⟨399,eb399,indexOk399.1,indexOk399.2,lookup399,rfl,threshold399,
   n287,922502,pos287,cp287,ivec132,dvec132,dpos132,vp132,ivec131,dvec131,dpos131,vp131⟩

private def bk402 : BoundKit true :=
  ⟨402,eb402,indexOk402.1,indexOk402.2,lookup402,rfl,threshold402,
   n290,46454565,pos290,cp290,ivec132,dvec132,dpos132,vp132,ivec133,dvec133,dpos133,vp133⟩

private def bk403 : BoundKit true :=
  ⟨403,eb403,indexOk403.1,indexOk403.2,lookup403,rfl,threshold403,
   n299,1841406,pos299,cp299,ivec135,dvec135,dpos135,vp135,ivec134,dvec134,dpos134,vp134⟩

private def bk404 : BoundKit true :=
  ⟨404,eb404,indexOk404.1,indexOk404.2,lookup404,rfl,threshold404,
   n292,1315290,pos292,cp292,ivec135,dvec135,dpos135,vp135,ivec134,dvec134,dpos134,vp134⟩

private def bk405 : BoundKit true :=
  ⟨405,eb405,indexOk405.1,indexOk405.2,lookup405,rfl,threshold405,
   n300,510,pos300,cp300,ivec59,dvec59,dpos59,vp59,ivec139,dvec139,dpos139,vp139⟩

private def bk406 : BoundKit true :=
  ⟨406,eb406,indexOk406.1,indexOk406.2,lookup406,rfl,threshold406,
   n296,77757764,pos296,cp296,ivec136,dvec136,dpos136,vp136,ivec131,dvec131,dpos131,vp131⟩

private def bk408 : BoundKit true :=
  ⟨408,eb408,indexOk408.1,indexOk408.2,lookup408,rfl,threshold408,
   n298,10727197,pos298,cp298,ivec138,dvec138,dpos138,vp138,ivec137,dvec137,dpos137,vp137⟩

private def bk411 : BoundKit true :=
  ⟨411,eb411,indexOk411.1,indexOk411.2,lookup411,rfl,threshold411,
   n302,1064531,pos302,cp302,ivec140,dvec140,dpos140,vp140,ivec53,dvec53,dpos53,vp53⟩

private def bk412 : BoundKit false :=
  ⟨412,eb412,indexOk412.1,indexOk412.2,lookup412,rfl,threshold412,
   n303,85,pos303,cp303,ivec59,dvec59,dpos59,vp59,ivec26,dvec26,dpos26,vp26⟩

private def bk414 : BoundKit false :=
  ⟨414,eb414,indexOk414.1,indexOk414.2,lookup414,rfl,threshold414,
   n305,458430,pos305,cp305,ivec141,dvec141,dpos141,vp141,ivec4,dvec4,dpos4,vp4⟩

private def bk415 : BoundKit true :=
  ⟨415,eb415,indexOk415.1,indexOk415.2,lookup415,rfl,threshold415,
   n303,85,pos303,cp303,ivec59,dvec59,dpos59,vp59,ivec26,dvec26,dpos26,vp26⟩

private def bk416 : BoundKit true :=
  ⟨416,eb416,indexOk416.1,indexOk416.2,lookup416,rfl,threshold416,
   n308,167131367,pos308,cp308,ivec140,dvec140,dpos140,vp140,ivec54,dvec54,dpos54,vp54⟩

private def bk419 : BoundKit true :=
  ⟨419,eb419,indexOk419.1,indexOk419.2,lookup419,rfl,threshold419,
   n317,7770,pos317,cp317,ivec148,dvec148,dpos148,vp148,ivec7,dvec7,dpos7,vp7⟩

private def bk420 : BoundKit true :=
  ⟨420,eb420,indexOk420.1,indexOk420.2,lookup420,rfl,threshold420,
   n309,128644477,pos309,cp309,ivec142,dvec142,dpos142,vp142,ivec53,dvec53,dpos53,vp53⟩

private def bk422 : BoundKit false :=
  ⟨422,eb422,indexOk422.1,indexOk422.2,lookup422,rfl,threshold422,
   n311,867613,pos311,cp311,ivec143,dvec143,dpos143,vp143,ivec144,dvec144,dpos144,vp144⟩

private def bk424 : BoundKit true :=
  ⟨424,eb424,indexOk424.1,indexOk424.2,lookup424,rfl,threshold424,
   n312,4214,pos312,cp312,ivec145,dvec145,dpos145,vp145,ivec5,dvec5,dpos5,vp5⟩

private def bk425 : BoundKit false :=
  ⟨425,eb425,indexOk425.1,indexOk425.2,lookup425,rfl,threshold425,
   n313,22604836,pos313,cp313,ivec143,dvec143,dpos143,vp143,ivec146,dvec146,dpos146,vp146⟩

private def bk426 : BoundKit true :=
  ⟨426,eb426,indexOk426.1,indexOk426.2,lookup426,rfl,threshold426,
   n316,2150,pos316,cp316,ivec145,dvec145,dpos145,vp145,ivec5,dvec5,dpos5,vp5⟩

private def bk427 : BoundKit false :=
  ⟨427,eb427,indexOk427.1,indexOk427.2,lookup427,rfl,threshold427,
   n318,2796719,pos318,cp318,ivec147,dvec147,dpos147,vp147,ivec144,dvec144,dpos144,vp144⟩

private def bk431 : BoundKit true :=
  ⟨431,eb431,indexOk431.1,indexOk431.2,lookup431,rfl,threshold431,
   n320,1841406,pos320,cp320,ivec135,dvec135,dpos135,vp135,ivec29,dvec29,dpos29,vp29⟩

private def bk432 : BoundKit false :=
  ⟨432,eb432,indexOk432.1,indexOk432.2,lookup432,rfl,threshold432,
   n321,33907254,pos321,cp321,ivec143,dvec143,dpos143,vp143,ivec149,dvec149,dpos149,vp149⟩

private def bk433 : BoundKit false :=
  ⟨433,eb433,indexOk433.1,indexOk433.2,lookup433,rfl,threshold433,
   n322,465908181,pos322,cp322,ivec143,dvec143,dpos143,vp143,ivec150,dvec150,dpos150,vp150⟩

private def bk434 : BoundKit false :=
  ⟨434,eb434,indexOk434.1,indexOk434.2,lookup434,rfl,threshold434,
   n323,473628142,pos323,cp323,ivec147,dvec147,dpos147,vp147,ivec149,dvec149,dpos149,vp149⟩

private def bk435 : BoundKit true :=
  ⟨435,eb435,indexOk435.1,indexOk435.2,lookup435,rfl,threshold435,
   n324,6576450,pos324,cp324,ivec135,dvec135,dpos135,vp135,ivec29,dvec29,dpos29,vp29⟩

private def bk436 : BoundKit true :=
  ⟨436,eb436,indexOk436.1,indexOk436.2,lookup436,rfl,threshold436,
   n325,510,pos325,cp325,ivec59,dvec59,dpos59,vp59,ivec30,dvec30,dpos30,vp30⟩

private def bk437 : BoundKit false :=
  ⟨437,eb437,indexOk437.1,indexOk437.2,lookup437,rfl,threshold437,
   n326,36565583,pos326,cp326,ivec151,dvec151,dpos151,vp151,ivec144,dvec144,dpos144,vp144⟩

private def bk439 : BoundKit false :=
  ⟨439,eb439,indexOk439.1,indexOk439.2,lookup439,rfl,threshold439,
   n327,476340838,pos327,cp327,ivec151,dvec151,dpos151,vp151,ivec146,dvec146,dpos146,vp146⟩

private def bk440 : BoundKit false :=
  ⟨440,eb440,indexOk440.1,indexOk440.2,lookup440,rfl,threshold440,
   n328,117867829,pos328,cp328,ivec152,dvec152,dpos152,vp152,ivec144,dvec144,dpos144,vp144⟩

private def bk441 : BoundKit true :=
  ⟨441,eb441,indexOk441.1,indexOk441.2,lookup441,rfl,threshold441,
   n329,10727197,pos329,cp329,ivec138,dvec138,dpos138,vp138,ivec109,dvec109,dpos109,vp109⟩

private def bk443 : BoundKit true :=
  ⟨443,eb443,indexOk443.1,indexOk443.2,lookup443,rfl,threshold443,
   n330,170,pos330,cp330,ivec59,dvec59,dpos59,vp59,ivec83,dvec83,dpos83,vp83⟩

private def bk446 : BoundKit false :=
  ⟨446,eb446,indexOk446.1,indexOk446.2,lookup446,rfl,threshold446,
   n331,349762,pos331,cp331,ivec145,dvec145,dpos145,vp145,ivec24,dvec24,dpos24,vp24⟩

private def bk447 : BoundKit false :=
  ⟨447,eb447,indexOk447.1,indexOk447.2,lookup447,rfl,threshold447,
   n359,4690,pos359,cp359,ivec163,dvec163,dpos163,vp163,ivec26,dvec26,dpos26,vp26⟩

private def bk449 : BoundKit false :=
  ⟨449,eb449,indexOk449.1,indexOk449.2,lookup449,rfl,threshold449,
   n334,5135331,pos334,cp334,ivec143,dvec143,dpos143,vp143,ivec154,dvec154,dpos154,vp154⟩

private def bk450 : BoundKit false :=
  ⟨450,eb450,indexOk450.1,indexOk450.2,lookup450,rfl,threshold450,
   n332,32359620,pos332,cp332,ivec143,dvec143,dpos143,vp143,ivec153,dvec153,dpos153,vp153⟩

private def bk452 : BoundKit true :=
  ⟨452,eb452,indexOk452.1,indexOk452.2,lookup452,rfl,threshold452,
   n333,7138,pos333,cp333,ivec145,dvec145,dpos145,vp145,ivec24,dvec24,dpos24,vp24⟩

private def bk454 : BoundKit false :=
  ⟨454,eb454,indexOk454.1,indexOk454.2,lookup454,rfl,threshold454,
   n335,215196189,pos335,cp335,ivec147,dvec147,dpos147,vp147,ivec154,dvec154,dpos154,vp154⟩

private def bk455 : BoundKit false :=
  ⟨455,eb455,indexOk455.1,indexOk455.2,lookup455,rfl,threshold455,
   n333,7138,pos333,cp333,ivec145,dvec145,dpos145,vp145,ivec24,dvec24,dpos24,vp24⟩

private def bk456 : BoundKit true :=
  ⟨456,eb456,indexOk456.1,indexOk456.2,lookup456,rfl,threshold456,
   n336,2590,pos336,cp336,ivec148,dvec148,dpos148,vp148,ivec26,dvec26,dpos26,vp26⟩

private def bk457 : BoundKit true :=
  ⟨457,eb457,indexOk457.1,indexOk457.2,lookup457,rfl,threshold457,
   n337,163774,pos337,cp337,ivec140,dvec140,dpos140,vp140,ivec109,dvec109,dpos109,vp109⟩

private def bk460 : BoundKit true :=
  ⟨460,eb460,indexOk460.1,indexOk460.2,lookup460,rfl,threshold460,
   n338,167131367,pos338,cp338,ivec140,dvec140,dpos140,vp140,ivec155,dvec155,dpos155,vp155⟩

private def bk461 : BoundKit true :=
  ⟨461,eb461,indexOk461.1,indexOk461.2,lookup461,rfl,threshold461,
   n344,229215,pos344,cp344,ivec141,dvec141,dpos141,vp141,ivec29,dvec29,dpos29,vp29⟩

private def bk462 : BoundKit true :=
  ⟨462,eb462,indexOk462.1,indexOk462.2,lookup462,rfl,threshold462,
   n348,818625,pos348,cp348,ivec141,dvec141,dpos141,vp141,ivec29,dvec29,dpos29,vp29⟩

private def bk463 : BoundKit true :=
  ⟨463,eb463,indexOk463.1,indexOk463.2,lookup463,rfl,threshold463,
   n349,3885,pos349,cp349,ivec148,dvec148,dpos148,vp148,ivec30,dvec30,dpos30,vp30⟩

private def bk464 : BoundKit true :=
  ⟨464,eb464,indexOk464.1,indexOk464.2,lookup464,rfl,threshold464,
   n339,128644477,pos339,cp339,ivec142,dvec142,dpos142,vp142,ivec109,dvec109,dpos109,vp109⟩

private def bk466 : BoundKit false :=
  ⟨466,eb466,indexOk466.1,indexOk466.2,lookup466,rfl,threshold466,
   n340,39923,pos340,cp340,ivec156,dvec156,dpos156,vp156,ivec144,dvec144,dpos144,vp144⟩

private def bk468 : BoundKit false :=
  ⟨468,eb468,indexOk468.1,indexOk468.2,lookup468,rfl,threshold468,
   n341,520078,pos341,cp341,ivec156,dvec156,dpos156,vp156,ivec146,dvec146,dpos146,vp146⟩

private def bk469 : BoundKit true :=
  ⟨469,eb469,indexOk469.1,indexOk469.2,lookup469,rfl,threshold469,
   n342,12314,pos342,cp342,ivec69,dvec69,dpos69,vp69,ivec39,dvec39,dpos39,vp39⟩

private def bk470 : BoundKit false :=
  ⟨470,eb470,indexOk470.1,indexOk470.2,lookup470,rfl,threshold470,
   n343,68783,pos343,cp343,ivec157,dvec157,dpos157,vp157,ivec144,dvec144,dpos144,vp144⟩

private def bk471 : BoundKit false :=
  ⟨471,eb471,indexOk471.1,indexOk471.2,lookup471,rfl,threshold471,
   n345,10141521,pos345,cp345,ivec156,dvec156,dpos156,vp156,ivec149,dvec149,dpos149,vp149⟩

private def bk472 : BoundKit false :=
  ⟨472,eb472,indexOk472.1,indexOk472.2,lookup472,rfl,threshold472,
   n346,278702463,pos346,cp346,ivec156,dvec156,dpos156,vp156,ivec150,dvec150,dpos150,vp150⟩

private def bk473 : BoundKit false :=
  ⟨473,eb473,indexOk473.1,indexOk473.2,lookup473,rfl,threshold473,
   n347,896038,pos347,cp347,ivec157,dvec157,dpos157,vp157,ivec149,dvec149,dpos149,vp149⟩

private def bk474 : BoundKit false :=
  ⟨474,eb474,indexOk474.1,indexOk474.2,lookup474,rfl,threshold474,
   n350,4824541,pos350,cp350,ivec158,dvec158,dpos158,vp158,ivec144,dvec144,dpos144,vp144⟩

private def bk475 : BoundKit false :=
  ⟨475,eb475,indexOk475.1,indexOk475.2,lookup475,rfl,threshold475,
   n351,125698852,pos351,cp351,ivec158,dvec158,dpos158,vp158,ivec146,dvec146,dpos146,vp146⟩

private def bk476 : BoundKit false :=
  ⟨476,eb476,indexOk476.1,indexOk476.2,lookup476,rfl,threshold476,
   n352,108058093,pos352,cp352,ivec159,dvec159,dpos159,vp159,ivec144,dvec144,dpos144,vp144⟩

private def bk477 : BoundKit true :=
  ⟨477,eb477,indexOk477.1,indexOk477.2,lookup477,rfl,threshold477,
   n353,1510223,pos353,cp353,ivec160,dvec160,dpos160,vp160,ivec53,dvec53,dpos53,vp53⟩

private def bk478 : BoundKit true :=
  ⟨478,eb478,indexOk478.1,indexOk478.2,lookup478,rfl,threshold478,
   n354,18238847,pos354,cp354,ivec160,dvec160,dpos160,vp160,ivec108,dvec108,dpos108,vp108⟩

private def bk479 : BoundKit true :=
  ⟨479,eb479,indexOk479.1,indexOk479.2,lookup479,rfl,threshold479,
   n355,4868149,pos355,cp355,ivec161,dvec161,dpos161,vp161,ivec53,dvec53,dpos53,vp53⟩

private def bk480 : BoundKit true :=
  ⟨480,eb480,indexOk480.1,indexOk480.2,lookup480,rfl,threshold480,
   n356,54716541,pos356,cp356,ivec160,dvec160,dpos160,vp160,ivec54,dvec54,dpos54,vp54⟩

private def bk481 : BoundKit true :=
  ⟨481,eb481,indexOk481.1,indexOk481.2,lookup481,rfl,threshold481,
   n357,74581782,pos357,cp357,ivec160,dvec160,dpos160,vp160,ivec162,dvec162,dpos162,vp162⟩

private def bk482 : BoundKit true :=
  ⟨482,eb482,indexOk482.1,indexOk482.2,lookup482,rfl,threshold482,
   n358,764299393,pos358,cp358,ivec161,dvec161,dpos161,vp161,ivec54,dvec54,dpos54,vp54⟩

private def bk483 : BoundKit true :=
  ⟨483,eb483,indexOk483.1,indexOk483.2,lookup483,rfl,threshold483,
   n361,22704539,pos361,cp361,ivec164,dvec164,dpos164,vp164,ivec53,dvec53,dpos53,vp53⟩

private def bk484 : BoundKit true :=
  ⟨484,eb484,indexOk484.1,indexOk484.2,lookup484,rfl,threshold484,
   n362,274200971,pos362,cp362,ivec164,dvec164,dpos164,vp164,ivec108,dvec108,dpos108,vp108⟩

private def bk485 : BoundKit true :=
  ⟨485,eb485,indexOk485.1,indexOk485.2,lookup485,rfl,threshold485,
   n363,73187257,pos363,cp363,ivec165,dvec165,dpos165,vp165,ivec53,dvec53,dpos53,vp53⟩

private def bk486 : BoundKit false :=
  ⟨486,eb486,indexOk486.1,indexOk486.2,lookup486,rfl,threshold486,
   n365,2693670,pos365,cp365,ivec166,dvec166,dpos166,vp166,ivec4,dvec4,dpos4,vp4⟩

private def bk487 : BoundKit false :=
  ⟨487,eb487,indexOk487.1,indexOk487.2,lookup487,rfl,threshold487,
   n370,178770,pos370,cp370,ivec169,dvec169,dpos169,vp169,ivec7,dvec7,dpos7,vp7⟩

private def bk488 : BoundKit true :=
  ⟨488,eb488,indexOk488.1,indexOk488.2,lookup488,rfl,threshold488,
   n369,55863897,pos369,cp369,ivec167,dvec167,dpos167,vp167,ivec54,dvec54,dpos54,vp54⟩

private def bk490 : BoundKit true :=
  ⟨490,eb490,indexOk490.1,indexOk490.2,lookup490,rfl,threshold490,
   n371,76145694,pos371,cp371,ivec167,dvec167,dpos167,vp167,ivec162,dvec162,dpos162,vp162⟩

private def bk491 : BoundKit true :=
  ⟨491,eb491,indexOk491.1,indexOk491.2,lookup491,rfl,threshold491,
   n373,417072227,pos373,cp373,ivec168,dvec168,dpos168,vp168,ivec54,dvec54,dpos54,vp54⟩

private def bk494 : BoundKit true :=
  ⟨494,eb494,indexOk494.1,indexOk494.2,lookup494,rfl,threshold494,
   n374,50713,pos374,cp374,ivec170,dvec170,dpos170,vp170,ivec53,dvec53,dpos53,vp53⟩

private def bk495 : BoundKit false :=
  ⟨495,eb495,indexOk495.1,indexOk495.2,lookup495,rfl,threshold495,
   n375,9620250,pos375,cp375,ivec166,dvec166,dpos166,vp166,ivec4,dvec4,dpos4,vp4⟩

private def bk496 : BoundKit true :=
  ⟨496,eb496,indexOk496.1,indexOk496.2,lookup496,rfl,threshold496,
   n376,86968894,pos376,cp376,ivec170,dvec170,dpos170,vp170,ivec108,dvec108,dpos108,vp108⟩

private def bk497 : BoundKit true :=
  ⟨497,eb497,indexOk497.1,indexOk497.2,lookup497,rfl,threshold497,
   n377,1135849,pos377,cp377,ivec171,dvec171,dpos171,vp171,ivec53,dvec53,dpos53,vp53⟩

private def bk498 : BoundKit false :=
  ⟨498,eb498,indexOk498.1,indexOk498.2,lookup498,rfl,threshold498,
   n378,495541,pos378,cp378,ivec67,dvec67,dpos67,vp67,ivec144,dvec144,dpos144,vp144⟩

private def bk499 : BoundKit false :=
  ⟨499,eb499,indexOk499.1,indexOk499.2,lookup499,rfl,threshold499,
   n380,12910852,pos380,cp380,ivec67,dvec67,dpos67,vp67,ivec146,dvec146,dpos146,vp146⟩

private def bk500 : BoundKit false :=
  ⟨500,eb500,indexOk500.1,indexOk500.2,lookup500,rfl,threshold500,
   n381,18234599,pos381,cp381,ivec68,dvec68,dpos68,vp68,ivec144,dvec144,dpos144,vp144⟩

private def bk501 : BoundKit false :=
  ⟨501,eb501,indexOk501.1,indexOk501.2,lookup501,rfl,threshold501,
   n382,6455426,pos382,cp382,ivec67,dvec67,dpos67,vp67,ivec149,dvec149,dpos149,vp149⟩

private def bk502 : BoundKit false :=
  ⟨502,eb502,indexOk502.1,indexOk502.2,lookup502,rfl,threshold502,
   n383,266105517,pos383,cp383,ivec67,dvec67,dpos67,vp67,ivec150,dvec150,dpos150,vp150⟩

private def bk503 : BoundKit false :=
  ⟨503,eb503,indexOk503.1,indexOk503.2,lookup503,rfl,threshold503,
   n384,118771307,pos384,cp384,ivec68,dvec68,dpos68,vp68,ivec149,dvec149,dpos149,vp149⟩

private def bk504 : BoundKit false :=
  ⟨504,eb504,indexOk504.1,indexOk504.2,lookup504,rfl,threshold504,
   n385,7449913,pos385,cp385,ivec77,dvec77,dpos77,vp77,ivec144,dvec144,dpos144,vp144⟩

private def bk505 : BoundKit false :=
  ⟨505,eb505,indexOk505.1,indexOk505.2,lookup505,rfl,threshold505,
   n386,194100436,pos386,cp386,ivec77,dvec77,dpos77,vp77,ivec146,dvec146,dpos146,vp146⟩

private def bk506 : BoundKit false :=
  ⟨506,eb506,indexOk506.1,indexOk506.2,lookup506,rfl,threshold506,
   n387,274137107,pos387,cp387,ivec172,dvec172,dpos172,vp172,ivec144,dvec144,dpos144,vp144⟩

private def bk507 : BoundKit true :=
  ⟨507,eb507,indexOk507.1,indexOk507.2,lookup507,rfl,threshold507,
   n388,63661,pos388,cp388,ivec173,dvec173,dpos173,vp173,ivec109,dvec109,dpos109,vp109⟩

private def bk510 : BoundKit true :=
  ⟨510,eb510,indexOk510.1,indexOk510.2,lookup510,rfl,threshold510,
   n390,580027,pos390,cp390,ivec100,dvec100,dpos100,vp100,ivec81,dvec81,dpos81,vp81⟩

private def bk512 : BoundKit true :=
  ⟨512,eb512,indexOk512.1,indexOk512.2,lookup512,rfl,threshold512,
   n391,414305,pos391,cp391,ivec100,dvec100,dpos100,vp100,ivec81,dvec81,dpos81,vp81⟩

private def bk513 : BoundKit true :=
  ⟨513,eb513,indexOk513.1,indexOk513.2,lookup513,rfl,threshold513,
   n392,6157,pos392,cp392,ivec69,dvec69,dpos69,vp69,ivec83,dvec83,dpos83,vp83⟩

private def bk516 : BoundKit true :=
  ⟨516,eb516,indexOk516.1,indexOk516.2,lookup516,rfl,threshold516,
   n393,2306487,pos393,cp393,ivec173,dvec173,dpos173,vp173,ivec155,dvec155,dpos155,vp155⟩

private def bk519 : BoundKit true :=
  ⟨519,eb519,indexOk519.1,indexOk519.2,lookup519,rfl,threshold519,
   n394,957073,pos394,cp394,ivec174,dvec174,dpos174,vp174,ivec109,dvec109,dpos109,vp109⟩

private def bk522 : BoundKit false :=
  ⟨522,eb522,indexOk522.1,indexOk522.2,lookup522,rfl,threshold522,
   n395,32263737,pos395,cp395,ivec67,dvec67,dpos67,vp67,ivec154,dvec154,dpos154,vp154⟩

private def bk523 : BoundKit false :=
  ⟨523,eb523,indexOk523.1,indexOk523.2,lookup523,rfl,threshold523,
   n396,67768580,pos396,cp396,ivec67,dvec67,dpos67,vp67,ivec153,dvec153,dpos153,vp153⟩

private def bk524 : BoundKit false :=
  ⟨524,eb524,indexOk524.1,indexOk524.2,lookup524,rfl,threshold524,
   n397,1187220243,pos397,cp397,ivec68,dvec68,dpos68,vp68,ivec154,dvec154,dpos154,vp154⟩

private def bk525 : BoundKit true :=
  ⟨525,eb525,indexOk525.1,indexOk525.2,lookup525,rfl,threshold525,
   n398,1541891,pos398,cp398,ivec167,dvec167,dpos167,vp167,ivec109,dvec109,dpos109,vp109⟩

private def bk526 : BoundKit false :=
  ⟨526,eb526,indexOk526.1,indexOk526.2,lookup526,rfl,threshold526,
   n399,1346835,pos399,cp399,ivec166,dvec166,dpos166,vp166,ivec29,dvec29,dpos29,vp29⟩

private def bk527 : BoundKit true :=
  ⟨527,eb527,indexOk527.1,indexOk527.2,lookup527,rfl,threshold527,
   n400,18621299,pos400,cp400,ivec167,dvec167,dpos167,vp167,ivec111,dvec111,dpos111,vp111⟩

private def bk528 : BoundKit true :=
  ⟨528,eb528,indexOk528.1,indexOk528.2,lookup528,rfl,threshold528,
   n401,69069286,pos401,cp401,ivec168,dvec168,dpos168,vp168,ivec109,dvec109,dpos109,vp109⟩

private def bk529 : BoundKit true :=
  ⟨529,eb529,indexOk529.1,indexOk529.2,lookup529,rfl,threshold529,
   n402,55863897,pos402,cp402,ivec167,dvec167,dpos167,vp167,ivec155,dvec155,dpos155,vp155⟩

private def bk531 : BoundKit true :=
  ⟨531,eb531,indexOk531.1,indexOk531.2,lookup531,rfl,threshold531,
   n403,38072847,pos403,cp403,ivec167,dvec167,dpos167,vp167,ivec175,dvec175,dpos175,vp175⟩

private def bk532 : BoundKit true :=
  ⟨532,eb532,indexOk532.1,indexOk532.2,lookup532,rfl,threshold532,
   n404,417072227,pos404,cp404,ivec168,dvec168,dpos168,vp168,ivec155,dvec155,dpos155,vp155⟩

private def bk534 : BoundKit true :=
  ⟨534,eb534,indexOk534.1,indexOk534.2,lookup534,rfl,threshold534,
   n405,7201246,pos405,cp405,ivec170,dvec170,dpos170,vp170,ivec109,dvec109,dpos109,vp109⟩

private def bk535 : BoundKit false :=
  ⟨535,eb535,indexOk535.1,indexOk535.2,lookup535,rfl,threshold535,
   n406,4810125,pos406,cp406,ivec166,dvec166,dpos166,vp166,ivec29,dvec29,dpos29,vp29⟩

private def bk536 : BoundKit true :=
  ⟨536,eb536,indexOk536.1,indexOk536.2,lookup536,rfl,threshold536,
   n407,43484447,pos407,cp407,ivec170,dvec170,dpos170,vp170,ivec111,dvec111,dpos111,vp111⟩

private def bk537 : BoundKit true :=
  ⟨537,eb537,indexOk537.1,indexOk537.2,lookup537,rfl,threshold537,
   n408,80645279,pos408,cp408,ivec171,dvec171,dpos171,vp171,ivec109,dvec109,dpos109,vp109⟩

private def bk538 : BoundKit false :=
  ⟨538,eb538,indexOk538.1,indexOk538.2,lookup538,rfl,threshold538,
   n409,21903658,pos409,cp409,ivec99,dvec99,dpos99,vp99,ivec24,dvec24,dpos24,vp24⟩

private def bk539 : BoundKit false :=
  ⟨539,eb539,indexOk539.1,indexOk539.2,lookup539,rfl,threshold539,
   n410,9478,pos410,cp410,ivec75,dvec75,dpos75,vp75,ivec26,dvec26,dpos26,vp26⟩

private def bk540 : BoundKit false :=
  ⟨540,eb540,indexOk540.1,indexOk540.2,lookup540,rfl,threshold540,
   n411,11144771,pos411,cp411,ivec113,dvec113,dpos113,vp113,ivec27,dvec27,dpos27,vp27⟩

private def bk545 : BoundKit false :=
  ⟨545,eb545,indexOk545.1,indexOk545.2,lookup545,rfl,threshold545,
   n413,3129094,pos413,cp413,ivec99,dvec99,dpos99,vp99,ivec24,dvec24,dpos24,vp24⟩

private def bk547 : BoundKit false :=
  ⟨547,eb547,indexOk547.1,indexOk547.2,lookup547,rfl,threshold547,
   n412,26342186,pos412,cp412,ivec113,dvec113,dpos113,vp113,ivec28,dvec28,dpos28,vp28⟩

private def bk550 : BoundKit false :=
  ⟨550,eb550,indexOk550.1,indexOk550.2,lookup550,rfl,threshold550,
   n414,366553,pos414,cp414,ivec176,dvec176,dpos176,vp176,ivec27,dvec27,dpos27,vp27⟩

private def bk553 : BoundKit true :=
  ⟨553,eb553,indexOk553.1,indexOk553.2,lookup553,rfl,threshold553,
   n415,200296174,pos415,cp415,ivec177,dvec177,dpos177,vp177,ivec109,dvec109,dpos109,vp109⟩

private def bk554 : BoundKit true :=
  ⟨554,eb554,indexOk554.1,indexOk554.2,lookup554,rfl,threshold554,
   n416,1209480743,pos416,cp416,ivec177,dvec177,dpos177,vp177,ivec111,dvec111,dpos111,vp111⟩

private def bk555 : BoundKit true :=
  ⟨555,eb555,indexOk555.1,indexOk555.2,lookup555,rfl,threshold555,
   n417,3685184893,pos417,cp417,ivec178,dvec178,dpos178,vp178,ivec109,dvec109,dpos109,vp109⟩

private def bk556 : BoundKit false :=
  ⟨556,eb556,indexOk556.1,indexOk556.2,lookup556,rfl,threshold556,
   n418,221882259,pos418,cp418,ivec113,dvec113,dpos113,vp113,ivec154,dvec154,dpos154,vp154⟩

private def bk557 : BoundKit false :=
  ⟨557,eb557,indexOk557.1,indexOk557.2,lookup557,rfl,threshold557,
   n419,466054060,pos419,cp419,ivec113,dvec113,dpos113,vp113,ivec153,dvec153,dpos153,vp153⟩

private def bk558 : BoundKit false :=
  ⟨558,eb558,indexOk558.1,indexOk558.2,lookup558,rfl,threshold558,
   n420,773927823,pos420,cp420,ivec179,dvec179,dpos179,vp179,ivec154,dvec154,dpos154,vp154⟩

private def bk559 : BoundKit false :=
  ⟨559,eb559,indexOk559.1,indexOk559.2,lookup559,rfl,threshold559,
   n446,29526,pos446,cp446,ivec190,dvec190,dpos190,vp190,ivec191,dvec191,dpos191,vp191⟩

private def bk560 : BoundKit false :=
  ⟨560,eb560,indexOk560.1,indexOk560.2,lookup560,rfl,threshold560,
   n421,539327,pos421,cp421,ivec143,dvec143,dpos143,vp143,ivec180,dvec180,dpos180,vp180⟩

private def bk564 : BoundKit true :=
  ⟨564,eb564,indexOk564.1,indexOk564.2,lookup564,rfl,threshold564,
   n422,2345,pos422,cp422,ivec163,dvec163,dpos163,vp163,ivec139,dvec139,dpos139,vp139⟩

private def bk567 : BoundKit true :=
  ⟨567,eb567,indexOk567.1,indexOk567.2,lookup567,rfl,threshold567,
   n423,349762,pos423,cp423,ivec145,dvec145,dpos145,vp145,ivec181,dvec181,dpos181,vp181⟩

private def bk568 : BoundKit false :=
  ⟨568,eb568,indexOk568.1,indexOk568.2,lookup568,rfl,threshold568,
   n424,3423554,pos424,cp424,ivec143,dvec143,dpos143,vp143,ivec182,dvec182,dpos182,vp182⟩

private def bk569 : BoundKit true :=
  ⟨569,eb569,indexOk569.1,indexOk569.2,lookup569,rfl,threshold569,
   n427,178450,pos427,cp427,ivec145,dvec145,dpos145,vp145,ivec181,dvec181,dpos181,vp181⟩

private def bk570 : BoundKit true :=
  ⟨570,eb570,indexOk570.1,indexOk570.2,lookup570,rfl,threshold570,
   n428,4690,pos428,cp428,ivec163,dvec163,dpos163,vp163,ivec183,dvec183,dpos183,vp183⟩

private def bk571 : BoundKit false :=
  ⟨571,eb571,indexOk571.1,indexOk571.2,lookup571,rfl,threshold571,
   n429,22600513,pos429,cp429,ivec147,dvec147,dpos147,vp147,ivec180,dvec180,dpos180,vp180⟩

private def bk573 : BoundKit false :=
  ⟨573,eb573,indexOk573.1,indexOk573.2,lookup573,rfl,threshold573,
   n431,16953627,pos431,cp431,ivec143,dvec143,dpos143,vp143,ivec184,dvec184,dpos184,vp184⟩

private def bk575 : BoundKit false :=
  ⟨575,eb575,indexOk575.1,indexOk575.2,lookup575,rfl,threshold575,
   n432,10786540,pos432,cp432,ivec143,dvec143,dpos143,vp143,ivec185,dvec185,dpos185,vp185⟩

private def bk576 : BoundKit false :=
  ⟨576,eb576,indexOk576.1,indexOk576.2,lookup576,rfl,threshold576,
   n433,236814071,pos433,cp433,ivec147,dvec147,dpos147,vp147,ivec184,dvec184,dpos184,vp184⟩

private def bk577 : BoundKit true :=
  ⟨577,eb577,indexOk577.1,indexOk577.2,lookup577,rfl,threshold577,
   n434,6576450,pos434,cp434,ivec135,dvec135,dpos135,vp135,ivec4,dvec4,dpos4,vp4⟩

private def bk578 : BoundKit true :=
  ⟨578,eb578,indexOk578.1,indexOk578.2,lookup578,rfl,threshold578,
   n435,510,pos435,cp435,ivec59,dvec59,dpos59,vp59,ivec7,dvec7,dpos7,vp7⟩

private def bk579 : BoundKit false :=
  ⟨579,eb579,indexOk579.1,indexOk579.2,lookup579,rfl,threshold579,
   n436,22729957,pos436,cp436,ivec151,dvec151,dpos151,vp151,ivec180,dvec180,dpos180,vp180⟩

private def bk581 : BoundKit false :=
  ⟨581,eb581,indexOk581.1,indexOk581.2,lookup581,rfl,threshold581,
   n437,72142907,pos437,cp437,ivec151,dvec151,dpos151,vp151,ivec182,dvec182,dpos182,vp182⟩

private def bk582 : BoundKit false :=
  ⟨582,eb582,indexOk582.1,indexOk582.2,lookup582,rfl,threshold582,
   n438,952499483,pos438,cp438,ivec152,dvec152,dpos152,vp152,ivec180,dvec180,dpos180,vp180⟩

private def bk583 : BoundKit true :=
  ⟨583,eb583,indexOk583.1,indexOk583.2,lookup583,rfl,threshold583,
   n439,53963533,pos439,cp439,ivec187,dvec187,dpos187,vp187,ivec137,dvec137,dpos137,vp137⟩

private def bk584 : BoundKit false :=
  ⟨584,eb584,indexOk584.1,indexOk584.2,lookup584,rfl,threshold584,
   n440,1807526,pos440,cp440,ivec186,dvec186,dpos186,vp186,ivec134,dvec134,dpos134,vp134⟩

private def bk585 : BoundKit false :=
  ⟨585,eb585,indexOk585.1,indexOk585.2,lookup585,rfl,threshold585,
   n444,84286,pos444,cp444,ivec188,dvec188,dpos188,vp188,ivec139,dvec139,dpos139,vp139⟩

private def bk586 : BoundKit true :=
  ⟨586,eb586,indexOk586.1,indexOk586.2,lookup586,rfl,threshold586,
   n443,651713437,pos443,cp443,ivec187,dvec187,dpos187,vp187,ivec189,dvec189,dpos189,vp189⟩

private def bk590 : BoundKit true :=
  ⟨590,eb590,indexOk590.1,indexOk590.2,lookup590,rfl,threshold590,
   n447,1666646111,pos447,cp447,ivec192,dvec192,dpos192,vp192,ivec137,dvec137,dpos137,vp137⟩

private def bk591 : BoundKit false :=
  ⟨591,eb591,indexOk591.1,indexOk591.2,lookup591,rfl,threshold591,
   n448,1291090,pos448,cp448,ivec186,dvec186,dpos186,vp186,ivec134,dvec134,dpos134,vp134⟩

private def bk592 : BoundKit true :=
  ⟨592,eb592,indexOk592.1,indexOk592.2,lookup592,rfl,threshold592,
   n450,4600479,pos450,cp450,ivec193,dvec193,dpos193,vp193,ivec137,dvec137,dpos137,vp137⟩

private def bk595 : BoundKit true :=
  ⟨595,eb595,indexOk595.1,indexOk595.2,lookup595,rfl,threshold595,
   n451,55559631,pos451,cp451,ivec193,dvec193,dpos193,vp193,ivec189,dvec189,dpos189,vp189⟩

private def bk598 : BoundKit true :=
  ⟨598,eb598,indexOk598.1,indexOk598.2,lookup598,rfl,threshold598,
   n452,142084293,pos452,cp452,ivec194,dvec194,dpos194,vp194,ivec137,dvec137,dpos137,vp137⟩

private def bk601 : BoundKit true :=
  ⟨601,eb601,indexOk601.1,indexOk601.2,lookup601,rfl,threshold601,
   n446,29526,pos446,cp446,ivec190,dvec190,dpos190,vp190,ivec191,dvec191,dpos191,vp191⟩

private def bk603 : BoundKit true :=
  ⟨603,eb603,indexOk603.1,indexOk603.2,lookup603,rfl,threshold603,
   n453,7770,pos453,cp453,ivec148,dvec148,dpos148,vp148,ivec139,dvec139,dpos139,vp139⟩

private def bk604 : BoundKit true :=
  ⟨604,eb604,indexOk604.1,indexOk604.2,lookup604,rfl,threshold604,
   n454,1064531,pos454,cp454,ivec140,dvec140,dpos140,vp140,ivec137,dvec137,dpos137,vp137⟩

private def bk606 : BoundKit true :=
  ⟨606,eb606,indexOk606.1,indexOk606.2,lookup606,rfl,threshold606,
   n455,167131367,pos455,cp455,ivec140,dvec140,dpos140,vp140,ivec189,dvec189,dpos189,vp189⟩

private def bk607 : BoundKit true :=
  ⟨607,eb607,indexOk607.1,indexOk607.2,lookup607,rfl,threshold607,
   n460,91686,pos460,cp460,ivec141,dvec141,dpos141,vp141,ivec134,dvec134,dpos134,vp134⟩

private def bk608 : BoundKit true :=
  ⟨608,eb608,indexOk608.1,indexOk608.2,lookup608,rfl,threshold608,
   n461,327450,pos461,cp461,ivec141,dvec141,dpos141,vp141,ivec134,dvec134,dpos134,vp134⟩

private def bk609 : BoundKit true :=
  ⟨609,eb609,indexOk609.1,indexOk609.2,lookup609,rfl,threshold609,
   n456,128644477,pos456,cp456,ivec142,dvec142,dpos142,vp142,ivec137,dvec137,dpos137,vp137⟩

private def bk611 : BoundKit true :=
  ⟨611,eb611,indexOk611.1,indexOk611.2,lookup611,rfl,threshold611,
   n457,90753,pos457,cp457,ivec195,dvec195,dpos195,vp195,ivec137,dvec137,dpos137,vp137⟩

private def bk612 : BoundKit true :=
  ⟨612,eb612,indexOk612.1,indexOk612.2,lookup612,rfl,threshold612,
   n458,14248221,pos458,cp458,ivec195,dvec195,dpos195,vp195,ivec196,dvec196,dpos196,vp196⟩

private def bk613 : BoundKit true :=
  ⟨613,eb613,indexOk613.1,indexOk613.2,lookup613,rfl,threshold613,
   n459,97513,pos459,cp459,ivec197,dvec197,dpos197,vp197,ivec137,dvec137,dpos137,vp137⟩

private def bk620 : BoundKit false :=
  ⟨620,eb620,indexOk620.1,indexOk620.2,lookup620,rfl,threshold620,
   n140,147323,pos140,cp140,ivec67,dvec67,dpos67,vp67,ivec11,dvec11,dpos11,vp11⟩

private def bk621 : BoundKit true :=
  ⟨621,eb621,indexOk621.1,indexOk621.2,lookup621,rfl,threshold621,
   n462,700271,pos462,cp462,ivec173,dvec173,dpos173,vp173,ivec53,dvec53,dpos53,vp53⟩

private def bk627 : BoundKit true :=
  ⟨627,eb627,indexOk627.1,indexOk627.2,lookup627,rfl,threshold627,
   n463,10527803,pos463,cp463,ivec174,dvec174,dpos174,vp174,ivec53,dvec53,dpos53,vp53⟩

private def bk630 : BoundKit true :=
  ⟨630,eb630,indexOk630.1,indexOk630.2,lookup630,rfl,threshold630,
   n140,147323,pos140,cp140,ivec67,dvec67,dpos67,vp67,ivec11,dvec11,dpos11,vp11⟩

private def bk631 : BoundKit false :=
  ⟨631,eb631,indexOk631.1,indexOk631.2,lookup631,rfl,threshold631,
   n143,7660796,pos143,cp143,ivec67,dvec67,dpos67,vp67,ivec12,dvec12,dpos12,vp12⟩

private def bk632 : BoundKit false :=
  ⟨632,eb632,indexOk632.1,indexOk632.2,lookup632,rfl,threshold632,
   n144,5421097,pos144,cp144,ivec68,dvec68,dpos68,vp68,ivec11,dvec11,dpos11,vp11⟩

private def bk639 : BoundKit true :=
  ⟨639,eb639,indexOk639.1,indexOk639.2,lookup639,rfl,threshold639,
   n464,51991484,pos464,cp464,ivec199,dvec199,dpos199,vp199,ivec198,dvec198,dpos198,vp198⟩

private def bk642 : BoundKit true :=
  ⟨642,eb642,indexOk642.1,indexOk642.2,lookup642,rfl,threshold642,
   n466,547307,pos466,cp466,ivec200,dvec200,dpos200,vp200,ivec198,dvec198,dpos198,vp198⟩

private def bk645 : BoundKit false :=
  ⟨645,eb645,indexOk645.1,indexOk645.2,lookup645,rfl,threshold645,
   n467,72486589,pos467,cp467,ivec201,dvec201,dpos201,vp201,ivec134,dvec134,dpos134,vp134⟩

private def bk646 : BoundKit false :=
  ⟨646,eb646,indexOk646.1,indexOk646.2,lookup646,rfl,threshold646,
   n478,22549813,pos478,cp478,ivec205,dvec205,dpos205,vp205,ivec206,dvec206,dpos206,vp206⟩

private def bk647 : BoundKit false :=
  ⟨647,eb647,indexOk647.1,indexOk647.2,lookup647,rfl,threshold647,
   n475,637177,pos475,cp475,ivec204,dvec204,dpos204,vp204,ivec139,dvec139,dpos139,vp139⟩

private def bk648 : BoundKit false :=
  ⟨648,eb648,indexOk648.1,indexOk648.2,lookup648,rfl,threshold648,
   n477,1046054,pos477,cp477,ivec203,dvec203,dpos203,vp203,ivec139,dvec139,dpos139,vp139⟩

private def bk654 : BoundKit false :=
  ⟨654,eb654,indexOk654.1,indexOk654.2,lookup654,rfl,threshold654,
   n481,106599116,pos481,cp481,ivec205,dvec205,dpos205,vp205,ivec207,dvec207,dpos207,vp207⟩

private def bk655 : BoundKit true :=
  ⟨655,eb655,indexOk655.1,indexOk655.2,lookup655,rfl,threshold655,
   n470,10028555,pos470,cp470,ivec202,dvec202,dpos202,vp202,ivec181,dvec181,dpos181,vp181⟩

private def bk656 : BoundKit true :=
  ⟨656,eb656,indexOk656.1,indexOk656.2,lookup656,rfl,threshold656,
   n473,523027,pos473,cp473,ivec203,dvec203,dpos203,vp203,ivec183,dvec183,dpos183,vp183⟩

private def bk657 : BoundKit false :=
  ⟨657,eb657,indexOk657.1,indexOk657.2,lookup657,rfl,threshold657,
   n482,784259531,pos482,cp482,ivec208,dvec208,dpos208,vp208,ivec206,dvec206,dpos206,vp206⟩

private def bk666 : BoundKit false :=
  ⟨666,eb666,indexOk666.1,indexOk666.2,lookup666,rfl,threshold666,
   n484,10355227,pos484,cp484,ivec201,dvec201,dpos201,vp201,ivec134,dvec134,dpos134,vp134⟩

private def bk669 : BoundKit true :=
  ⟨669,eb669,indexOk669.1,indexOk669.2,lookup669,rfl,threshold669,
   n485,1258,pos485,cp485,ivec209,dvec209,dpos209,vp209,ivec139,dvec139,dpos139,vp139⟩

private def bk670 : BoundKit true :=
  ⟨670,eb670,indexOk670.1,indexOk670.2,lookup670,rfl,threshold670,
   n486,10727197,pos486,cp486,ivec138,dvec138,dpos138,vp138,ivec210,dvec210,dpos210,vp210⟩

private def bk673 : BoundKit true :=
  ⟨673,eb673,indexOk673.1,indexOk673.2,lookup673,rfl,threshold673,
   n489,510,pos489,cp489,ivec59,dvec59,dpos59,vp59,ivec211,dvec211,dpos211,vp211⟩

private def bk677 : BoundKit true :=
  ⟨677,eb677,indexOk677.1,indexOk677.2,lookup677,rfl,threshold677,
   n492,613802,pos492,cp492,ivec135,dvec135,dpos135,vp135,ivec212,dvec212,dpos212,vp212⟩

private def bk679 : BoundKit true :=
  ⟨679,eb679,indexOk679.1,indexOk679.2,lookup679,rfl,threshold679,
   n494,2192150,pos494,cp494,ivec135,dvec135,dpos135,vp135,ivec212,dvec212,dpos212,vp212⟩

private def bk680 : BoundKit true :=
  ⟨680,eb680,indexOk680.1,indexOk680.2,lookup680,rfl,threshold680,
   n495,170,pos495,cp495,ivec59,dvec59,dpos59,vp59,ivec213,dvec213,dpos213,vp213⟩

private def bk683 : BoundKit false :=
  ⟨683,eb683,indexOk683.1,indexOk683.2,lookup683,rfl,threshold683,
   n497,72486589,pos497,cp497,ivec201,dvec201,dpos201,vp201,ivec4,dvec4,dpos4,vp4⟩

private def bk684 : BoundKit false :=
  ⟨684,eb684,indexOk684.1,indexOk684.2,lookup684,rfl,threshold684,
   n500,22549813,pos500,cp500,ivec205,dvec205,dpos205,vp205,ivec11,dvec11,dpos11,vp11⟩

private def bk685 : BoundKit false :=
  ⟨685,eb685,indexOk685.1,indexOk685.2,lookup685,rfl,threshold685,
   n498,637177,pos498,cp498,ivec204,dvec204,dpos204,vp204,ivec7,dvec7,dpos7,vp7⟩

private def bk686 : BoundKit false :=
  ⟨686,eb686,indexOk686.1,indexOk686.2,lookup686,rfl,threshold686,
   n499,1046054,pos499,cp499,ivec203,dvec203,dpos203,vp203,ivec7,dvec7,dpos7,vp7⟩

private def bk692 : BoundKit false :=
  ⟨692,eb692,indexOk692.1,indexOk692.2,lookup692,rfl,threshold692,
   n501,106599116,pos501,cp501,ivec205,dvec205,dpos205,vp205,ivec12,dvec12,dpos12,vp12⟩

private def bk695 : BoundKit false :=
  ⟨695,eb695,indexOk695.1,indexOk695.2,lookup695,rfl,threshold695,
   n502,784259531,pos502,cp502,ivec208,dvec208,dpos208,vp208,ivec11,dvec11,dpos11,vp11⟩

private def bk704 : BoundKit false :=
  ⟨704,eb704,indexOk704.1,indexOk704.2,lookup704,rfl,threshold704,
   n503,51776135,pos503,cp503,ivec201,dvec201,dpos201,vp201,ivec4,dvec4,dpos4,vp4⟩

private def bk708 : BoundKit true :=
  ⟨708,eb708,indexOk708.1,indexOk708.2,lookup708,rfl,threshold708,
   n504,10727197,pos504,cp504,ivec138,dvec138,dpos138,vp138,ivec15,dvec15,dpos15,vp15⟩

private def bk711 : BoundKit true :=
  ⟨711,eb711,indexOk711.1,indexOk711.2,lookup711,rfl,threshold711,
   n505,170,pos505,cp505,ivec59,dvec59,dpos59,vp59,ivec20,dvec20,dpos20,vp20⟩

private def bk715 : BoundKit true :=
  ⟨715,eb715,indexOk715.1,indexOk715.2,lookup715,rfl,threshold715,
   n506,613802,pos506,cp506,ivec135,dvec135,dpos135,vp135,ivec74,dvec74,dpos74,vp74⟩

private def bk717 : BoundKit true :=
  ⟨717,eb717,indexOk717.1,indexOk717.2,lookup717,rfl,threshold717,
   n507,2192150,pos507,cp507,ivec135,dvec135,dpos135,vp135,ivec74,dvec74,dpos74,vp74⟩

private def bk718 : BoundKit true :=
  ⟨718,eb718,indexOk718.1,indexOk718.2,lookup718,rfl,threshold718,
   n508,170,pos508,cp508,ivec59,dvec59,dpos59,vp59,ivec76,dvec76,dpos76,vp76⟩

private def bk721 : BoundKit false :=
  ⟨721,eb721,indexOk721.1,indexOk721.2,lookup721,rfl,threshold721,
   n509,1807526,pos509,cp509,ivec186,dvec186,dpos186,vp186,ivec4,dvec4,dpos4,vp4⟩

private def bk722 : BoundKit false :=
  ⟨722,eb722,indexOk722.1,indexOk722.2,lookup722,rfl,threshold722,
   n516,7488217,pos516,cp516,ivec216,dvec216,dpos216,vp216,ivec11,dvec11,dpos11,vp11⟩

private def bk723 : BoundKit false :=
  ⟨723,eb723,indexOk723.1,indexOk723.2,lookup723,rfl,threshold723,
   n513,421430,pos513,cp513,ivec188,dvec188,dpos188,vp188,ivec7,dvec7,dpos7,vp7⟩

private def bk724 : BoundKit false :=
  ⟨724,eb724,indexOk724.1,indexOk724.2,lookup724,rfl,threshold724,
   n514,161581,pos514,cp514,ivec215,dvec215,dpos215,vp215,ivec7,dvec7,dpos7,vp7⟩

private def bk730 : BoundKit false :=
  ⟨730,eb730,indexOk730.1,indexOk730.2,lookup730,rfl,threshold730,
   n518,35398844,pos518,cp518,ivec216,dvec216,dpos216,vp216,ivec12,dvec12,dpos12,vp12⟩

private def bk731 : BoundKit true :=
  ⟨731,eb731,indexOk731.1,indexOk731.2,lookup731,rfl,threshold731,
   n510,48468670,pos510,cp510,ivec214,dvec214,dpos214,vp214,ivec5,dvec5,dpos5,vp5⟩

private def bk733 : BoundKit false :=
  ⟨733,eb733,indexOk733.1,indexOk733.2,lookup733,rfl,threshold733,
   n519,132663949,pos519,cp519,ivec217,dvec217,dpos217,vp217,ivec11,dvec11,dpos11,vp11⟩

private def bk742 : BoundKit false :=
  ⟨742,eb742,indexOk742.1,indexOk742.2,lookup742,rfl,threshold742,
   n521,6455450,pos521,cp521,ivec186,dvec186,dpos186,vp186,ivec4,dvec4,dpos4,vp4⟩

private def bk746 : BoundKit true :=
  ⟨746,eb746,indexOk746.1,indexOk746.2,lookup746,rfl,threshold746,
   n522,90753,pos522,cp522,ivec195,dvec195,dpos195,vp195,ivec15,dvec15,dpos15,vp15⟩

private def bk751 : BoundKit true :=
  ⟨751,eb751,indexOk751.1,indexOk751.2,lookup751,rfl,threshold751,
   n523,4749407,pos523,cp523,ivec195,dvec195,dpos195,vp195,ivec71,dvec71,dpos71,vp71⟩

private def bk755 : BoundKit true :=
  ⟨755,eb755,indexOk755.1,indexOk755.2,lookup755,rfl,threshold755,
   n524,97513,pos524,cp524,ivec197,dvec197,dpos197,vp197,ivec15,dvec15,dpos15,vp15⟩

private def bk757 : BoundKit true :=
  ⟨757,eb757,indexOk757.1,indexOk757.2,lookup757,rfl,threshold757,
   n525,1295,pos525,cp525,ivec148,dvec148,dpos148,vp148,ivec20,dvec20,dpos20,vp20⟩

private def bk761 : BoundKit true :=
  ⟨761,eb761,indexOk761.1,indexOk761.2,lookup761,rfl,threshold761,
   n526,76405,pos526,cp526,ivec141,dvec141,dpos141,vp141,ivec74,dvec74,dpos74,vp74⟩

private def bk765 : BoundKit true :=
  ⟨765,eb765,indexOk765.1,indexOk765.2,lookup765,rfl,threshold765,
   n527,272875,pos527,cp527,ivec141,dvec141,dpos141,vp141,ivec74,dvec74,dpos74,vp74⟩

private def bk766 : BoundKit true :=
  ⟨766,eb766,indexOk766.1,indexOk766.2,lookup766,rfl,threshold766,
   n528,1295,pos528,cp528,ivec148,dvec148,dpos148,vp148,ivec76,dvec76,dpos76,vp76⟩

private def bk771 : BoundKit false :=
  ⟨771,eb771,indexOk771.1,indexOk771.2,lookup771,rfl,threshold771,
   n529,98279839,pos529,cp529,ivec202,dvec202,dpos202,vp202,ivec24,dvec24,dpos24,vp24⟩

private def bk772 : BoundKit false :=
  ⟨772,eb772,indexOk772.1,indexOk772.2,lookup772,rfl,threshold772,
   n531,1734601,pos531,cp531,ivec205,dvec205,dpos205,vp205,ivec27,dvec27,dpos27,vp27⟩

private def bk773 : BoundKit false :=
  ⟨773,eb773,indexOk773.1,indexOk773.2,lookup773,rfl,threshold773,
   n530,523027,pos530,cp530,ivec203,dvec203,dpos203,vp203,ivec26,dvec26,dpos26,vp26⟩

private def bk780 : BoundKit false :=
  ⟨780,eb780,indexOk780.1,indexOk780.2,lookup780,rfl,threshold780,
   n532,2005711,pos532,cp532,ivec202,dvec202,dpos202,vp202,ivec24,dvec24,dpos24,vp24⟩

private def bk783 : BoundKit false :=
  ⟨783,eb783,indexOk783.1,indexOk783.2,lookup783,rfl,threshold783,
   n533,53299558,pos533,cp533,ivec205,dvec205,dpos205,vp205,ivec28,dvec28,dpos28,vp28⟩

private def bk788 : BoundKit false :=
  ⟨788,eb788,indexOk788.1,indexOk788.2,lookup788,rfl,threshold788,
   n534,27179581,pos534,cp534,ivec218,dvec218,dpos218,vp218,ivec27,dvec27,dpos27,vp27⟩

private def bk792 : BoundKit true :=
  ⟨792,eb792,indexOk792.1,indexOk792.2,lookup792,rfl,threshold792,
   n536,10727197,pos536,cp536,ivec138,dvec138,dpos138,vp138,ivec32,dvec32,dpos32,vp32⟩

private def bk795 : BoundKit true :=
  ⟨795,eb795,indexOk795.1,indexOk795.2,lookup795,rfl,threshold795,
   n537,920703,pos537,cp537,ivec135,dvec135,dpos135,vp135,ivec79,dvec79,dpos79,vp79⟩

private def bk797 : BoundKit true :=
  ⟨797,eb797,indexOk797.1,indexOk797.2,lookup797,rfl,threshold797,
   n538,3288225,pos538,cp538,ivec135,dvec135,dpos135,vp135,ivec79,dvec79,dpos79,vp79⟩

private def bk798 : BoundKit true :=
  ⟨798,eb798,indexOk798.1,indexOk798.2,lookup798,rfl,threshold798,
   n539,255,pos539,cp539,ivec59,dvec59,dpos59,vp59,ivec36,dvec36,dpos36,vp36⟩

private def bk801 : BoundKit false :=
  ⟨801,eb801,indexOk801.1,indexOk801.2,lookup801,rfl,threshold801,
   n540,28079954,pos540,cp540,ivec202,dvec202,dpos202,vp202,ivec81,dvec81,dpos81,vp81⟩

private def bk802 : BoundKit false :=
  ⟨802,eb802,indexOk802.1,indexOk802.2,lookup802,rfl,threshold802,
   n542,106599116,pos542,cp542,ivec205,dvec205,dpos205,vp205,ivec86,dvec86,dpos86,vp86⟩

private def bk803 : BoundKit false :=
  ⟨803,eb803,indexOk803.1,indexOk803.2,lookup803,rfl,threshold803,
   n541,1046054,pos541,cp541,ivec203,dvec203,dpos203,vp203,ivec83,dvec83,dpos83,vp83⟩

private def bk808 : BoundKit false :=
  ⟨808,eb808,indexOk808.1,indexOk808.2,lookup808,rfl,threshold808,
   n543,20057110,pos543,cp543,ivec202,dvec202,dpos202,vp202,ivec81,dvec81,dpos81,vp81⟩

private def bk810 : BoundKit true :=
  ⟨810,eb810,indexOk810.1,indexOk810.2,lookup810,rfl,threshold810,
   n544,10727197,pos544,cp544,ivec138,dvec138,dpos138,vp138,ivec87,dvec87,dpos87,vp87⟩

private def bk813 : BoundKit true :=
  ⟨813,eb813,indexOk813.1,indexOk813.2,lookup813,rfl,threshold813,
   n545,1841406,pos545,cp545,ivec135,dvec135,dpos135,vp135,ivec219,dvec219,dpos219,vp219⟩

private def bk815 : BoundKit true :=
  ⟨815,eb815,indexOk815.1,indexOk815.2,lookup815,rfl,threshold815,
   n547,6576450,pos547,cp547,ivec135,dvec135,dpos135,vp135,ivec219,dvec219,dpos219,vp219⟩

private def bk816 : BoundKit true :=
  ⟨816,eb816,indexOk816.1,indexOk816.2,lookup816,rfl,threshold816,
   n548,510,pos548,cp548,ivec59,dvec59,dpos59,vp59,ivec93,dvec93,dpos93,vp93⟩

private def bk819 : BoundKit false :=
  ⟨819,eb819,indexOk819.1,indexOk819.2,lookup819,rfl,threshold819,
   n549,67856138,pos549,cp549,ivec214,dvec214,dpos214,vp214,ivec24,dvec24,dpos24,vp24⟩

private def bk820 : BoundKit false :=
  ⟨820,eb820,indexOk820.1,indexOk820.2,lookup820,rfl,threshold820,
   n551,7488217,pos551,cp551,ivec216,dvec216,dpos216,vp216,ivec27,dvec27,dpos27,vp27⟩

private def bk821 : BoundKit false :=
  ⟨821,eb821,indexOk821.1,indexOk821.2,lookup821,rfl,threshold821,
   n550,323162,pos550,cp550,ivec215,dvec215,dpos215,vp215,ivec26,dvec26,dpos26,vp26⟩

private def bk827 : BoundKit false :=
  ⟨827,eb827,indexOk827.1,indexOk827.2,lookup827,rfl,threshold827,
   n552,9693734,pos552,cp552,ivec214,dvec214,dpos214,vp214,ivec24,dvec24,dpos24,vp24⟩

private def bk830 : BoundKit false :=
  ⟨830,eb830,indexOk830.1,indexOk830.2,lookup830,rfl,threshold830,
   n553,17699422,pos553,cp553,ivec216,dvec216,dpos216,vp216,ivec28,dvec28,dpos28,vp28⟩

private def bk834 : BoundKit false :=
  ⟨834,eb834,indexOk834.1,indexOk834.2,lookup834,rfl,threshold834,
   n554,231271139,pos554,cp554,ivec220,dvec220,dpos220,vp220,ivec27,dvec27,dpos27,vp27⟩

private def bk838 : BoundKit true :=
  ⟨838,eb838,indexOk838.1,indexOk838.2,lookup838,rfl,threshold838,
   n555,90753,pos555,cp555,ivec195,dvec195,dpos195,vp195,ivec32,dvec32,dpos32,vp32⟩

private def bk842 : BoundKit true :=
  ⟨842,eb842,indexOk842.1,indexOk842.2,lookup842,rfl,threshold842,
   n556,84309,pos556,cp556,ivec195,dvec195,dpos195,vp195,ivec78,dvec78,dpos78,vp78⟩

private def bk845 : BoundKit true :=
  ⟨845,eb845,indexOk845.1,indexOk845.2,lookup845,rfl,threshold845,
   n557,97513,pos557,cp557,ivec197,dvec197,dpos197,vp197,ivec32,dvec32,dpos32,vp32⟩

private def bk847 : BoundKit true :=
  ⟨847,eb847,indexOk847.1,indexOk847.2,lookup847,rfl,threshold847,
   n558,91686,pos558,cp558,ivec141,dvec141,dpos141,vp141,ivec79,dvec79,dpos79,vp79⟩

private def bk851 : BoundKit true :=
  ⟨851,eb851,indexOk851.1,indexOk851.2,lookup851,rfl,threshold851,
   n559,327450,pos559,cp559,ivec141,dvec141,dpos141,vp141,ivec79,dvec79,dpos79,vp79⟩

private def bk852 : BoundKit true :=
  ⟨852,eb852,indexOk852.1,indexOk852.2,lookup852,rfl,threshold852,
   n560,1554,pos560,cp560,ivec148,dvec148,dpos148,vp148,ivec36,dvec36,dpos36,vp36⟩

private def bk857 : BoundKit false :=
  ⟨857,eb857,indexOk857.1,indexOk857.2,lookup857,rfl,threshold857,
   n561,10790913,pos561,cp561,ivec221,dvec221,dpos221,vp221,ivec4,dvec4,dpos4,vp4⟩

private def bk858 : BoundKit false :=
  ⟨858,eb858,indexOk858.1,indexOk858.2,lookup858,rfl,threshold858,
   n566,11017897,pos566,cp566,ivec223,dvec223,dpos223,vp223,ivec11,dvec11,dpos11,vp11⟩

private def bk859 : BoundKit false :=
  ⟨859,eb859,indexOk859.1,indexOk859.2,lookup859,rfl,threshold859,
   n564,38505,pos564,cp564,ivec222,dvec222,dpos222,vp222,ivec7,dvec7,dpos7,vp7⟩

private def bk862 : BoundKit false :=
  ⟨862,eb862,indexOk862.1,indexOk862.2,lookup862,rfl,threshold862,
   n569,52084604,pos569,cp569,ivec223,dvec223,dpos223,vp223,ivec12,dvec12,dpos12,vp12⟩

private def bk864 : BoundKit false :=
  ⟨864,eb864,indexOk864.1,indexOk864.2,lookup864,rfl,threshold864,
   n570,110140129,pos570,cp570,ivec224,dvec224,dpos224,vp224,ivec11,dvec11,dpos11,vp11⟩

private def bk872 : BoundKit false :=
  ⟨872,eb872,indexOk872.1,indexOk872.2,lookup872,rfl,threshold872,
   n572,38538975,pos572,cp572,ivec221,dvec221,dpos221,vp221,ivec4,dvec4,dpos4,vp4⟩

private def bk876 : BoundKit true :=
  ⟨876,eb876,indexOk876.1,indexOk876.2,lookup876,rfl,threshold876,
   n573,2100813,pos573,cp573,ivec173,dvec173,dpos173,vp173,ivec15,dvec15,dpos15,vp15⟩

private def bk880 : BoundKit true :=
  ⟨880,eb880,indexOk880.1,indexOk880.2,lookup880,rfl,threshold880,
   n577,8457119,pos577,cp577,ivec173,dvec173,dpos173,vp173,ivec22,dvec22,dpos22,vp22⟩

private def bk885 : BoundKit true :=
  ⟨885,eb885,indexOk885.1,indexOk885.2,lookup885,rfl,threshold885,
   n578,31583409,pos578,cp578,ivec174,dvec174,dpos174,vp174,ivec15,dvec15,dpos15,vp15⟩

private def bk889 : BoundKit false :=
  ⟨889,eb889,indexOk889.1,indexOk889.2,lookup889,rfl,threshold889,
   n579,96454246,pos579,cp579,ivec225,dvec225,dpos225,vp225,ivec4,dvec4,dpos4,vp4⟩

private def bk890 : BoundKit false :=
  ⟨890,eb890,indexOk890.1,indexOk890.2,lookup890,rfl,threshold890,
   n582,17679959,pos582,cp582,ivec85,dvec85,dpos85,vp85,ivec11,dvec11,dpos11,vp11⟩

private def bk891 : BoundKit false :=
  ⟨891,eb891,indexOk891.1,indexOk891.2,lookup891,rfl,threshold891,
   n581,454510,pos581,cp581,ivec84,dvec84,dpos84,vp84,ivec7,dvec7,dpos7,vp7⟩

private def bk894 : BoundKit false :=
  ⟨894,eb894,indexOk894.1,indexOk894.2,lookup894,rfl,threshold894,
   n583,83577988,pos583,cp583,ivec85,dvec85,dpos85,vp85,ivec12,dvec12,dpos12,vp12⟩

private def bk896 : BoundKit false :=
  ⟨896,eb896,indexOk896.1,indexOk896.2,lookup896,rfl,threshold896,
   n584,272669507,pos584,cp584,ivec226,dvec226,dpos226,vp226,ivec11,dvec11,dpos11,vp11⟩

private def bk904 : BoundKit false :=
  ⟨904,eb904,indexOk904.1,indexOk904.2,lookup904,rfl,threshold904,
   n586,49211350,pos586,cp586,ivec225,dvec225,dpos225,vp225,ivec4,dvec4,dpos4,vp4⟩

private def bk908 : BoundKit true :=
  ⟨908,eb908,indexOk908.1,indexOk908.2,lookup908,rfl,threshold908,
   n587,8433958,pos587,cp587,ivec88,dvec88,dpos88,vp88,ivec15,dvec15,dpos15,vp15⟩

private def bk912 : BoundKit true :=
  ⟨912,eb912,indexOk912.1,indexOk912.2,lookup912,rfl,threshold912,
   n588,15762614,pos588,cp588,ivec64,dvec64,dpos64,vp64,ivec18,dvec18,dpos18,vp18⟩

private def bk914 : BoundKit true :=
  ⟨914,eb914,indexOk914.1,indexOk914.2,lookup914,rfl,threshold914,
   n589,321686,pos589,cp589,ivec64,dvec64,dpos64,vp64,ivec18,dvec18,dpos18,vp18⟩

private def bk915 : BoundKit true :=
  ⟨915,eb915,indexOk915.1,indexOk915.2,lookup915,rfl,threshold915,
   n590,57974,pos590,cp590,ivec65,dvec65,dpos65,vp65,ivec20,dvec20,dpos20,vp20⟩

private def bk918 : BoundKit true :=
  ⟨918,eb918,indexOk918.1,indexOk918.2,lookup918,rfl,threshold918,
   n591,50928131,pos591,cp591,ivec88,dvec88,dpos88,vp88,ivec22,dvec22,dpos22,vp22⟩

private def bk923 : BoundKit true :=
  ⟨923,eb923,indexOk923.1,indexOk923.2,lookup923,rfl,threshold923,
   n592,29542461,pos592,cp592,ivec92,dvec92,dpos92,vp92,ivec15,dvec15,dpos15,vp15⟩

private def bk927 : BoundKit false :=
  ⟨927,eb927,indexOk927.1,indexOk927.2,lookup927,rfl,threshold927,
   n593,1891477,pos593,cp593,ivec227,dvec227,dpos227,vp227,ivec24,dvec24,dpos24,vp24⟩

private def bk928 : BoundKit false :=
  ⟨928,eb928,indexOk928.1,indexOk928.2,lookup928,rfl,threshold928,
   n598,11017897,pos598,cp598,ivec223,dvec223,dpos223,vp223,ivec27,dvec27,dpos27,vp27⟩

private def bk929 : BoundKit false :=
  ⟨929,eb929,indexOk929.1,indexOk929.2,lookup929,rfl,threshold929,
   n595,19765,pos595,cp595,ivec228,dvec228,dpos228,vp228,ivec26,dvec26,dpos26,vp26⟩

private def bk930 : BoundKit false :=
  ⟨930,eb930,indexOk930.1,indexOk930.2,lookup930,rfl,threshold930,
   n597,25670,pos597,cp597,ivec222,dvec222,dpos222,vp222,ivec26,dvec26,dpos26,vp26⟩

private def bk937 : BoundKit false :=
  ⟨937,eb937,indexOk937.1,indexOk937.2,lookup937,rfl,threshold937,
   n599,270211,pos599,cp599,ivec227,dvec227,dpos227,vp227,ivec24,dvec24,dpos24,vp24⟩

private def bk943 : BoundKit false :=
  ⟨943,eb943,indexOk943.1,indexOk943.2,lookup943,rfl,threshold943,
   n600,26042302,pos600,cp600,ivec223,dvec223,dpos223,vp223,ivec28,dvec28,dpos28,vp28⟩

private def bk948 : BoundKit false :=
  ⟨948,eb948,indexOk948.1,indexOk948.2,lookup948,rfl,threshold948,
   n601,67839167,pos601,cp601,ivec229,dvec229,dpos229,vp229,ivec27,dvec27,dpos27,vp27⟩

private def bk952 : BoundKit true :=
  ⟨952,eb952,indexOk952.1,indexOk952.2,lookup952,rfl,threshold952,
   n603,2100813,pos603,cp603,ivec173,dvec173,dpos173,vp173,ivec32,dvec32,dpos32,vp32⟩

private def bk960 : BoundKit true :=
  ⟨960,eb960,indexOk960.1,indexOk960.2,lookup960,rfl,threshold960,
   n606,12314,pos606,cp606,ivec69,dvec69,dpos69,vp69,ivec34,dvec34,dpos34,vp34⟩

private def bk962 : BoundKit true :=
  ⟨962,eb962,indexOk962.1,indexOk962.2,lookup962,rfl,threshold962,
   n607,25371357,pos607,cp607,ivec173,dvec173,dpos173,vp173,ivec35,dvec35,dpos35,vp35⟩

private def bk968 : BoundKit true :=
  ⟨968,eb968,indexOk968.1,indexOk968.2,lookup968,rfl,threshold968,
   n608,31583409,pos608,cp608,ivec174,dvec174,dpos174,vp174,ivec32,dvec32,dpos32,vp32⟩

private def bk972 : BoundKit true :=
  ⟨972,eb972,indexOk972.1,indexOk972.2,lookup972,rfl,threshold972,
   n609,12314,pos609,cp609,ivec69,dvec69,dpos69,vp69,ivec36,dvec36,dpos36,vp36⟩

private def bk973 : BoundKit false :=
  ⟨973,eb973,indexOk973.1,indexOk973.2,lookup973,rfl,threshold973,
   n610,56462,pos610,cp610,ivec227,dvec227,dpos227,vp227,ivec81,dvec81,dpos81,vp81⟩

private def bk974 : BoundKit false :=
  ⟨974,eb974,indexOk974.1,indexOk974.2,lookup974,rfl,threshold974,
   n614,52084604,pos614,cp614,ivec223,dvec223,dpos223,vp223,ivec86,dvec86,dpos86,vp86⟩

private def bk975 : BoundKit false :=
  ⟨975,eb975,indexOk975.1,indexOk975.2,lookup975,rfl,threshold975,
   n611,590,pos611,cp611,ivec228,dvec228,dpos228,vp228,ivec83,dvec83,dpos83,vp83⟩

private def bk976 : BoundKit false :=
  ⟨976,eb976,indexOk976.1,indexOk976.2,lookup976,rfl,threshold976,
   n612,1510,pos612,cp612,ivec222,dvec222,dpos222,vp222,ivec83,dvec83,dpos83,vp83⟩

private def bk983 : BoundKit false :=
  ⟨983,eb983,indexOk983.1,indexOk983.2,lookup983,rfl,threshold983,
   n615,201650,pos615,cp615,ivec227,dvec227,dpos227,vp227,ivec81,dvec81,dpos81,vp81⟩

private def bk984 : BoundKit true :=
  ⟨984,eb984,indexOk984.1,indexOk984.2,lookup984,rfl,threshold984,
   n613,1310,pos613,cp613,ivec66,dvec66,dpos66,vp66,ivec83,dvec83,dpos83,vp83⟩

private def bk986 : BoundKit true :=
  ⟨986,eb986,indexOk986.1,indexOk986.2,lookup986,rfl,threshold986,
   n616,2100813,pos616,cp616,ivec173,dvec173,dpos173,vp173,ivec87,dvec87,dpos87,vp87⟩

private def bk994 : BoundKit true :=
  ⟨994,eb994,indexOk994.1,indexOk994.2,lookup994,rfl,threshold994,
   n617,1160054,pos617,cp617,ivec100,dvec100,dpos100,vp100,ivec89,dvec89,dpos89,vp89⟩

private def bk996 : BoundKit true :=
  ⟨996,eb996,indexOk996.1,indexOk996.2,lookup996,rfl,threshold996,
   n618,828610,pos618,cp618,ivec100,dvec100,dpos100,vp100,ivec89,dvec89,dpos89,vp89⟩

private def bk997 : BoundKit true :=
  ⟨997,eb997,indexOk997.1,indexOk997.2,lookup997,rfl,threshold997,
   n619,12314,pos619,cp619,ivec69,dvec69,dpos69,vp69,ivec90,dvec90,dpos90,vp90⟩

private def bk1000 : BoundKit true :=
  ⟨1000,eb1000,indexOk1000.1,indexOk1000.2,lookup1000,rfl,threshold1000,
   n620,25371357,pos620,cp620,ivec173,dvec173,dpos173,vp173,ivec91,dvec91,dpos91,vp91⟩

private def bk1006 : BoundKit true :=
  ⟨1006,eb1006,indexOk1006.1,indexOk1006.2,lookup1006,rfl,threshold1006,
   n621,31583409,pos621,cp621,ivec174,dvec174,dpos174,vp174,ivec87,dvec87,dpos87,vp87⟩

private def bk1010 : BoundKit true :=
  ⟨1010,eb1010,indexOk1010.1,indexOk1010.2,lookup1010,rfl,threshold1010,
   n622,12314,pos622,cp622,ivec69,dvec69,dpos69,vp69,ivec93,dvec93,dpos93,vp93⟩

private def bk1011 : BoundKit false :=
  ⟨1011,eb1011,indexOk1011.1,indexOk1011.2,lookup1011,rfl,threshold1011,
   n623,21210854,pos623,cp623,ivec80,dvec80,dpos80,vp80,ivec24,dvec24,dpos24,vp24⟩

private def bk1012 : BoundKit false :=
  ⟨1012,eb1012,indexOk1012.1,indexOk1012.2,lookup1012,rfl,threshold1012,
   n626,17679959,pos626,cp626,ivec85,dvec85,dpos85,vp85,ivec27,dvec27,dpos27,vp27⟩

private def bk1013 : BoundKit false :=
  ⟨1013,eb1013,indexOk1013.1,indexOk1013.2,lookup1013,rfl,threshold1013,
   n624,198830,pos624,cp624,ivec82,dvec82,dpos82,vp82,ivec26,dvec26,dpos26,vp26⟩

private def bk1014 : BoundKit false :=
  ⟨1014,eb1014,indexOk1014.1,indexOk1014.2,lookup1014,rfl,threshold1014,
   n625,227255,pos625,cp625,ivec84,dvec84,dpos84,vp84,ivec26,dvec26,dpos26,vp26⟩

private def bk1021 : BoundKit false :=
  ⟨1021,eb1021,indexOk1021.1,indexOk1021.2,lookup1021,rfl,threshold1021,
   n627,3030122,pos627,cp627,ivec80,dvec80,dpos80,vp80,ivec24,dvec24,dpos24,vp24⟩

private def bk1027 : BoundKit false :=
  ⟨1027,eb1027,indexOk1027.1,indexOk1027.2,lookup1027,rfl,threshold1027,
   n628,125366982,pos628,cp628,ivec85,dvec85,dpos85,vp85,ivec28,dvec28,dpos28,vp28⟩

private def bk1032 : BoundKit false :=
  ⟨1032,eb1032,indexOk1032.1,indexOk1032.2,lookup1032,rfl,threshold1032,
   n629,1882548107,pos629,cp629,ivec230,dvec230,dpos230,vp230,ivec27,dvec27,dpos27,vp27⟩

private def bk1036 : BoundKit true :=
  ⟨1036,eb1036,indexOk1036.1,indexOk1036.2,lookup1036,rfl,threshold1036,
   n631,4216979,pos631,cp631,ivec88,dvec88,dpos88,vp88,ivec32,dvec32,dpos32,vp32⟩

private def bk1037 : BoundKit false :=
  ⟨1037,eb1037,indexOk1037.1,indexOk1037.2,lookup1037,rfl,threshold1037,
   n632,538734,pos632,cp632,ivec166,dvec166,dpos166,vp166,ivec79,dvec79,dpos79,vp79⟩

private def bk1044 : BoundKit true :=
  ⟨1044,eb1044,indexOk1044.1,indexOk1044.2,lookup1044,rfl,threshold1044,
   n633,2251802,pos633,cp633,ivec64,dvec64,dpos64,vp64,ivec33,dvec33,dpos33,vp33⟩

private def bk1046 : BoundKit true :=
  ⟨1046,eb1046,indexOk1046.1,indexOk1046.2,lookup1046,rfl,threshold1046,
   n634,1608430,pos634,cp634,ivec64,dvec64,dpos64,vp64,ivec33,dvec33,dpos33,vp33⟩

private def bk1047 : BoundKit true :=
  ⟨1047,eb1047,indexOk1047.1,indexOk1047.2,lookup1047,rfl,threshold1047,
   n635,57974,pos635,cp635,ivec65,dvec65,dpos65,vp65,ivec34,dvec34,dpos34,vp34⟩

private def bk1050 : BoundKit true :=
  ⟨1050,eb1050,indexOk1050.1,indexOk1050.2,lookup1050,rfl,threshold1050,
   n636,101856262,pos636,cp636,ivec88,dvec88,dpos88,vp88,ivec35,dvec35,dpos35,vp35⟩

private def bk1056 : BoundKit true :=
  ⟨1056,eb1056,indexOk1056.1,indexOk1056.2,lookup1056,rfl,threshold1056,
   n637,29542461,pos637,cp637,ivec92,dvec92,dpos92,vp92,ivec32,dvec32,dpos32,vp32⟩

private def bk1060 : BoundKit true :=
  ⟨1060,eb1060,indexOk1060.1,indexOk1060.2,lookup1060,rfl,threshold1060,
   n638,28987,pos638,cp638,ivec65,dvec65,dpos65,vp65,ivec36,dvec36,dpos36,vp36⟩

private def bk1061 : BoundKit false :=
  ⟨1061,eb1061,indexOk1061.1,indexOk1061.2,lookup1061,rfl,threshold1061,
   n639,104524931,pos639,cp639,ivec94,dvec94,dpos94,vp94,ivec24,dvec24,dpos24,vp24⟩

private def bk1062 : BoundKit false :=
  ⟨1062,eb1062,indexOk1062.1,indexOk1062.2,lookup1062,rfl,threshold1062,
   n642,54363419,pos642,cp642,ivec97,dvec97,dpos97,vp97,ivec27,dvec27,dpos27,vp27⟩

private def bk1063 : BoundKit false :=
  ⟨1063,eb1063,indexOk1063.1,indexOk1063.2,lookup1063,rfl,threshold1063,
   n640,921695,pos640,cp640,ivec95,dvec95,dpos95,vp95,ivec26,dvec26,dpos26,vp26⟩

private def bk1064 : BoundKit false :=
  ⟨1064,eb1064,indexOk1064.1,indexOk1064.2,lookup1064,rfl,threshold1064,
   n641,502670,pos641,cp641,ivec96,dvec96,dpos96,vp96,ivec26,dvec26,dpos26,vp26⟩

private def bk1071 : BoundKit false :=
  ⟨1071,eb1071,indexOk1071.1,indexOk1071.2,lookup1071,rfl,threshold1071,
   n643,14932133,pos643,cp643,ivec94,dvec94,dpos94,vp94,ivec24,dvec24,dpos24,vp24⟩

private def bk1077 : BoundKit false :=
  ⟨1077,eb1077,indexOk1077.1,indexOk1077.2,lookup1077,rfl,threshold1077,
   n644,385486062,pos644,cp644,ivec97,dvec97,dpos97,vp97,ivec28,dvec28,dpos28,vp28⟩

private def bk1082 : BoundKit false :=
  ⟨1082,eb1082,indexOk1082.1,indexOk1082.2,lookup1082,rfl,threshold1082,
   n645,72787979,pos645,cp645,ivec231,dvec231,dpos231,vp231,ivec27,dvec27,dpos27,vp27⟩

private def bk1086 : BoundKit true :=
  ⟨1086,eb1086,indexOk1086.1,indexOk1086.2,lookup1086,rfl,threshold1086,
   n647,312797329,pos647,cp647,ivec98,dvec98,dpos98,vp98,ivec32,dvec32,dpos32,vp32⟩

private def bk1087 : BoundKit false :=
  ⟨1087,eb1087,indexOk1087.1,indexOk1087.2,lookup1087,rfl,threshold1087,
   n648,14217,pos648,cp648,ivec75,dvec75,dpos75,vp75,ivec30,dvec30,dpos30,vp30⟩

private def bk1092 : BoundKit true :=
  ⟨1092,eb1092,indexOk1092.1,indexOk1092.2,lookup1092,rfl,threshold1092,
   n649,65710974,pos649,cp649,ivec99,dvec99,dpos99,vp99,ivec33,dvec33,dpos33,vp33⟩

private def bk1094 : BoundKit true :=
  ⟨1094,eb1094,indexOk1094.1,indexOk1094.2,lookup1094,rfl,threshold1094,
   n650,46936410,pos650,cp650,ivec99,dvec99,dpos99,vp99,ivec33,dvec33,dpos33,vp33⟩

private def bk1095 : BoundKit true :=
  ⟨1095,eb1095,indexOk1095.1,indexOk1095.2,lookup1095,rfl,threshold1095,
   n651,28434,pos651,cp651,ivec75,dvec75,dpos75,vp75,ivec34,dvec34,dpos34,vp34⟩

private def bk1098 : BoundKit true :=
  ⟨1098,eb1098,indexOk1098.1,indexOk1098.2,lookup1098,rfl,threshold1098,
   n652,28434,pos652,cp652,ivec75,dvec75,dpos75,vp75,ivec36,dvec36,dpos36,vp36⟩

private def bk1099 : BoundKit false :=
  ⟨1099,eb1099,indexOk1099.1,indexOk1099.2,lookup1099,rfl,threshold1099,
   n657,7488217,pos657,cp657,ivec216,dvec216,dpos216,vp216,ivec206,dvec206,dpos206,vp206⟩

private def bk1100 : BoundKit false :=
  ⟨1100,eb1100,indexOk1100.1,indexOk1100.2,lookup1100,rfl,threshold1100,
   n656,161581,pos656,cp656,ivec215,dvec215,dpos215,vp215,ivec139,dvec139,dpos139,vp139⟩

private def bk1104 : BoundKit true :=
  ⟨1104,eb1104,indexOk1104.1,indexOk1104.2,lookup1104,rfl,threshold1104,
   n653,67856138,pos653,cp653,ivec214,dvec214,dpos214,vp214,ivec181,dvec181,dpos181,vp181⟩

private def bk1105 : BoundKit false :=
  ⟨1105,eb1105,indexOk1105.1,indexOk1105.2,lookup1105,rfl,threshold1105,
   n658,35398844,pos658,cp658,ivec216,dvec216,dpos216,vp216,ivec207,dvec207,dpos207,vp207⟩

private def bk1106 : BoundKit true :=
  ⟨1106,eb1106,indexOk1106.1,indexOk1106.2,lookup1106,rfl,threshold1106,
   n654,48468670,pos654,cp654,ivec214,dvec214,dpos214,vp214,ivec181,dvec181,dpos181,vp181⟩

private def bk1107 : BoundKit true :=
  ⟨1107,eb1107,indexOk1107.1,indexOk1107.2,lookup1107,rfl,threshold1107,
   n655,323162,pos655,cp655,ivec215,dvec215,dpos215,vp215,ivec183,dvec183,dpos183,vp183⟩

private def bk1108 : BoundKit false :=
  ⟨1108,eb1108,indexOk1108.1,indexOk1108.2,lookup1108,rfl,threshold1108,
   n659,132663949,pos659,cp659,ivec217,dvec217,dpos217,vp217,ivec206,dvec206,dpos206,vp206⟩

private def bk1116 : BoundKit true :=
  ⟨1116,eb1116,indexOk1116.1,indexOk1116.2,lookup1116,rfl,threshold1116,
   n660,30251,pos660,cp660,ivec195,dvec195,dpos195,vp195,ivec210,dvec210,dpos210,vp210⟩

private def bk1121 : BoundKit true :=
  ⟨1121,eb1121,indexOk1121.1,indexOk1121.2,lookup1121,rfl,threshold1121,
   n661,14248221,pos661,cp661,ivec195,dvec195,dpos195,vp195,ivec232,dvec232,dpos232,vp232⟩

private def bk1122 : BoundKit true :=
  ⟨1122,eb1122,indexOk1122.1,indexOk1122.2,lookup1122,rfl,threshold1122,
   n683,349762,pos683,cp683,ivec145,dvec145,dpos145,vp145,ivec238,dvec238,dpos238,vp238⟩

private def bk1123 : BoundKit true :=
  ⟨1123,eb1123,indexOk1123.1,indexOk1123.2,lookup1123,rfl,threshold1123,
   n686,4690,pos686,cp686,ivec163,dvec163,dpos163,vp163,ivec211,dvec211,dpos211,vp211⟩

private def bk1124 : BoundKit true :=
  ⟨1124,eb1124,indexOk1124.1,indexOk1124.2,lookup1124,rfl,threshold1124,
   n685,178450,pos685,cp685,ivec145,dvec145,dpos145,vp145,ivec238,dvec238,dpos238,vp238⟩

private def bk1125 : BoundKit true :=
  ⟨1125,eb1125,indexOk1125.1,indexOk1125.2,lookup1125,rfl,threshold1125,
   n663,97513,pos663,cp663,ivec197,dvec197,dpos197,vp197,ivec210,dvec210,dpos210,vp210⟩

private def bk1127 : BoundKit true :=
  ⟨1127,eb1127,indexOk1127.1,indexOk1127.2,lookup1127,rfl,threshold1127,
   n664,777,pos664,cp664,ivec148,dvec148,dpos148,vp148,ivec211,dvec211,dpos211,vp211⟩

private def bk1131 : BoundKit true :=
  ⟨1131,eb1131,indexOk1131.1,indexOk1131.2,lookup1131,rfl,threshold1131,
   n665,76405,pos665,cp665,ivec141,dvec141,dpos141,vp141,ivec212,dvec212,dpos212,vp212⟩

private def bk1135 : BoundKit true :=
  ⟨1135,eb1135,indexOk1135.1,indexOk1135.2,lookup1135,rfl,threshold1135,
   n666,272875,pos666,cp666,ivec141,dvec141,dpos141,vp141,ivec212,dvec212,dpos212,vp212⟩

private def bk1136 : BoundKit true :=
  ⟨1136,eb1136,indexOk1136.1,indexOk1136.2,lookup1136,rfl,threshold1136,
   n667,185,pos667,cp667,ivec148,dvec148,dpos148,vp148,ivec213,dvec213,dpos213,vp213⟩

private def bk1141 : BoundKit false :=
  ⟨1141,eb1141,indexOk1141.1,indexOk1141.2,lookup1141,rfl,threshold1141,
   n668,65508114,pos668,cp668,ivec233,dvec233,dpos233,vp233,ivec134,dvec134,dpos134,vp134⟩

private def bk1142 : BoundKit false :=
  ⟨1142,eb1142,indexOk1142.1,indexOk1142.2,lookup1142,rfl,threshold1142,
   n673,91184291,pos673,cp673,ivec235,dvec235,dpos235,vp235,ivec206,dvec206,dpos206,vp206⟩

private def bk1143 : BoundKit false :=
  ⟨1143,eb1143,indexOk1143.1,indexOk1143.2,lookup1143,rfl,threshold1143,
   n671,1439634,pos671,cp671,ivec234,dvec234,dpos234,vp234,ivec139,dvec139,dpos139,vp139⟩

private def bk1144 : BoundKit false :=
  ⟨1144,eb1144,indexOk1144.1,indexOk1144.2,lookup1144,rfl,threshold1144,
   n679,73186666,pos679,cp679,ivec237,dvec237,dpos237,vp237,ivec181,dvec181,dpos181,vp181⟩

private def bk1146 : BoundKit false :=
  ⟨1146,eb1146,indexOk1146.1,indexOk1146.2,lookup1146,rfl,threshold1146,
   n676,431053012,pos676,cp676,ivec235,dvec235,dpos235,vp235,ivec207,dvec207,dpos207,vp207⟩

private def bk1148 : BoundKit false :=
  ⟨1148,eb1148,indexOk1148.1,indexOk1148.2,lookup1148,rfl,threshold1148,
   n677,676813533,pos677,cp677,ivec236,dvec236,dpos236,vp236,ivec206,dvec206,dpos206,vp206⟩

private def bk1157 : BoundKit false :=
  ⟨1157,eb1157,indexOk1157.1,indexOk1157.2,lookup1157,rfl,threshold1157,
   n681,9358302,pos681,cp681,ivec233,dvec233,dpos233,vp233,ivec134,dvec134,dpos134,vp134⟩

private def bk1160 : BoundKit true :=
  ⟨1160,eb1160,indexOk1160.1,indexOk1160.2,lookup1160,rfl,threshold1160,
   n682,3066986,pos682,cp682,ivec193,dvec193,dpos193,vp193,ivec210,dvec210,dpos210,vp210⟩

private def bk1164 : BoundKit true :=
  ⟨1164,eb1164,indexOk1164.1,indexOk1164.2,lookup1164,rfl,threshold1164,
   n687,18519877,pos687,cp687,ivec193,dvec193,dpos193,vp193,ivec239,dvec239,dpos239,vp239⟩

private def bk1169 : BoundKit true :=
  ⟨1169,eb1169,indexOk1169.1,indexOk1169.2,lookup1169,rfl,threshold1169,
   n689,47361431,pos689,cp689,ivec194,dvec194,dpos194,vp194,ivec210,dvec210,dpos210,vp210⟩

private def bk1174 : BoundKit false :=
  ⟨1174,eb1174,indexOk1174.1,indexOk1174.2,lookup1174,rfl,threshold1174,
   n146,3029375,pos146,cp146,ivec240,dvec240,dpos240,vp240,ivec241,dvec241,dpos241,vp241⟩

private def integerPair (l : BoundKit true) (u : BoundKit false) (qn qd : ℤ)
    (h : 0 < qn ∧ 0 < qd ∧ ∀ i j,
      qn * ((l.cd*(u.xd i*l.yd j)*(u.cd*(l.xd i*u.yd j))) * 10^30) <
        numerator (crossN l.cn (u.xn i) (l.yn j) u.cn (l.xn i) (u.yn j)
          l.cd (u.xd i) (l.yd j) u.cd (l.xd i) (u.yd j)) * qd) :
    {p : LowerEarlyTerminalPair // lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p} := by
  have hq : (0:ℚ) < (qn:ℚ)/qd := div_pos (by exact_mod_cast h.1) (by exact_mod_cast h.2.1)
  refine ⟨⟨l.id,u.id,(qn:ℚ)/qd⟩, ?_⟩
  apply explicit_pair_valid l.id u.id ((qn:ℚ)/qd) l.b u.b
  · exact l.idpos
  · exact l.idlen
  · exact u.idpos
  · exact u.idlen
  · exact l.lookup
  · exact u.lookup
  · exact l.orient
  · exact u.orient
  · exact l.thresholdValid
  · exact u.thresholdValid
  · intro i j
    unfold certCoefficientBoundValid
    refine ⟨le_of_lt hq, if_neg (ne_of_gt hq) ▸ ?_⟩
    rw [bernstein_factored]
    simp only [factoredCoefficients, earlyRect]
    rw [u.xscaled,l.yscaled,l.xscaled,u.yscaled,l.cscaled,u.cscaled]
    exact cross_scaled_all l.cn u.cn u.xn l.yn l.xn u.yn
      l.cd u.cd u.xd l.yd l.xd u.yd qn qd l.cdpos u.xdpos l.ydpos
      u.cdpos l.xdpos u.ydpos h.2.1 h.2.2 i j
  · exact Or.inl hq

private def zeroPair (l : BoundKit true) (u : BoundKit false)
    (heq : u.b.threshold = l.b.threshold) (hs : l.b.strict = true ∨ u.b.strict = true) :
    {p : LowerEarlyTerminalPair // lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p} := by
  refine ⟨⟨l.id,u.id,0⟩, ?_⟩
  apply explicit_pair_valid l.id u.id 0 l.b u.b
  · exact l.idpos
  · exact l.idlen
  · exact u.idpos
  · exact u.idlen
  · exact l.lookup
  · exact u.lookup
  · exact l.orient
  · exact u.orient
  · exact l.thresholdValid
  · exact u.thresholdValid
  · intro i j
    rw [heq]
    exact self_cross_coefficient_valid l.b.threshold earlyRect i j
  · exact Or.inr hs
private def pv001 := integerPair bk2 bk6 1209457821582646905920249162334217344661 2287549824000000000000000000000000000000 (by decide +kernel)
private def pv002 := integerPair bk13 bk6 217681969427389219945251575100867401818233 217999716725000000000000000000000000000000 (by decide +kernel)
private def pv003 := integerPair bk14 bk6 49780492297847917718747824217773595543257 73831499392000000000000000000000000000000 (by decide +kernel)
private def pv004 := integerPair bk2 bk8 1306140749652335656127702716380446531 3225216000000000000000000000000000000 (by decide +kernel)
private def pv005 := integerPair bk13 bk8 57485801500886445114772599032385203353 66274015546875000000000000000000000000 (by decide +kernel)
private def pv006 := integerPair bk14 bk8 325070305942570740561959304975416568219 598546336000000000000000000000000000000 (by decide +kernel)
private def pv007 := integerPair bk2 bk7 459114798895975670075916752288865492303 1675499584000000000000000000000000000000 (by decide +kernel)
private def pv008 := integerPair bk2 bk12 899705438055774599649980173037200697241 3960271744000000000000000000000000000000 (by decide +kernel)
private def pv009 := integerPair bk13 bk7 187192231991094112997583729392266216059427707 256404747702400000000000000000000000000000000 (by decide +kernel)
private def pv010 := integerPair bk14 bk15 52057232613753761924828675252043790033443 158209785728000000000000000000000000000000 (by decide +kernel)
private def pv011 := integerPair bk2 bk23 3123850090522287946077690438632370776441 11437749120000000000000000000000000000000 (by decide +kernel)
private def pv012 := integerPair bk13 bk23 22687006594991833973069827476185119771019 31142816675000000000000000000000000000000 (by decide +kernel)
private def pv013 := integerPair bk14 bk23 851304639586552319383475649570573526031 2109471411200000000000000000000000000000 (by decide +kernel)
private def pv014 := integerPair bk28 bk394 11911703752184106631583354131135001 1260032000000000000000000000000000 (by decide +kernel)
private def pv015 := integerPair bk33 bk394 32223464179004906256319240899945220702551 3644321408000000000000000000000000000000 (by decide +kernel)
private def pv016 := integerPair bk35 bk394 47285616985097842528471461144854658942369 2603086720000000000000000000000000000000 (by decide +kernel)
private def pv017 := integerPair bk36 bk394 382391860367772648552174805210138168197 30155008000000000000000000000000000000 (by decide +kernel)
private def pv018 := integerPair bk39 bk394 2114777850668898171539271069960867385647 257172531200000000000000000000000000000 (by decide +kernel)
private def pv019 := integerPair bk45 bk394 373244426005007739655412943223386811 43596800000000000000000000000000000 (by decide +kernel)
private def pv020 := integerPair bk2 bk50 64817465566250482179482166165647860599869 114478573440000000000000000000000000000000 (by decide +kernel)
private def pv021 := integerPair bk2 bk52 527763547021147601370692421703280961797 1081787520000000000000000000000000000000 (by decide +kernel)
private def pv022 := integerPair bk2 bk53 957308416286117144382899564997708849 2175945728000000000000000000000000000 (by decide +kernel)
private def pv023 := integerPair bk61 bk53 295863255533906645909906438797393772643 598546336000000000000000000000000000000 (by decide +kernel)
private def pv024 := integerPair bk2 bk51 537889672306650460020910744424434183839 1675499584000000000000000000000000000000 (by decide +kernel)
private def pv025 := integerPair bk2 bk60 2560119705867331692267093225229511665733 7433673600000000000000000000000000000000 (by decide +kernel)
private def pv026 := integerPair bk61 bk51 45446251399094304390565755391507930103781 123350002432000000000000000000000000000000 (by decide +kernel)
private def pv027 := integerPair bk2 bk66 1095931858788215575923148148749164771617 3960271744000000000000000000000000000000 (by decide +kernel)
private def pv028 := integerPair bk61 bk66 1031139205597574355579834316801194276188471 3207100063232000000000000000000000000000000 (by decide +kernel)
private def pv029 := integerPair bk69 bk50 358564554452398437040104969806636014555969 366239524098000000000000000000000000000000 (by decide +kernel)
private def pv030 := integerPair bk69 bk52 5172947512441969181354114062527004349261 5768085890000000000000000000000000000000 (by decide +kernel)
private def pv031 := integerPair bk69 bk51 568259004161396538531092106534831072337824857 789029310460160000000000000000000000000000000 (by decide +kernel)
private def pv032 := integerPair bk69 bk60 139275821228662479247976257153957347085297 186856900050000000000000000000000000000000 (by decide +kernel)
private def pv033 := integerPair bk70 bk50 1987268221469226341780067589545978824581 2827691330000000000000000000000000000000 (by decide +kernel)
private def pv034 := integerPair bk70 bk52 69628207089541432126016657409435389863 112227438000000000000000000000000000000 (by decide +kernel)
private def pv035 := integerPair bk70 bk71 1528779807464963898774769945962350229086189 4139093854464000000000000000000000000000000 (by decide +kernel)
private def pv036 := integerPair bk70 bk60 1327099385647560259412528608232799719773 2827691330000000000000000000000000000000 (by decide +kernel)
private def pv037 := integerPair bk76 bk394 698430061541908628949985426056766703 81902080000000000000000000000000000 (by decide +kernel)
private def pv038 := integerPair bk84 bk394 64847603552762168349450748270981683627477 7288642816000000000000000000000000000000 (by decide +kernel)
private def pv039 := integerPair bk86 bk394 19026435848569796645696019069847411228011 1041234688000000000000000000000000000000 (by decide +kernel)
private def pv040 := integerPair bk87 bk394 25652076118795114283999783240138061417 1884688000000000000000000000000000000 (by decide +kernel)
private def pv041 := integerPair bk90 bk394 234567853852401965952080084149532424481 32146566400000000000000000000000000000 (by decide +kernel)
private def pv042 := integerPair bk96 bk394 7736471602930154965352391278140937709 1002726400000000000000000000000000000 (by decide +kernel)
private def pv043 := integerPair bk100 bk394 21974921026368738617299273597211984877 1884688000000000000000000000000000000 (by decide +kernel)
private def pv044 := integerPair bk2 bk101 152311140967011396712778429291908213 504292250000000000000000000000000000 (by decide +kernel)
private def pv045 := integerPair bk27 bk101 6226054828392094167121413117639505447 3586483200000000000000000000000000000 (by decide +kernel)
private def pv046 := integerPair bk105 bk101 3811883459046190038496238477331969143 1151317146000000000000000000000000000 (by decide +kernel)
private def pv047 := integerPair bk107 bk101 17769266588696014225420252595118608147 2569904343750000000000000000000000000 (by decide +kernel)
private def pv048 := integerPair bk43 bk101 255005479281491536373477160223865831 49033950000000000000000000000000000 (by decide +kernel)
private def pv049 := integerPair bk2 bk102 53249158019166184458159817310862257 469200000000000000000000000000000000 (by decide +kernel)
private def pv050 := integerPair bk27 bk102 1583677895264646568630828006979671 1045500000000000000000000000000000 (by decide +kernel)
private def pv051 := integerPair bk105 bk102 26327778229447433955931396530607898533 8591919000000000000000000000000000000 (by decide +kernel)
private def pv052 := integerPair bk107 bk102 40548882289206331714116247606358816507 6137085000000000000000000000000000000 (by decide +kernel)
private def pv053 := integerPair bk43 bk102 10290151143953854833550864001845663 2091000000000000000000000000000000 (by decide +kernel)
private def pv054 := integerPair bk114 bk103 2038542672924758021461571706802347036007 12282830208000000000000000000000000000000 (by decide +kernel)
private def pv055 := integerPair bk27 bk103 1944107490506032425162188429511025873949 1252726464000000000000000000000000000000 (by decide +kernel)
private def pv056 := integerPair bk105 bk106 13472692885803468922489022865521484639128547 4211800474112000000000000000000000000000000 (by decide +kernel)
private def pv057 := integerPair bk107 bk103 1096653005464994543405003177834109287305181 157294210560000000000000000000000000000000 (by decide +kernel)
private def pv058 := integerPair bk43 bk109 936816777912990725392133646031408326234389 181409316352000000000000000000000000000000 (by decide +kernel)
private def pv059 := integerPair bk2 bk116 1328438747018175068116121781213905177 179132096000000000000000000000000000000 (by decide +kernel)
private def pv060 := integerPair bk27 bk116 19354205679677521760635783676594502062551 13028355225600000000000000000000000000000 (by decide +kernel)
private def pv061 := integerPair bk105 bk118 36684723877600487065815635513529966880591691 11732872749312000000000000000000000000000000 (by decide +kernel)
private def pv062 := integerPair bk107 bk116 1760222851854582557030229862647587660042119 255603092160000000000000000000000000000000 (by decide +kernel)
private def pv063 := integerPair bk43 bk119 345907208058048909093201313267755948690407 68028493632000000000000000000000000000000 (by decide +kernel)
private def pv064 := integerPair bk120 bk121 145915202785250702935445244691475942549137909 91162579527577600000000000000000000000000000 (by decide +kernel)
private def pv065 := integerPair bk122 bk394 1714600599874020630555227200663988047107 1250231690240000000000000000000000000000 (by decide +kernel)
private def pv066 := integerPair bk120 bk394 15320901175072596684650231896189988949 10858924960000000000000000000000000000 (by decide +kernel)
private def pv067 := integerPair bk125 bk394 68183522768268292896604909492307918878221 48924023782400000000000000000000000000000 (by decide +kernel)
private def pv068 := integerPair bk127 bk121 3736460859950888046140249576588588896499537 4189954798848000000000000000000000000000000 (by decide +kernel)
private def pv069 := integerPair bk129 bk121 275265076665448628061398533329724302577 328325864720000000000000000000000000000 (by decide +kernel)
private def pv070 := integerPair bk131 bk121 13627897805461138967602167648214961051171 5862961870000000000000000000000000000000 (by decide +kernel)
private def pv071 := integerPair bk75 bk121 352448293567890550127898356705469431749 237714638000000000000000000000000000000 (by decide +kernel)
private def pv072 := integerPair bk134 bk394 32875018879616735128118609954326492711 64293132800000000000000000000000000000 (by decide +kernel)
private def pv073 := integerPair bk129 bk394 2377258434350213563482900201637004527851 3644321408000000000000000000000000000000 (by decide +kernel)
private def pv074 := integerPair bk131 bk394 26833799719908647602441873986454418877 12697984000000000000000000000000000000 (by decide +kernel)
private def pv075 := integerPair bk75 bk394 38742049611434667241312818947897121531 30155008000000000000000000000000000000 (by decide +kernel)
private def pv076 := integerPair bk127 bk394 46117564068791907099888590541019779 65521664000000000000000000000000000 (by decide +kernel)
private def pv077 := integerPair bk137 bk394 569447649446832094845531114610445737 1002726400000000000000000000000000000 (by decide +kernel)
private def pv078 := integerPair bk27 bk394 45168948793056991298132344235453059323 30155008000000000000000000000000000000 (by decide +kernel)
private def pv079 := integerPair bk140 bk394 144189478952116695062206788409730295307 413712332800000000000000000000000000000 (by decide +kernel)
private def pv080 := integerPair bk144 bk394 20091269943273150176634489410440574011 88111504000000000000000000000000000000 (by decide +kernel)
private def pv081 := integerPair bk146 bk394 29288215614389280927642881416493770181 36774400000000000000000000000000000000 (by decide +kernel)
private def pv082 := integerPair bk147 bk394 154661198486150851535870940631700191 432640000000000000000000000000000000 (by decide +kernel)
private def pv083 := integerPair bk150 bk394 5051658913607386026398306599434988948161 7377680128000000000000000000000000000000 (by decide +kernel)
private def pv084 := integerPair bk154 bk394 11520394026484950287304913810034239889187 5269771520000000000000000000000000000000 (by decide +kernel)
private def pv085 := integerPair bk159 bk162 1195072700540155739366864366533722003186567 2551460800000000000000000000000000000000000 (by decide +kernel)
private def pv086 := integerPair bk172 bk162 1312190002957914426042761225816205165598631 1364310536750000000000000000000000000000000 (by decide +kernel)
private def pv087 := integerPair bk173 bk162 974091930427445604930285375407711835827 1404999890000000000000000000000000000000 (by decide +kernel)
private def pv088 := integerPair bk159 bk164 22582643275733853267079013008937695054791 58082675200000000000000000000000000000000 (by decide +kernel)
private def pv089 := integerPair bk172 bk164 12438563802400892832525632584574676656611 14117190110000000000000000000000000000000 (by decide +kernel)
private def pv090 := integerPair bk173 bk164 311773624870173313640598102070902955541 508837798000000000000000000000000000000 (by decide +kernel)
private def pv091 := integerPair bk159 bk165 319335238042124663673178077205982287347843 959121856000000000000000000000000000000000 (by decide +kernel)
private def pv092 := integerPair bk159 bk163 5491214177342897585064030293379431313668769 24373117120000000000000000000000000000000000 (by decide +kernel)
private def pv093 := integerPair bk159 bk171 9000338175511769155884723135146309699747913 48746234240000000000000000000000000000000000 (by decide +kernel)
private def pv094 := integerPair bk172 bk163 152211688830201121303992634283177561129291343 212315024669440000000000000000000000000000000 (by decide +kernel)
private def pv095 := integerPair bk173 bk174 15210079448150741795933580611056439781705513 40228182717184000000000000000000000000000000 (by decide +kernel)
private def pv096 := integerPair bk159 bk183 97470183247748965493396724481579040942481 364494400000000000000000000000000000000000 (by decide +kernel)
private def pv097 := integerPair bk172 bk183 147899008391949096244009116745692496499513 194901505250000000000000000000000000000000 (by decide +kernel)
private def pv098 := integerPair bk173 bk183 3443508125542426257309692166986418557767 7024999450000000000000000000000000000000 (by decide +kernel)
private def pv099 := integerPair bk186 bk165 338906656796827992004159751563750660017 815876384000000000000000000000000000000 (by decide +kernel)
private def pv100 := integerPair bk186 bk163 142572064924050255642897436706070978936933 464418668032000000000000000000000000000000 (by decide +kernel)
private def pv101 := integerPair bk186 bk171 803305456294394061490517788564843295941707 3018721342208000000000000000000000000000000 (by decide +kernel)
private def pv102 := integerPair bk188 bk160 7736841817937872472827775881903548789 1010639872000000000000000000000000000 (by decide +kernel)
private def pv103 := integerPair bk193 bk160 77850102976978717204361152886130391892131 11900284492800000000000000000000000000000 (by decide +kernel)
private def pv104 := integerPair bk197 bk160 7887620494013481924226672320742155083959 1131794892800000000000000000000000000000 (by decide +kernel)
private def pv105 := integerPair bk199 bk160 109676923404048309216589018938610981691 10654336000000000000000000000000000000 (by decide +kernel)
private def pv106 := integerPair bk203 bk160 3701908317062253338467008807620491134821 429709772800000000000000000000000000000 (by decide +kernel)
private def pv107 := integerPair bk207 bk160 5412159120001660657169767786478788132303 306935552000000000000000000000000000000 (by decide +kernel)
private def pv108 := integerPair bk208 bk160 37775780082389426354985440982683406899 3044096000000000000000000000000000000 (by decide +kernel)
private def pv109 := integerPair bk159 bk214 119412788636321825286465699898669117036715981 260776686016000000000000000000000000000000000 (by decide +kernel)
private def pv110 := integerPair bk159 bk216 349241005444870000545578629104750619696243 959121856000000000000000000000000000000000 (by decide +kernel)
private def pv111 := integerPair bk159 bk215 6486107282498058069657145876844210592416769 24373117120000000000000000000000000000000000 (by decide +kernel)
private def pv112 := integerPair bk159 bk223 9137101822933757831045229865336483242326843 37253812288000000000000000000000000000000000 (by decide +kernel)
private def pv113 := integerPair bk159 bk226 11097324132911645130630675168349309926870913 48746234240000000000000000000000000000000000 (by decide +kernel)
private def pv114 := integerPair bk229 bk214 664289964231273646074521033431392280377009 955017375725000000000000000000000000000000 (by decide +kernel)
private def pv115 := integerPair bk229 bk216 264006231826498969646039277108464038447 439062465625000000000000000000000000000 (by decide +kernel)
private def pv116 := integerPair bk229 bk215 4589099547543720021885854946894933350049297 9140154636800000000000000000000000000000000 (by decide +kernel)
private def pv117 := integerPair bk229 bk223 46909624782964612749723041783255182871097 97450752625000000000000000000000000000000 (by decide +kernel)
private def pv118 := integerPair bk230 bk214 419128289434479690188273169563503375041261 887318074496000000000000000000000000000000 (by decide +kernel)
private def pv119 := integerPair bk230 bk216 308456432251724475472440151849173251337 815876384000000000000000000000000000000 (by decide +kernel)
private def pv120 := integerPair bk230 bk231 1560445416121004838705831708433011204328507 6982023026176000000000000000000000000000000 (by decide +kernel)
private def pv121 := integerPair bk230 bk223 6554790699295400976504925362675234212931 25351944985600000000000000000000000000000 (by decide +kernel)
private def pv122 := integerPair bk236 bk160 522975598024617276188949539358024430031 75797990400000000000000000000000000000 (by decide +kernel)
private def pv123 := integerPair bk241 bk160 1481870228126634657948395299372614415519 247922593600000000000000000000000000000 (by decide +kernel)
private def pv124 := integerPair bk245 bk160 58692703709711697244660012145863258607 9353676800000000000000000000000000000 (by decide +kernel)
private def pv125 := integerPair bk247 bk160 3205645590754183539506851422006882632693 460403328000000000000000000000000000000 (by decide +kernel)
private def pv126 := integerPair bk251 bk160 33136482860249793562036809854242868174653 2302016640000000000000000000000000000000 (by decide +kernel)
private def pv127 := integerPair bk252 bk160 60475372859363248998847747269352258873 6392601600000000000000000000000000000 (by decide +kernel)
private def pv128 := integerPair bk159 bk258 214653418181906405930569220567290942638870667 350912368576000000000000000000000000000000000 (by decide +kernel)
private def pv129 := integerPair bk159 bk260 1948688716740471790454896487310165920651807 3289443520000000000000000000000000000000000 (by decide +kernel)
private def pv130 := integerPair bk159 bk261 872002685869305830995063980405468618747617 1503882688000000000000000000000000000000000 (by decide +kernel)
private def pv131 := integerPair bk159 bk259 3218723410823115222549397171990579425683111 6043331440000000000000000000000000000000000 (by decide +kernel)
private def pv132 := integerPair bk159 bk268 27372531827695242313932113490355589118845581 50130338368000000000000000000000000000000000 (by decide +kernel)
private def pv133 := integerPair bk272 bk160 1813998804064642196898238605230399460563 1050481907200000000000000000000000000000 (by decide +kernel)
private def pv134 := integerPair bk280 bk160 405767836056727573149552833106464806813 227882362400000000000000000000000000000 (by decide +kernel)
private def pv135 := integerPair bk282 bk160 193019518596052248666557311080427021920413 45576472480000000000000000000000000000000 (by decide +kernel)
private def pv136 := integerPair bk283 bk160 282435831111733735238705832476000356319 93871500800000000000000000000000000000 (by decide +kernel)
private def pv137 := integerPair bk286 bk160 231353442129951484237729008621960193965129 164925659430400000000000000000000000000000 (by decide +kernel)
private def pv138 := integerPair bk292 bk160 4039278875927407747341622232517038009701 2676092467200000000000000000000000000000 (by decide +kernel)
private def pv139 := integerPair bk296 bk160 35231675427313845207398419746561579101 13410214400000000000000000000000000000 (by decide +kernel)
private def pv140 := integerPair bk159 bk298 37654255802322090889827475324694067458669683 58618998592000000000000000000000000000000000 (by decide +kernel)
private def pv141 := integerPair bk159 bk300 19241654821675907970577672301876645910982549 30497044160000000000000000000000000000000000 (by decide +kernel)
private def pv142 := integerPair bk159 bk301 5201264236027604262404735031150412994555327 8316172480000000000000000000000000000000000 (by decide +kernel)
private def pv143 := integerPair bk159 bk299 244278452719174892899804883331092374012203641 408812910880000000000000000000000000000000000 (by decide +kernel)
private def pv144 := integerPair bk159 bk308 5061730941489145114096369374091699750356469 8374142656000000000000000000000000000000000 (by decide +kernel)
private def pv145 := integerPair bk312 bk160 115474712964775669354243752512721527517 219803161600000000000000000000000000000 (by decide +kernel)
private def pv146 := integerPair bk318 bk160 16796470167354382149785205563467348026937 26599802275200000000000000000000000000000 (by decide +kernel)
private def pv147 := integerPair bk320 bk160 377140248008706033460200361698475410343223 189998587680000000000000000000000000000000 (by decide +kernel)
private def pv148 := integerPair bk321 bk160 91291808572397568972860468440068691939 65771904000000000000000000000000000000 (by decide +kernel)
private def pv149 := integerPair bk324 bk160 67312276340670840680346712853007466091 57550416000000000000000000000000000000 (by decide +kernel)
private def pv150 := integerPair bk159 bk6 10919236799022995967829683986249964843568493 25710070848000000000000000000000000000000000 (by decide +kernel)
private def pv151 := integerPair bk159 bk8 49819508330705057291782225819773779163527 166743667200000000000000000000000000000000 (by decide +kernel)
private def pv152 := integerPair bk159 bk7 1477573793209915746398084997860083413865353 8948690960000000000000000000000000000000000 (by decide +kernel)
private def pv153 := integerPair bk159 bk12 382068424288703913276293865200651936110617 3254069440000000000000000000000000000000000 (by decide +kernel)
private def pv154 := integerPair bk159 bk23 4225812047315686498804188159192408862019693 25710070848000000000000000000000000000000000 (by decide +kernel)
private def pv155 := integerPair bk28 bk160 18135501372511039357920826633201749427 1992425600000000000000000000000000000 (by decide +kernel)
private def pv156 := integerPair bk33 bk160 92921679829765583205573736370556349366041 10911400192000000000000000000000000000000 (by decide +kernel)
private def pv157 := integerPair bk35 bk160 12365031308843348385692052521868317544417 708532480000000000000000000000000000000 (by decide +kernel)
private def pv158 := integerPair bk36 bk160 550543060747475404645875246895338267521 45143296000000000000000000000000000000 (by decide +kernel)
private def pv159 := integerPair bk39 bk160 594820131273546801135029839897568488321 75074596608000000000000000000000000000 (by decide +kernel)
private def pv160 := integerPair bk45 bk160 482814991711033398386248328002089793387 58543795200000000000000000000000000000 (by decide +kernel)
private def pv161 := integerPair bk159 bk50 2576398494475188294874344939299895506928213 5569868480000000000000000000000000000000000 (by decide +kernel)
private def pv162 := integerPair bk159 bk52 5639678085998441749307074542652108969267 14737395200000000000000000000000000000000 (by decide +kernel)
private def pv163 := integerPair bk159 bk53 18586430919034605287024650768909630314669 55581222400000000000000000000000000000000 (by decide +kernel)
private def pv164 := integerPair bk159 bk51 1906116924974064710346666164902715258044353 8948690960000000000000000000000000000000000 (by decide +kernel)
private def pv165 := integerPair bk159 bk60 1318044544473708059374273779532770815199573 5569868480000000000000000000000000000000000 (by decide +kernel)
private def pv166 := integerPair bk159 bk66 546297841096147961350285093333877850413617 3254069440000000000000000000000000000000000 (by decide +kernel)
private def pv167 := integerPair bk76 bk160 49102352036410939830109164061503792073 5977276800000000000000000000000000000 (by decide +kernel)
private def pv168 := integerPair bk84 bk160 4674828761935721940278928889592435843937 545570009600000000000000000000000000000 (by decide +kernel)
private def pv169 := integerPair bk86 bk160 34205049492451307520654838932590060013873 1948464320000000000000000000000000000000 (by decide +kernel)
private def pv170 := integerPair bk87 bk160 59077726520415422973695424108318145429 4514329600000000000000000000000000000 (by decide +kernel)
private def pv171 := integerPair bk90 bk160 8802742303308578075033904648341637426973 1251243276800000000000000000000000000000 (by decide +kernel)
private def pv172 := integerPair bk96 bk160 145118111160555255726444883942746651993 19514598400000000000000000000000000000 (by decide +kernel)
private def pv173 := integerPair bk100 bk160 3164753601515603244831416078384902483 282145600000000000000000000000000000 (by decide +kernel)
private def pv174 := integerPair bk159 bk101 481921983340208475355761681879533788487 2362483200000000000000000000000000000000 (by decide +kernel)
private def pv175 := integerPair bk327 bk101 131290037817350413810583253170255267507 149229346560000000000000000000000000000 (by decide +kernel)
private def pv176 := integerPair bk329 bk101 227935903845502950811284139396077510781 106592390400000000000000000000000000000 (by decide +kernel)
private def pv177 := integerPair bk187 bk101 20505001002090315732355272454189726709 14389670400000000000000000000000000000 (by decide +kernel)
private def pv178 := integerPair bk159 bk332 24012526930263774806333347309865936983252423 217960416960000000000000000000000000000000000 (by decide +kernel)
private def pv179 := integerPair bk327 bk333 488418866013204062586733884136233160012455347 606174438975705600000000000000000000000000000 (by decide +kernel)
private def pv180 := integerPair bk329 bk332 53551366598631747878564808471968360401475249 25405898519040000000000000000000000000000000 (by decide +kernel)
private def pv181 := integerPair bk187 bk334 7702976383615803215895998135148720073723 5648349907200000000000000000000000000000 (by decide +kernel)
private def pv182 := integerPair bk114 bk325 1963715357766780984647038540969215350879 5540624496000000000000000000000000000000 (by decide +kernel)
private def pv183 := integerPair bk327 bk328 44848864124411142489886522272690736459107951 52329460553216000000000000000000000000000000 (by decide +kernel)
private def pv184 := integerPair bk329 bk325 2900480177085635213839789404103644115130473 1343581171680000000000000000000000000000000 (by decide +kernel)
private def pv185 := integerPair bk187 bk331 9841310589930017498085695221653253345333 6951815270400000000000000000000000000000 (by decide +kernel)
private def pv186 := integerPair bk115 bk335 275663466066885608290004305676068909693 3440148940800000000000000000000000000000 (by decide +kernel)
private def pv187 := integerPair bk327 bk336 634286192059742293516965608764472392278217 797206625615400000000000000000000000000000 (by decide +kernel)
private def pv188 := integerPair bk329 bk335 18277838481461452102552684680145574179573181 8733277615920000000000000000000000000000000 (by decide +kernel)
private def pv189 := integerPair bk187 bk337 1958269218652669035410491629021781988571 1448294848000000000000000000000000000000 (by decide +kernel)
private def pv190 := integerPair bk338 bk160 598435684646666924259437089824963988011 632019097600000000000000000000000000000 (by decide +kernel)
private def pv191 := integerPair bk340 bk160 98012705810341932429181028970519990643887 106876384102400000000000000000000000000000 (by decide +kernel)
private def pv192 := integerPair bk342 bk160 1130761562644304747012993516362023653789 575504160000000000000000000000000000000 (by decide +kernel)
private def pv193 := integerPair bk187 bk160 790158117250703298807259681465699727 680064000000000000000000000000000000 (by decide +kernel)
private def pv194 := integerPair bk345 bk346 53352825819138616733228874710181784875231 67234078288000000000000000000000000000000 (by decide +kernel)
private def pv195 := integerPair bk347 bk217 559405767643059802270548161034937097447 1229744998400000000000000000000000000000 (by decide +kernel)
private def pv196 := integerPair bk345 bk160 607585048543346748664523130113769271 1184343600000000000000000000000000000 (by decide +kernel)
private def pv197 := integerPair bk350 bk160 461635457818133060615832115471457839631 1131794892800000000000000000000000000000 (by decide +kernel)
private def pv198 := integerPair bk235 bk160 10524812478024601595701536986576538207 10654336000000000000000000000000000000 (by decide +kernel)
private def pv199 := integerPair bk341 bk346 248813537942743282702757170880401281591 274874795300000000000000000000000000000 (by decide +kernel)
private def pv200 := integerPair bk341 bk217 2749157011966788847882708509239677496551 3734786944000000000000000000000000000000 (by decide +kernel)
private def pv201 := integerPair bk341 bk160 1429535805978787812848116401465491839 2302016640000000000000000000000000000 (by decide +kernel)
private def pv202 := integerPair bk342 bk346 3132142157270103011295357046764007901853 1374373976500000000000000000000000000000 (by decide +kernel)
private def pv203 := integerPair bk342 bk217 1127010435196482441249720019867777002757 533540992000000000000000000000000000000 (by decide +kernel)
private def pv204 := integerPair bk187 bk346 69503670610859459240082374205640910713 47707220750000000000000000000000000000 (by decide +kernel)
private def pv205 := integerPair bk187 bk217 2612212955445391300140412654067879601 2025653000000000000000000000000000000 (by decide +kernel)
private def pv206 := integerPair bk358 bk359 175968531956855849091391275032994527298355801 279837091066624000000000000000000000000000000 (by decide +kernel)
private def pv207 := integerPair bk360 bk257 4051733604621854660147607503330634130610599 12429870482176000000000000000000000000000000 (by decide +kernel)
private def pv208 := integerPair bk358 bk160 35358382625337198240160784830229507051 138201958400000000000000000000000000000 (by decide +kernel)
private def pv209 := integerPair bk363 bk160 16479101046201360510435701211923150977 101709335552000000000000000000000000000 (by decide +kernel)
private def pv210 := integerPair bk235 bk359 130922825551274747681070218424470732605909 94827885824000000000000000000000000000000 (by decide +kernel)
private def pv211 := integerPair bk235 bk257 427298724710469244404092967598896656571 348771584000000000000000000000000000000 (by decide +kernel)
private def pv212 := integerPair bk366 bk359 2942617944662862507735147313715500286797 1067128967800000000000000000000000000000 (by decide +kernel)
private def pv213 := integerPair bk366 bk257 357494266446632964513618659531981155209 137369393000000000000000000000000000000 (by decide +kernel)
private def pv214 := integerPair bk366 bk160 299691182565519628938017457006813165443 128912931840000000000000000000000000000 (by decide +kernel)
private def pv215 := integerPair bk370 bk359 155326162140796829688983784451751948278009 26678224195000000000000000000000000000000 (by decide +kernel)
private def pv216 := integerPair bk370 bk257 13568592599481574780276451075678116287 2393195000000000000000000000000000000 (by decide +kernel)
private def pv217 := integerPair bk370 bk160 12210347460651981887700276913814214867157 2302016640000000000000000000000000000000 (by decide +kernel)
private def pv218 := integerPair bk243 bk359 1537342964226257845735994631264379282551 370421429000000000000000000000000000000 (by decide +kernel)
private def pv219 := integerPair bk243 bk257 5445543750247857856266629978278308301 1362389000000000000000000000000000000 (by decide +kernel)
private def pv220 := integerPair bk243 bk160 117636995297193417889976482187818588249 31963008000000000000000000000000000000 (by decide +kernel)
private def pv221 := integerPair bk159 bk375 32236648001341873125069428467071548434073383 72474823590400000000000000000000000000000000 (by decide +kernel)
private def pv222 := integerPair bk159 bk297 10883630054270585285673457449457519142767 31360806400000000000000000000000000000000 (by decide +kernel)
private def pv223 := integerPair bk159 bk376 20356711060244134113575650120609057800569581 83808677920000000000000000000000000000000000 (by decide +kernel)
private def pv224 := integerPair bk159 bk380 2253032980929482582228583926623548541015633 10353546227200000000000000000000000000000000 (by decide +kernel)
private def pv225 := integerPair bk159 bk382 3876381216510852862777087853206878825668636393 66271752238208000000000000000000000000000000000 (by decide +kernel)
private def pv226 := integerPair bk27 bk382 919165473646159447329232076910359285557385983 536070537447168000000000000000000000000000000 (by decide +kernel)
private def pv227 := integerPair bk105 bk383 6095731892042453804072893972404411144942515222743 1786050383294683968000000000000000000000000000000 (by decide +kernel)
private def pv228 := integerPair bk107 bk382 491821374399870080612053563649734843406594943 67065943197248000000000000000000000000000000 (by decide +kernel)
private def pv229 := integerPair bk43 bk384 52223514044800123263322436698157881966956640413 9703653641616128000000000000000000000000000000 (by decide +kernel)
private def pv230 := integerPair bk385 bk375 197237835536770533863530826386787276099331 136124596785479680000000000000000000000000 (by decide +kernel)
private def pv231 := integerPair bk386 bk297 8443624928977740583229675952286114590144539 6534540223232000000000000000000000000000000 (by decide +kernel)
private def pv232 := integerPair bk385 bk121 6843047379045464266990107468411513934985799 6623585178112000000000000000000000000000000 (by decide +kernel)
private def pv233 := integerPair bk387 bk380 669817724569692923072871898405152178268625151 556411089315648000000000000000000000000000000 (by decide +kernel)
private def pv234 := integerPair bk388 bk375 2697089607649154226616397141331924159454328581 1999330015286732800000000000000000000000000000 (by decide +kernel)
private def pv235 := integerPair bk389 bk297 1705189749967807147966184763629452007784041319 1422689053108736000000000000000000000000000000 (by decide +kernel)
private def pv236 := integerPair bk388 bk160 17403481283442431324909320023214703397553 23093425484800000000000000000000000000000 (by decide +kernel)
private def pv237 := integerPair bk390 bk380 16506021015361184306948761453076025559027682039 14943612113048832000000000000000000000000000000 (by decide +kernel)
private def pv238 := integerPair bk385 bk160 731308187967705925766397624934153692577 859861587200000000000000000000000000000 (by decide +kernel)
private def pv239 := integerPair bk391 bk375 1662777644102366488881541509130953887193913239 1197848744493721600000000000000000000000000000 (by decide +kernel)
private def pv240 := integerPair bk392 bk297 35461510680622731262304864792894239347583 28750831910920000000000000000000000000000 (by decide +kernel)
private def pv241 := integerPair bk391 bk160 60624243593686624816611613688408613491 76562017280000000000000000000000000000 (by decide +kernel)
private def pv242 := integerPair bk393 bk380 28656560069170760571862422545906445318703767133 25068659620307251200000000000000000000000000000 (by decide +kernel)
private def pv243 := integerPair bk27 bk375 164179549618459467793307129414236596228189 78166270085120000000000000000000000000000 (by decide +kernel)
private def pv244 := integerPair bk27 bk297 13211646053922100136210336644630753563 6606166000000000000000000000000000000 (by decide +kernel)
private def pv245 := integerPair bk27 bk160 3031365416296433020026677472745230079 2051968000000000000000000000000000000 (by decide +kernel)
private def pv246 := integerPair bk27 bk380 2603256437968314783887678943369804660518727 1395826251520000000000000000000000000000000 (by decide +kernel)
private def pv247 := integerPair bk134 bk160 43391703357186328608658183297807257721 81602822400000000000000000000000000000 (by decide +kernel)
private def pv248 := integerPair bk129 bk160 1818504668113322319555338197359252141669 2727850048000000000000000000000000000000 (by decide +kernel)
private def pv249 := integerPair bk131 bk160 87546841179563156219126308298828097573 42357920000000000000000000000000000000 (by decide +kernel)
private def pv250 := integerPair bk75 bk160 28734308856856968587082945002744737321 22571648000000000000000000000000000000 (by decide +kernel)
private def pv251 := integerPair bk127 bk160 80024277352614545999423806868062079 111724800000000000000000000000000000 (by decide +kernel)
private def pv252 := integerPair bk137 bk160 6860621787114101020926805297518600787 11708759040000000000000000000000000000 (by decide +kernel)
private def pv253 := integerPair bk140 bk160 16401477768840693802526844212418028741 43758035200000000000000000000000000000 (by decide +kernel)
private def pv254 := integerPair bk144 bk160 287047033684413952538572199646366800559 1097462671360000000000000000000000000000 (by decide +kernel)
private def pv255 := integerPair bk146 bk160 16578873546117123136375184413570258361 20644800000000000000000000000000000000 (by decide +kernel)
private def pv256 := integerPair bk147 bk160 62128585459626643606179228572368253 161920000000000000000000000000000000 (by decide +kernel)
private def pv257 := integerPair bk150 bk160 38555160767452705209145700500411356279 55223463680000000000000000000000000000 (by decide +kernel)
private def pv258 := integerPair bk154 bk160 263441310115719448811019883956251807697 123266660000000000000000000000000000000 (by decide +kernel)
private def pv259 := integerPair bk1 bk396 9764915443948463846163037737960970385564233 120358429734400000000000000000000000000000000 (by decide +kernel)
private def pv260 := integerPair bk110 bk397 5976400019746738272944261316844779819081599 97583213038080000000000000000000000000000000 (by decide +kernel)
private def pv261 := integerPair bk114 bk396 21601233843475959636881967060213548951009 44025676288000000000000000000000000000000 (by decide +kernel)
private def pv262 := integerPair bk115 bk398 561966350695440885387746035292019331480031 2575502062848000000000000000000000000000000 (by decide +kernel)
private def pv263 := integerPair bk399 bk395 155857192110745846033873967819634036469970977 305237461760000000000000000000000000000000000 (by decide +kernel)
private def pv264 := integerPair bk402 bk395 65713379130425335760655020093314956971940133 130816055040000000000000000000000000000000000 (by decide +kernel)
private def pv265 := integerPair bk404 bk395 21294152706315170645783604086153471176379 25600185600000000000000000000000000000000 (by decide +kernel)
private def pv266 := integerPair bk406 bk395 3235337403213848814004149922002221741419605121 6432122238080000000000000000000000000000000000 (by decide +kernel)
private def pv267 := integerPair bk408 bk395 855759040022312820947025288018884554046051451 7098829886720000000000000000000000000000000000 (by decide +kernel)
private def pv268 := integerPair bk403 bk395 32648892910094380212277856438801764017673 333335750000000000000000000000000000000000 (by decide +kernel)
private def pv269 := integerPair bk405 bk395 1086527588814037462192742197223549882233 2481600000000000000000000000000000000000 (by decide +kernel)
private def pv270 := integerPair bk411 bk412 1534315512742732309424587027308166135643 1781861120000000000000000000000000000000 (by decide +kernel)
private def pv271 := integerPair bk411 bk414 1371556466158490560455025586040708673739347 1859096938400000000000000000000000000000000 (by decide +kernel)
private def pv272 := integerPair bk416 bk412 633868323057878000903707418017191019415289 909194636480000000000000000000000000000000 (by decide +kernel)
private def pv273 := integerPair bk416 bk395 2240792483390825253805106924557203524743976357 4253878977920000000000000000000000000000000000 (by decide +kernel)
private def pv274 := integerPair bk411 bk395 18768211691976905288821328923009334514710601 27094770560000000000000000000000000000000000 (by decide +kernel)
private def pv275 := integerPair bk420 bk412 2073134310733409995305955312520934874131121 2799303819520000000000000000000000000000000 (by decide +kernel)
private def pv276 := integerPair bk420 bk395 48593207047491248126939487776046892993627714723 85131769099520000000000000000000000000000000000 (by decide +kernel)
private def pv277 := integerPair bk1 bk422 11694986244500608106288658694060764642359 47642365056000000000000000000000000000000 (by decide +kernel)
private def pv278 := integerPair bk424 bk425 1566015154507509749766564957123824382353765959 3036024057228288000000000000000000000000000000 (by decide +kernel)
private def pv279 := integerPair bk426 bk422 5644735117210944488882881870388036987436521 4756240584192000000000000000000000000000000 (by decide +kernel)
private def pv280 := integerPair bk419 bk427 11229386976350695945553175111410636032843 15636567797760000000000000000000000000000 (by decide +kernel)
private def pv281 := integerPair bk415 bk422 5812503509292291281261750387249409117607 18879258880000000000000000000000000000000 (by decide +kernel)
private def pv282 := integerPair bk431 bk432 5195951809659604644550078183387263029044436197 8879931869742080000000000000000000000000000000 (by decide +kernel)
private def pv283 := integerPair bk431 bk433 159461052760153665919073577194988696260929411711 274536358381595520000000000000000000000000000000 (by decide +kernel)
private def pv284 := integerPair bk426 bk432 14648956739260941403890972723750468459751987 12391934927462400000000000000000000000000000 (by decide +kernel)
private def pv285 := integerPair bk419 bk434 19188602932338752015331830853836919554935771 26917234566144000000000000000000000000000000 (by decide +kernel)
private def pv286 := integerPair bk435 bk422 322130932426455606021143692262030465986063779 243448043257600000000000000000000000000000000 (by decide +kernel)
private def pv287 := integerPair bk435 bk425 8366980439061889061065782259066834019488630423 6342808478387200000000000000000000000000000000 (by decide +kernel)
private def pv288 := integerPair bk435 bk427 15931829247460374039524941209895405834978278683 12242036463521280000000000000000000000000000000 (by decide +kernel)
private def pv289 := integerPair bk436 bk437 80774746366548681946084582318766162367893 79566708608000000000000000000000000000000 (by decide +kernel)
private def pv290 := integerPair bk436 bk439 5236768026669842502577610964306223473555653 5182588317440000000000000000000000000000000 (by decide +kernel)
private def pv291 := integerPair bk426 bk437 116067809788252050750062573591945800160146687 100225970478336000000000000000000000000000000 (by decide +kernel)
private def pv292 := integerPair bk436 bk440 49681279471906692404114893819310243174823877 50013677201280000000000000000000000000000000 (by decide +kernel)
private def pv293 := integerPair bk441 bk412 339658147156991566888256617826426125409 1867390453760000000000000000000000000000 (by decide +kernel)
private def pv294 := integerPair bk443 bk412 8691411953793857522594943109739 21250000000000000000000000000000 (by decide +kernel)
private def pv295 := integerPair bk441 bk395 2548258866096849842639348004651017648251149 554596084900000000000000000000000000000000000 (by decide +kernel)
private def pv296 := integerPair bk443 bk395 195041995829956168713886756636490941467 827200000000000000000000000000000000000 (by decide +kernel)
private def pv297 := integerPair bk431 bk395 540772135352526972938338176136299876077 5120037120000000000000000000000000000000 (by decide +kernel)
private def pv298 := integerPair bk435 bk395 4330679178545795456015709651843493209701 5120037120000000000000000000000000000000 (by decide +kernel)
private def pv299 := integerPair bk436 bk395 1400669740256494729466835186097680843983 2481600000000000000000000000000000000000 (by decide +kernel)
private def pv300 := integerPair bk1 bk446 1390717101869334243782510275736022884767287 8322656742400000000000000000000000000000000 (by decide +kernel)
private def pv301 := integerPair bk1 bk450 481506551332283948030056307963338265327 3589760512000000000000000000000000000000 (by decide +kernel)
private def pv302 := integerPair bk452 bk449 18870714136042080627885473534063400348017043 78199451046400000000000000000000000000000000 (by decide +kernel)
private def pv303 := integerPair bk1 bk454 766831085914769616426084280920931156440667 5968107641600000000000000000000000000000000 (by decide +kernel)
private def pv304 := integerPair bk456 bk449 2892176048571201265641830615963368838762269 5107394799360000000000000000000000000000000 (by decide +kernel)
private def pv305 := integerPair bk443 bk446 69092034701443623417776609342115754353 108726016000000000000000000000000000000 (by decide +kernel)
private def pv306 := integerPair bk443 bk450 2198870787432109442390951785958966716187 3667423600000000000000000000000000000000 (by decide +kernel)
private def pv307 := integerPair bk443 bk449 210227578323128481554560696124632106036509 335234407680000000000000000000000000000000 (by decide +kernel)
private def pv308 := integerPair bk443 bk454 694969858045720326225655974128791282282259 1170667268160000000000000000000000000000000 (by decide +kernel)
private def pv309 := integerPair bk457 bk395 189506661740304333445948330187115228269746137 88058004320000000000000000000000000000000000 (by decide +kernel)
private def pv310 := integerPair bk460 bk395 25291512537860297866422306820531538662292853509 13825106678240000000000000000000000000000000000 (by decide +kernel)
private def pv311 := integerPair bk464 bk395 323338413262172334762543539088708925065451523 170263538199040000000000000000000000000000000 (by decide +kernel)
private def pv312 := integerPair bk1 bk466 4774624162738389709177839506091954567 45671912000000000000000000000000000000 (by decide +kernel)
private def pv313 := integerPair bk186 bk466 345544357183326368711291836304185894199863 818042071808000000000000000000000000000000 (by decide +kernel)
private def pv314 := integerPair bk327 bk468 527639422624451973777405782677723331234948547 501961045424384000000000000000000000000000000 (by decide +kernel)
private def pv315 := integerPair bk329 bk466 65937242733518372929211495885785866092588823 27523056728960000000000000000000000000000000 (by decide +kernel)
private def pv316 := integerPair bk469 bk470 6852195649150157138796505296453033511457 4336608573440000000000000000000000000000 (by decide +kernel)
private def pv317 := integerPair bk456 bk466 7123257395940487467805153188236056727711 13950693120000000000000000000000000000000 (by decide +kernel)
private def pv318 := integerPair bk461 bk471 2067671341123646596952431110285064681277007671 1983649054732800000000000000000000000000000000 (by decide +kernel)
private def pv319 := integerPair bk461 bk472 84565278034777640576076961660567610765235913559 81769964872377600000000000000000000000000000000 (by decide +kernel)
private def pv320 := integerPair bk329 bk471 855771826489861746375255310420252187228516433 358543603874560000000000000000000000000000000 (by decide +kernel)
private def pv321 := integerPair bk469 bk473 40314501494359834799773319883102991691319 25678689587200000000000000000000000000000 (by decide +kernel)
private def pv322 := integerPair bk462 bk466 17246089260562329104242390818967690554384623 7251038828800000000000000000000000000000000 (by decide +kernel)
private def pv323 := integerPair bk462 bk468 44786684466547189484239053520129398301536791 18891895759360000000000000000000000000000000 (by decide +kernel)
private def pv324 := integerPair bk462 bk470 4488034607465137127598907282191763513519891 1921962099200000000000000000000000000000000 (by decide +kernel)
private def pv325 := integerPair bk463 bk474 15073708289978135586951874647438830147559 8645577472000000000000000000000000000000 (by decide +kernel)
private def pv326 := integerPair bk463 bk475 903545956364563126766906011789384308032487 520896042688000000000000000000000000000000 (by decide +kernel)
private def pv327 := integerPair bk329 bk474 1798535483152916532014283986195338587849591437 767551280257920000000000000000000000000000000 (by decide +kernel)
private def pv328 := integerPair bk463 bk476 493803383721523346463617447539220890634909 290460153984000000000000000000000000000000 (by decide +kernel)
private def pv329 := integerPair bk477 bk162 563542383804300901029509283601097856013985113 327938279468800000000000000000000000000000000 (by decide +kernel)
private def pv330 := integerPair bk478 bk162 727645077759302698009101343907780028438527481 495060671890400000000000000000000000000000000 (by decide +kernel)
private def pv331 := integerPair bk479 bk162 35189379356273661554395099140640485888407541 21141942709888000000000000000000000000000000 (by decide +kernel)
private def pv332 := integerPair bk480 bk446 19574008677671426913242122398791453596144483 13918375864176000000000000000000000000000000 (by decide +kernel)
private def pv333 := integerPair bk481 bk164 253125257989803517055725358740677751296000157 209473376196480000000000000000000000000000000 (by decide +kernel)
private def pv334 := integerPair bk480 bk164 107804813098112263033129591252843070462701679 76839532857120000000000000000000000000000000 (by decide +kernel)
private def pv335 := integerPair bk482 bk164 5819886560932812211795586588452613598678400663 4293283694311040000000000000000000000000000000 (by decide +kernel)
private def pv336 := integerPair bk477 bk446 2517111868043071978182168611822667562072373 1536635976512000000000000000000000000000000 (by decide +kernel)
private def pv337 := integerPair bk478 bk447 128886205625107190515925776206527461322221 97760219920000000000000000000000000000000 (by decide +kernel)
private def pv338 := integerPair bk477 bk395 38756810580104733204463865071534866468464167 31231411640000000000000000000000000000000000 (by decide +kernel)
private def pv339 := integerPair bk479 bk455 1685507837981742712728441648879688532421509 1263594456800000000000000000000000000000000 (by decide +kernel)
private def pv340 := integerPair bk483 bk446 18455633385389309280298954002520747651398677 11550814501408000000000000000000000000000000 (by decide +kernel)
private def pv341 := integerPair bk484 bk447 13202462075456770841311302522782779183288033 10288020431920000000000000000000000000000000 (by decide +kernel)
private def pv342 := integerPair bk483 bk183 1559998055243513252845378574059091761635707713 1056469445116800000000000000000000000000000000 (by decide +kernel)
private def pv343 := integerPair bk485 bk183 49687556845087466185252108614885113992453671 34928111722240000000000000000000000000000000 (by decide +kernel)
private def pv344 := integerPair bk355 bk486 417619531093950064521552365760650071436822869 443023523196800000000000000000000000000000000 (by decide +kernel)
private def pv345 := integerPair bk356 bk486 1728376025653082696182533822411713793837623133 2140144404366080000000000000000000000000000000 (by decide +kernel)
private def pv346 := integerPair bk357 bk486 33126586900874453118114094468572585542489106761 39690637572185600000000000000000000000000000000 (by decide +kernel)
private def pv347 := integerPair bk488 bk487 1095615383337907454317842649602949444026657 1406280500480000000000000000000000000000000 (by decide +kernel)
private def pv348 := integerPair bk490 bk487 586617928163224083959895994159447385087149537 871204205848320000000000000000000000000000000 (by decide +kernel)
private def pv349 := integerPair bk349 bk487 87786802393146002601658018011010108662011 98753739800000000000000000000000000000000 (by decide +kernel)
private def pv350 := integerPair bk491 bk487 502321025189482531439519845715887858893307607 734129250666240000000000000000000000000000000 (by decide +kernel)
private def pv351 := integerPair bk355 bk165 1594158311474042316535701052151049440834257 2288373474150400000000000000000000000000000 (by decide +kernel)
private def pv352 := integerPair bk356 bk165 38807997883524223260830656630327975852835089 69091276046464000000000000000000000000000000 (by decide +kernel)
private def pv353 := integerPair bk357 bk165 301675104398693446202864883387627049415447837 512540516680192000000000000000000000000000000 (by decide +kernel)
private def pv354 := integerPair bk494 bk495 4373633596547846035904168715966165236456699629 5320534028659200000000000000000000000000000000 (by decide +kernel)
private def pv355 := integerPair bk496 bk495 886196260600200756527279547946684548471447857 1285113603845376000000000000000000000000000000 (by decide +kernel)
private def pv356 := integerPair bk349 bk495 7012244979046971898578695899478962438554889 8502864376000000000000000000000000000000000 (by decide +kernel)
private def pv357 := integerPair bk497 bk495 23633136072438261891065352789374420792583287 33101983799456000000000000000000000000000000 (by decide +kernel)
private def pv358 := integerPair bk355 bk346 59090437545458761987816800645714600406495839 114475316615296000000000000000000000000000000 (by decide +kernel)
private def pv359 := integerPair bk356 bk395 344798356094941013190418645703626292193921333 1540353853280000000000000000000000000000000000 (by decide +kernel)
private def pv360 := integerPair bk355 bk395 91158592149073261585559324135607148769036669 255090447040000000000000000000000000000000000 (by decide +kernel)
private def pv361 := integerPair bk357 bk395 260029644077901164687686305022224798853250887 1038802061440000000000000000000000000000000000 (by decide +kernel)
private def pv362 := integerPair bk1 bk498 23902988364183532596131064993118105889773 79819365683200000000000000000000000000000 (by decide +kernel)
private def pv363 := integerPair bk170 bk499 33617235345092373110215449894637605809335813769 71635089323469056000000000000000000000000000000 (by decide +kernel)
private def pv364 := integerPair bk172 bk498 4114791787213866285516540781407455401245315173 3927827956384640000000000000000000000000000000 (by decide +kernel)
private def pv365 := integerPair bk173 bk500 1130605026829114359367914060485295089018660317 1488442760535808000000000000000000000000000000 (by decide +kernel)
private def pv366 := integerPair bk1 bk501 30814278160500047170380329773687961391583 103980903403520000000000000000000000000000 (by decide +kernel)
private def pv367 := integerPair bk170 bk502 458421650616116878094688757867182668396482242191 984313685869990784000000000000000000000000000000 (by decide +kernel)
private def pv368 := integerPair bk172 bk501 53429817085427406642088291739156428690746737363 51167920945335040000000000000000000000000000000 (by decide +kernel)
private def pv369 := integerPair bk173 bk503 14652491254030247125169613683515213081321725873 19389984069682688000000000000000000000000000000 (by decide +kernel)
private def pv370 := integerPair bk229 bk498 267446970058711893785684261601667442780587869 338185721561600000000000000000000000000000000 (by decide +kernel)
private def pv371 := integerPair bk229 bk499 3470981028241471952360805250094471283990020271 4405554534937600000000000000000000000000000000 (by decide +kernel)
private def pv372 := integerPair bk229 bk500 2400635722598869789836330811977298309556814357 3111085167625600000000000000000000000000000000 (by decide +kernel)
private def pv373 := integerPair bk230 bk504 5688907176418490498482108108350826556032087 10333394078740480000000000000000000000000000 (by decide +kernel)
private def pv374 := integerPair bk230 bk505 368288224497652965406023222742636099153511119 673067019723366400000000000000000000000000000 (by decide +kernel)
private def pv375 := integerPair bk172 bk504 6083906376630646120557362638927023780698602529 5905056605615552000000000000000000000000000000 (by decide +kernel)
private def pv376 := integerPair bk173 bk506 8305319093288030949515870259223524800954647639 11188548547417472000000000000000000000000000000 (by decide +kernel)
private def pv377 := integerPair bk507 bk218 44361116493621096635789837305227751488448181 76030383228800000000000000000000000000000000 (by decide +kernel)
private def pv378 := integerPair bk510 bk218 53186915946236016730721321998116989365977 97258927360000000000000000000000000000000 (by decide +kernel)
private def pv379 := integerPair bk512 bk218 19523022817647118078580285203202624574435123 12852072544000000000000000000000000000000000 (by decide +kernel)
private def pv380 := integerPair bk513 bk218 8533668924417342042530050878477225099469 10445042650000000000000000000000000000000 (by decide +kernel)
private def pv381 := integerPair bk516 bk395 1035576479049747359566386643721228076844571293 4197437302080000000000000000000000000000000000 (by decide +kernel)
private def pv382 := integerPair bk510 bk395 31673312893076353107270292336461734682203789 95959666880000000000000000000000000000000000 (by decide +kernel)
private def pv383 := integerPair bk512 bk395 17754745053584791803122964005541085458281027 13708523840000000000000000000000000000000000 (by decide +kernel)
private def pv384 := integerPair bk513 bk395 60899033769430270852409835495368218914233 101861408000000000000000000000000000000000 (by decide +kernel)
private def pv385 := integerPair bk507 bk395 42405024486839023458301838913907452801120929 115852834240000000000000000000000000000000000 (by decide +kernel)
private def pv386 := integerPair bk519 bk395 981975042713863432964234812172675733452577573 3483439456640000000000000000000000000000000000 (by decide +kernel)
private def pv387 := integerPair bk1 bk522 110920508324138891468492169358811395248743 465286105856000000000000000000000000000000 (by decide +kernel)
private def pv388 := integerPair bk1 bk523 2479932253961331323315127676715876233697 11276691712000000000000000000000000000000 (by decide +kernel)
private def pv389 := integerPair bk1 bk524 22612935107861847077696362868532546735318039 107008117902400000000000000000000000000000000 (by decide +kernel)
private def pv390 := integerPair bk525 bk526 859064639623428680942866252707918703480695649 443023523196800000000000000000000000000000000 (by decide +kernel)
private def pv391 := integerPair bk527 bk526 3511207910590980998233540207892709606976365783 2140144404366080000000000000000000000000000000 (by decide +kernel)
private def pv392 := integerPair bk528 bk526 4254643888537874662453205886487031061605709341 2480664848261600000000000000000000000000000000 (by decide +kernel)
private def pv393 := integerPair bk529 bk216 110719385317183455422532838954722017989618121 69091276046464000000000000000000000000000000 (by decide +kernel)
private def pv394 := integerPair bk531 bk216 771254396487363639363094690362606433441458713 565052219386368000000000000000000000000000000 (by decide +kernel)
private def pv395 := integerPair bk512 bk216 183857372744843470419551612272343559857049 109800768320000000000000000000000000000000 (by decide +kernel)
private def pv396 := integerPair bk532 bk216 106005667669657741486040512278413383259267497 75486736509184000000000000000000000000000000 (by decide +kernel)
private def pv397 := integerPair bk525 bk395 93629182349502905012265672528100877886253651 63772611760000000000000000000000000000000000 (by decide +kernel)
private def pv398 := integerPair bk527 bk395 3614080993115024237811556672551829269850507041 3080707706560000000000000000000000000000000000 (by decide +kernel)
private def pv399 := integerPair bk528 bk395 323736391426851506513753613347455424095100803 259700515360000000000000000000000000000000000 (by decide +kernel)
private def pv400 := integerPair bk534 bk535 8909601170437716253154435682433584989479923679 5320534028659200000000000000000000000000000000 (by decide +kernel)
private def pv401 := integerPair bk536 bk535 8879474002069837661571154613752003531087211143 6425568019226880000000000000000000000000000000 (by decide +kernel)
private def pv402 := integerPair bk537 bk535 349196757376072804764400768854808426752519659 240741700359680000000000000000000000000000000 (by decide +kernel)
private def pv403 := integerPair bk1 bk538 31755119793468937214123886203938813451942009 104240384568320000000000000000000000000000000 (by decide +kernel)
private def pv404 := integerPair bk1 bk539 8068593368624134607510726421579405349049 32218700800000000000000000000000000000000 (by decide +kernel)
private def pv405 := integerPair bk1 bk540 26241968920995724513795824375545137458843 120541843136000000000000000000000000000000 (by decide +kernel)
private def pv406 := integerPair bk1 bk526 5943887963140613497269891336134269748935471 29134734720000000000000000000000000000000000 (by decide +kernel)
private def pv407 := integerPair bk1 bk547 8725157062047264482491384521175834187639 43833397504000000000000000000000000000000 (by decide +kernel)
private def pv408 := integerPair bk1 bk545 2916633881450637669701001220168603820318687 14891483509760000000000000000000000000000000 (by decide +kernel)
private def pv409 := integerPair bk1 bk550 216423030768930461710045396249937295405847 1125956978432000000000000000000000000000000 (by decide +kernel)
private def pv410 := integerPair bk553 bk359 127448797745617430247032323407091914516258345577 202060241692085504000000000000000000000000000000 (by decide +kernel)
private def pv411 := integerPair bk554 bk257 588098286769441757793689411804189633245809617 1795031976823859200000000000000000000000000000 (by decide +kernel)
private def pv412 := integerPair bk553 bk395 1548498246429051166464471799359628519459499103 4142124878320000000000000000000000000000000000 (by decide +kernel)
private def pv413 := integerPair bk555 bk395 339339810397966945834579748774708533390753568527 1219353977395840000000000000000000000000000000000 (by decide +kernel)
private def pv414 := integerPair bk1 bk556 519571502727426311826764655265242649782183 1599919008896000000000000000000000000000000 (by decide +kernel)
private def pv415 := integerPair bk1 bk557 3054481014529628752611011862996783166053 9693924448000000000000000000000000000000 (by decide +kernel)
private def pv416 := integerPair bk1 bk558 259282590104201773507867386971182841689053431 837080333356800000000000000000000000000000000 (by decide +kernel)
private def pv417 := integerPair bk1 bk560 41435865861300782683697838947676334337913 320834845760000000000000000000000000000000 (by decide +kernel)
private def pv418 := integerPair bk564 bk560 29696235565708815440836326424675300136507 64753756928000000000000000000000000000000 (by decide +kernel)
private def pv419 := integerPair bk567 bk568 11338835996329931857328649016839277256477981 10947923146496000000000000000000000000000000 (by decide +kernel)
private def pv420 := integerPair bk569 bk560 1434783802869490676775602241899035786614031 615954580160000000000000000000000000000000 (by decide +kernel)
private def pv421 := integerPair bk570 bk571 2993781548832179188162297891064649683443639 1938219994880000000000000000000000000000000 (by decide +kernel)
private def pv422 := integerPair bk1 bk573 30510429323180564531418247489112424191887 310319188608000000000000000000000000000000 (by decide +kernel)
private def pv423 := integerPair bk564 bk573 8662862223759609022100331002027299175857961 20355202721280000000000000000000000000000000 (by decide +kernel)
private def pv424 := integerPair bk567 bk575 863427920114803284018650545324651419294187 862336412224000000000000000000000000000000 (by decide +kernel)
private def pv425 := integerPair bk569 bk573 88926747893363312126980045289910843644769827 38724796648320000000000000000000000000000000 (by decide +kernel)
private def pv426 := integerPair bk570 bk576 13393594064868843362426064067648728617351437 8885263943920000000000000000000000000000000 (by decide +kernel)
private def pv427 := integerPair bk577 bk560 5350836784592311469226681159036401959941739 14187428196600000000000000000000000000000000 (by decide +kernel)
private def pv428 := integerPair bk578 bk579 45274874749932677900955349912561152490299 247301932160000000000000000000000000000000 (by decide +kernel)
private def pv429 := integerPair bk564 bk579 2795707918571524613634169138579095977410223 6822623893120000000000000000000000000000000 (by decide +kernel)
private def pv430 := integerPair bk567 bk581 56853711337077828040339019727231897416451247 57675079858592000000000000000000000000000000 (by decide +kernel)
private def pv431 := integerPair bk569 bk579 118378785410124129742458714215503602005415429 51918858581120000000000000000000000000000000 (by decide +kernel)
private def pv432 := integerPair bk570 bk582 213778913658206365537388177186759435093296321 142951122408640000000000000000000000000000000 (by decide +kernel)
private def pv433 := integerPair bk583 bk584 135932201799573743220604329297823493238467377419 62425912927589120000000000000000000000000000000 (by decide +kernel)
private def pv434 := integerPair bk586 bk585 62890150323044494517224459481356387764717768331 35155404000628480000000000000000000000000000000 (by decide +kernel)
private def pv435 := integerPair bk583 bk559 1234609851319416732012586157403116025280164167 652505455622800000000000000000000000000000000 (by decide +kernel)
private def pv436 := integerPair bk590 bk591 661840207910998764570707772486770822059942638519 344286420392158400000000000000000000000000000000 (by decide +kernel)
private def pv437 := integerPair bk592 bk584 401814069541435889005154400448759039525851293 1064382131834112000000000000000000000000000000 (by decide +kernel)
private def pv438 := integerPair bk424 bk584 198044871212605234598868856918860900843679 412867858816000000000000000000000000000000 (by decide +kernel)
private def pv439 := integerPair bk426 bk584 11859300085784142572554257217180764944682691 10321696470400000000000000000000000000000000 (by decide +kernel)
private def pv440 := integerPair bk419 bk584 44985290994302703394975704693992230125047 64203323520000000000000000000000000000000 (by decide +kernel)
private def pv441 := integerPair bk595 bk585 691034640507175998597173749104853760782130599 2997055397418240000000000000000000000000000000 (by decide +kernel)
private def pv442 := integerPair bk424 bk585 829850316673301675009904948675124712129 2011431296000000000000000000000000000000 (by decide +kernel)
private def pv443 := integerPair bk426 bk585 520597293773134879942982504171039932518401 481306774400000000000000000000000000000000 (by decide +kernel)
private def pv444 := integerPair bk419 bk585 51245243098088403075555862384299871241 80914560000000000000000000000000000000 (by decide +kernel)
private def pv445 := integerPair bk592 bk559 1180714712588603609700873372504204935317794863 12460482020313600000000000000000000000000000000 (by decide +kernel)
private def pv446 := integerPair bk424 bk559 27018523615727643355359471109313500594943 137162665920000000000000000000000000000000 (by decide +kernel)
private def pv447 := integerPair bk426 bk559 60532215807062326355247013061838955692293 69980952000000000000000000000000000000000 (by decide +kernel)
private def pv448 := integerPair bk419 bk559 211713654350779434073665819440033572007 507847200000000000000000000000000000000 (by decide +kernel)
private def pv449 := integerPair bk598 bk591 1191210522552660465298816307787959074873551317 9783659191966400000000000000000000000000000000 (by decide +kernel)
private def pv450 := integerPair bk424 bk591 79886296684246993936058234137569763364273 294905613440000000000000000000000000000000 (by decide +kernel)
private def pv451 := integerPair bk426 bk591 1386314098488236642192081998432026305905753 1474528067200000000000000000000000000000000 (by decide +kernel)
private def pv452 := integerPair bk419 bk591 7042111270173233687041706660988349453 14331099000000000000000000000000000000 (by decide +kernel)
private def pv453 := integerPair bk564 bk559 1913395906008108649828885768210380271583 7356921600000000000000000000000000000000 (by decide +kernel)
private def pv454 := integerPair bk601 bk560 280243180585434890323742604092167357931621 1410016508800000000000000000000000000000000 (by decide +kernel)
private def pv455 := integerPair bk603 bk571 199221703287397814573265148726223567079221 128443235481600000000000000000000000000000 (by decide +kernel)
private def pv456 := integerPair bk601 bk573 7611854744388686864229925911109160060837054359 45919210676236800000000000000000000000000000000 (by decide +kernel)
private def pv457 := integerPair bk603 bk576 178267676104545937149498053777969690464339 117762901226880000000000000000000000000000 (by decide +kernel)
private def pv458 := integerPair bk603 bk582 14227205104596135787768069653880179945178787 9473178858124800000000000000000000000000000 (by decide +kernel)
private def pv459 := integerPair bk604 bk395 231981014720584829583687919575794992913310137 88058004320000000000000000000000000000000000 (by decide +kernel)
private def pv460 := integerPair bk606 bk395 30298990362638841797235373991016272171851477009 13825106678240000000000000000000000000000000000 (by decide +kernel)
private def pv461 := integerPair bk609 bk395 398084828347076836948411262826951340333114243 170263538199040000000000000000000000000000000 (by decide +kernel)
private def pv462 := integerPair bk611 bk395 475190672349730332665385853893869107597181 577468320000000000000000000000000000000000 (by decide +kernel)
private def pv463 := integerPair bk612 bk395 2258964147633976187195666944619493207423617 3487020240000000000000000000000000000000000 (by decide +kernel)
private def pv464 := integerPair bk613 bk395 11175027535259242655381703434859164944002033 16132550720000000000000000000000000000000000 (by decide +kernel)
private def pv465 := integerPair bk607 bk395 18916602138757445433545995090344885645604369 27086664000000000000000000000000000000000000 (by decide +kernel)
private def pv466 := integerPair bk426 bk395 166851693460034224962909749466781214159281 236182144000000000000000000000000000000000 (by decide +kernel)
private def pv467 := integerPair bk608 bk395 54519850649708520433526895249554322151440769 27086664000000000000000000000000000000000000 (by decide +kernel)
private def pv468 := integerPair bk603 bk395 6359823974900454483831206913651003298873 5141875200000000000000000000000000000000 (by decide +kernel)
private def pv469 := integerPair bk621 bk162 6431886567551806829540642543601654327785437 21722966636800000000000000000000000000000000 (by decide +kernel)
private def pv470 := integerPair bk348 bk162 1124902502153974846778399940223762678147779 3598580312320000000000000000000000000000000 (by decide +kernel)
private def pv471 := integerPair bk349 bk162 10466681476590384804490499677830581162858613 12852072544000000000000000000000000000000000 (by decide +kernel)
private def pv472 := integerPair bk230 bk162 92223311418785452577871906888221003057533 190995065600000000000000000000000000000000 (by decide +kernel)
private def pv473 := integerPair bk1 bk164 23742750247828813656670515841329278955021 160654208000000000000000000000000000000000 (by decide +kernel)
private def pv474 := integerPair bk348 bk164 303437129844659057011886271320380567450841 1303269626624000000000000000000000000000000 (by decide +kernel)
private def pv475 := integerPair bk349 bk164 3417759150216135499655640904266995356339583 4654534380800000000000000000000000000000000 (by decide +kernel)
private def pv476 := integerPair bk230 bk164 27864240626268844365383182784473066744803 69171185920000000000000000000000000000000 (by decide +kernel)
private def pv477 := integerPair bk621 bk620 339745871613812767684697381958446386238409 6602625570112000000000000000000000000000000 (by decide +kernel)
private def pv478 := integerPair bk348 bk620 2993722891744246196658900916479043699992561 43751074673152000000000000000000000000000000 (by decide +kernel)
private def pv479 := integerPair bk349 bk620 3567878060577067242378637224681140081967111 6250153524736000000000000000000000000000000 (by decide +kernel)
private def pv480 := integerPair bk230 bk620 2013551465567882964822337236755566909827 8443975782400000000000000000000000000000 (by decide +kernel)
private def pv481 := integerPair bk627 bk183 13018026236081995947774896931213531208136279 244935653476800000000000000000000000000000000 (by decide +kernel)
private def pv482 := integerPair bk348 bk183 1995202964652289006033619566348874008585071 17992901561600000000000000000000000000000000 (by decide +kernel)
private def pv483 := integerPair bk349 bk183 7874317515077823927448799581566338747034453 12852072544000000000000000000000000000000000 (by decide +kernel)
private def pv484 := integerPair bk230 bk183 53629208483022217603964482756334777253613 190995065600000000000000000000000000000000 (by decide +kernel)
private def pv485 := integerPair bk186 bk620 142572064924050255642897436706070978936933 464418668032000000000000000000000000000000 (by decide +kernel)
private def pv486 := zeroPair bk630 bk620 (by rfl) (Or.inr rfl)
private def pv487 := integerPair bk170 bk162 147899008391949096244009116745692496499513 382006950290000000000000000000000000000000 (by decide +kernel)
private def pv488 := integerPair bk170 bk164 42452349807195565893662078453523334624919 138348463078000000000000000000000000000000 (by decide +kernel)
private def pv489 := integerPair bk170 bk631 70613862776557683249668982217192876689737697 702569717997056000000000000000000000000000000 (by decide +kernel)
private def pv490 := integerPair bk173 bk632 15210079448150741795933580611056439781705513 40228182717184000000000000000000000000000000 (by decide +kernel)
private def pv491 := integerPair bk1 bk165 131226106640017613823117167634994435893637 1379502924800000000000000000000000000000000 (by decide +kernel)
private def pv492 := integerPair bk1 bk183 202071584912138699279215701792444122688453 5766766720000000000000000000000000000000000 (by decide +kernel)
private def pv493 := integerPair bk170 bk183 351839320059766427951469211693561716354709 1910034751450000000000000000000000000000000 (by decide +kernel)
private def pv494 := integerPair bk186 bk631 803305456294394061490517788564843295941707 3018721342208000000000000000000000000000000 (by decide +kernel)
private def pv495 := integerPair bk639 bk395 24705569410748232428687206474487657445559837 79563607794880000000000000000000000000000000000 (by decide +kernel)
private def pv496 := integerPair bk145 bk395 5537873236857628704988206735614895909 37600000000000000000000000000000000000 (by decide +kernel)
private def pv497 := integerPair bk146 bk395 34842801181710235219341252978470833509 37600000000000000000000000000000000000 (by decide +kernel)
private def pv498 := integerPair bk147 bk395 52032626600739718571269761097303187597 103400000000000000000000000000000000000 (by decide +kernel)
private def pv499 := integerPair bk642 bk375 19809906129622386061812733391505173493304657 50692221475796800000000000000000000000000000 (by decide +kernel)
private def pv500 := integerPair bk145 bk375 657465223719891079825920987263235920953 1117086558000000000000000000000000000000 (by decide +kernel)
private def pv501 := integerPair bk146 bk375 7696623850319891176997139001356236644613 5585432790000000000000000000000000000000 (by decide +kernel)
private def pv502 := integerPair bk147 bk375 4222947657891119729691054314286147629 4380731600000000000000000000000000000 (by decide +kernel)
private def pv503 := integerPair bk642 bk297 1800186032718066536489979671404787401039437 6141852883264000000000000000000000000000000 (by decide +kernel)
private def pv504 := integerPair bk145 bk297 8324856218583326307787681068093140767 16918230000000000000000000000000000000 (by decide +kernel)
private def pv505 := integerPair bk146 bk297 15490644168401461359426288212699917637 12084450000000000000000000000000000000 (by decide +kernel)
private def pv506 := integerPair bk147 bk297 8192658953376673027629257962385557 9478000000000000000000000000000000 (by decide +kernel)
private def pv507 := integerPair bk642 bk376 3228085115237413659077306611917529597046198091 17070039147032768000000000000000000000000000000 (by decide +kernel)
private def pv508 := integerPair bk145 bk376 2341359748930679596369281695357044414095083 6018662657280000000000000000000000000000000 (by decide +kernel)
private def pv509 := integerPair bk146 bk376 5063980896073525989159488511615744829017889 4299044755200000000000000000000000000000000 (by decide +kernel)
private def pv510 := integerPair bk147 bk376 12769733865753298003435401492433214046411 16858999040000000000000000000000000000000 (by decide +kernel)
private def pv511 := integerPair bk642 bk380 41519910223878495233429409714810192109795691 253461107378984000000000000000000000000000000 (by decide +kernel)
private def pv512 := integerPair bk145 bk380 1452758186238926288876065435814039275351 3989594850000000000000000000000000000000 (by decide +kernel)
private def pv513 := integerPair bk146 bk380 4602256566039237558781446910842651446671 3989594850000000000000000000000000000000 (by decide +kernel)
private def pv514 := integerPair bk147 bk380 57258515419097638856625429212227921279 78227350000000000000000000000000000000 (by decide +kernel)
private def pv515 := integerPair bk1 bk645 996877968796434278531641281479130600407706467 3449665765145600000000000000000000000000000000 (by decide +kernel)
private def pv516 := integerPair bk655 bk645 54767286332978810690654151944841513244372449 119730593219818000000000000000000000000000000 (by decide +kernel)
private def pv517 := integerPair bk656 bk645 24784330350465807851455975646427767659881747 75824886369806000000000000000000000000000000 (by decide +kernel)
private def pv518 := integerPair bk1 bk647 7629989814038838671051111362100416881030979 30323508300800000000000000000000000000000000 (by decide +kernel)
private def pv519 := integerPair bk655 bk647 62786009538835030826288102678211964601121 150352107982000000000000000000000000000000 (by decide +kernel)
private def pv520 := integerPair bk656 bk647 191326178030813962142321795699986559936997 666521549558000000000000000000000000000000 (by decide +kernel)
private def pv521 := integerPair bk1 bk648 5883279119755935656661806898207809228802861 24891064140800000000000000000000000000000000 (by decide +kernel)
private def pv522 := integerPair bk1 bk646 915652562694385464205851030187842912479 5284913920000000000000000000000000000000 (by decide +kernel)
private def pv523 := integerPair bk1 bk654 3535300284479714262508813250976670508739 23451805520000000000000000000000000000000 (by decide +kernel)
private def pv524 := integerPair bk655 bk646 3385757142777292683465971155094487991874542713 10131163387977632000000000000000000000000000000 (by decide +kernel)
private def pv525 := integerPair bk656 bk657 4373210751776066264005990864584481239722106209 26252090222101568000000000000000000000000000000 (by decide +kernel)
private def pv526 := integerPair bk1 bk666 86348702940964619101672950901117514343662261 492809395020800000000000000000000000000000000 (by decide +kernel)
private def pv527 := integerPair bk655 bk666 32862798504223823111367720533852551160793 97739259771280000000000000000000000000000 (by decide +kernel)
private def pv528 := integerPair bk656 bk666 2227572388108285718963895121808839235297109 10832126624258000000000000000000000000000000 (by decide +kernel)
private def pv529 := integerPair bk669 bk648 2793263917972230158114073875900956777443 10527487456000000000000000000000000000000 (by decide +kernel)
private def pv530 := integerPair bk669 bk646 1799016840264751609932774352708681879646413 9077652721280000000000000000000000000000000 (by decide +kernel)
private def pv531 := integerPair bk669 bk654 35945399680935335382012358057214746780389 206310289120000000000000000000000000000000 (by decide +kernel)
private def pv532 := integerPair bk670 bk395 26311901769185668531761486121307396416230183451 7098829886720000000000000000000000000000000000 (by decide +kernel)
private def pv533 := integerPair bk673 bk395 14432726034466052543009936397839681424233 2481600000000000000000000000000000000000 (by decide +kernel)
private def pv534 := integerPair bk677 bk395 3042651116715588623178694161982286248087771 746672080000000000000000000000000000000000 (by decide +kernel)
private def pv535 := integerPair bk679 bk395 736066613365205894742970272727636555376901 85333952000000000000000000000000000000000 (by decide +kernel)
private def pv536 := integerPair bk680 bk395 5504398263841257500157372435494346797661 827200000000000000000000000000000000000 (by decide +kernel)
private def pv537 := integerPair bk1 bk683 609780615574695228636840995377459110554733303 1724832882572800000000000000000000000000000000 (by decide +kernel)
private def pv538 := integerPair bk1 bk685 5032140524170546769658574905194038872223997 15161754150400000000000000000000000000000000 (by decide +kernel)
private def pv539 := integerPair bk1 bk686 8082865494824599283147060353775361518247297 24891064140800000000000000000000000000000000 (by decide +kernel)
private def pv540 := integerPair bk1 bk684 110311700051316202159730283743458529460819 375228888320000000000000000000000000000000 (by decide +kernel)
private def pv541 := integerPair bk1 bk692 212973701959379442544761164723340416319393 750457776640000000000000000000000000000000 (by decide +kernel)
private def pv542 := integerPair bk1 bk695 7347168872921332027341020967516186909747427 26507972147800000000000000000000000000000000 (by decide +kernel)
private def pv543 := integerPair bk1 bk704 74350008199896174574722174749169054820369569 246404697510400000000000000000000000000000000 (by decide +kernel)
private def pv544 := integerPair bk708 bk395 10308073214570109574800386589465097122649059451 7098829886720000000000000000000000000000000000 (by decide +kernel)
private def pv545 := integerPair bk711 bk395 1975923251871364452301513614435209986661 827200000000000000000000000000000000000 (by decide +kernel)
private def pv546 := integerPair bk715 bk395 2847322040249229509433987271423345916709 1706679040000000000000000000000000000000 (by decide +kernel)
private def pv547 := integerPair bk717 bk395 104234475989168292211085479075966714571157 26666860000000000000000000000000000000000 (by decide +kernel)
private def pv548 := integerPair bk718 bk395 2458592003508755482432739585240469267411 827200000000000000000000000000000000000 (by decide +kernel)
private def pv549 := integerPair bk1 bk721 68334130441990839283127931354523501729008143 215052213376000000000000000000000000000000000 (by decide +kernel)
private def pv550 := integerPair bk731 bk721 47398611973018754309877788861116905501501749 109510476513025000000000000000000000000000000 (by decide +kernel)
private def pv551 := integerPair bk1 bk723 2821334726211007523871601171412330458838953 10028011136000000000000000000000000000000000 (by decide +kernel)
private def pv552 := integerPair bk731 bk723 1005263356779201771707004926602403858894421 2553268949762500000000000000000000000000000 (by decide +kernel)
private def pv553 := integerPair bk1 bk724 2035941468410261578151916799603227860444017 7689704422400000000000000000000000000000000 (by decide +kernel)
private def pv554 := integerPair bk1 bk722 346281502581849915465868303577155925152709 1619851101440000000000000000000000000000000 (by decide +kernel)
private def pv555 := integerPair bk1 bk730 635380944959897186160603333628897081315663 3239702202880000000000000000000000000000000 (by decide +kernel)
private def pv556 := integerPair bk731 bk722 14925722766882355647500200794905180884972520113 46456821588657920000000000000000000000000000000 (by decide +kernel)
private def pv557 := integerPair bk1 bk733 2404793767212627634116004335035046757540173 13044484294400000000000000000000000000000000 (by decide +kernel)
private def pv558 := integerPair bk1 bk742 7032801856974787801258010760194398320649289 30721744768000000000000000000000000000000000 (by decide +kernel)
private def pv559 := integerPair bk731 bk742 5279697007473792960046161654412860689488079 15644353787575000000000000000000000000000000 (by decide +kernel)
private def pv560 := integerPair bk746 bk395 1936444346323302599593096432962779274279931 577468320000000000000000000000000000000000 (by decide +kernel)
private def pv561 := integerPair bk751 bk395 5330232548222789645501564444529873745573079 1888802630000000000000000000000000000000000 (by decide +kernel)
private def pv562 := integerPair bk755 bk395 48439955536840287970012877622569713220488033 16132550720000000000000000000000000000000000 (by decide +kernel)
private def pv563 := integerPair bk757 bk395 2135560200501411534483948047035421317481 463232000000000000000000000000000000000 (by decide +kernel)
private def pv564 := integerPair bk761 bk395 443957360611453593733069745710305678820266759 126404432000000000000000000000000000000000000 (by decide +kernel)
private def pv565 := integerPair bk765 bk395 13593693460970295783444402538053759420190057 1805777600000000000000000000000000000000000 (by decide +kernel)
private def pv566 := integerPair bk766 bk395 96308476194192844042627563341704988120547 17139584000000000000000000000000000000000 (by decide +kernel)
private def pv567 := integerPair bk1 bk771 40711533715499037939223285916126527144751 115088013040000000000000000000000000000000 (by decide +kernel)
private def pv568 := integerPair bk1 bk773 1033592592580878739530053347852978716415687 3111383017600000000000000000000000000000000 (by decide +kernel)
private def pv569 := integerPair bk1 bk772 114151400191706432658951929022908885012499 375228888320000000000000000000000000000000 (by decide +kernel)
private def pv570 := integerPair bk1 bk780 252142373130440999911819062529798682844803 835210151776000000000000000000000000000000 (by decide +kernel)
private def pv571 := integerPair bk1 bk783 20096984544383015033279303616760748606123 68223434240000000000000000000000000000000 (by decide +kernel)
private def pv572 := integerPair bk1 bk788 1065075927827274936374732369252737330713003 3674679351200000000000000000000000000000000 (by decide +kernel)
private def pv573 := integerPair bk792 bk395 8960975090522744864690978377631171187339371451 7098829886720000000000000000000000000000000000 (by decide +kernel)
private def pv574 := integerPair bk795 bk395 6440316816105609002770715617974960689557 5120037120000000000000000000000000000000 (by decide +kernel)
private def pv575 := integerPair bk797 bk395 79468933764109181172435847189236342020609 25600185600000000000000000000000000000000 (by decide +kernel)
private def pv576 := integerPair bk798 bk395 5356963458564094216983534588649391975983 2481600000000000000000000000000000000000 (by decide +kernel)
private def pv577 := integerPair bk1 bk801 16678843632247352938163113987208355118899229 55025609999360000000000000000000000000000000 (by decide +kernel)
private def pv578 := integerPair bk1 bk803 6665574525701828444065608677846292675262061 24891064140800000000000000000000000000000000 (by decide +kernel)
private def pv579 := integerPair bk1 bk802 9262449052812426335105658403667638810783 46903611040000000000000000000000000000000 (by decide +kernel)
private def pv580 := integerPair bk1 bk808 5416227699857325893589109912904432757610831 26726724856832000000000000000000000000000000 (by decide +kernel)
private def pv581 := integerPair bk810 bk395 439191952160384540389829140319437963329731733 151038933760000000000000000000000000000000000 (by decide +kernel)
private def pv582 := integerPair bk813 bk395 15069496761992418135028248425605347059407 5120037120000000000000000000000000000000 (by decide +kernel)
private def pv583 := integerPair bk815 bk395 1640348972337999106685596687040138319666113 256001856000000000000000000000000000000000 (by decide +kernel)
private def pv584 := integerPair bk816 bk395 11598369729737254089370077314579468882233 2481600000000000000000000000000000000000 (by decide +kernel)
private def pv585 := integerPair bk1 bk819 510808064509731653363480611953259914450339049 1614650374937600000000000000000000000000000000 (by decide +kernel)
private def pv586 := integerPair bk1 bk821 2136928697879692274114784335838843246542817 7689704422400000000000000000000000000000000 (by decide +kernel)
private def pv587 := integerPair bk1 bk820 374983545522720387384582511064055910907429 1619851101440000000000000000000000000000000 (by decide +kernel)
private def pv588 := integerPair bk1 bk827 52065539738850124336478760639444256802987647 230664339276800000000000000000000000000000000 (by decide +kernel)
private def pv589 := integerPair bk1 bk830 63261606945592697000072663674832542391173 294518382080000000000000000000000000000000 (by decide +kernel)
private def pv590 := integerPair bk1 bk834 12935624871424477807014676150572969391925589 62535715985600000000000000000000000000000000 (by decide +kernel)
private def pv591 := integerPair bk838 bk395 1728193536350485506333160772460405607113431 577468320000000000000000000000000000000000 (by decide +kernel)
private def pv592 := integerPair bk842 bk395 462843021928926617134206702433713256184548709 181325052480000000000000000000000000000000000 (by decide +kernel)
private def pv593 := integerPair bk845 bk395 43129138135228528005629087530290461907192033 16132550720000000000000000000000000000000000 (by decide +kernel)
private def pv594 := integerPair bk847 bk395 75205303444177721569594947453360876123248119 27086664000000000000000000000000000000000000 (by decide +kernel)
private def pv595 := integerPair bk851 bk395 32969141041666452332036568376213073670393131 5417332800000000000000000000000000000000000 (by decide +kernel)
private def pv596 := integerPair bk852 bk395 216596697609708735719014868241406384178791 51418752000000000000000000000000000000000 (by decide +kernel)
private def pv597 := integerPair bk1 bk857 283326600289110972353218407559240341694643399 855906443392000000000000000000000000000000000 (by decide +kernel)
private def pv598 := integerPair bk1 bk859 48444446223173230624546957433969846626933 166588032000000000000000000000000000000000 (by decide +kernel)
private def pv599 := integerPair bk1 bk858 37797873454098058278198794225311208467703 148961967440000000000000000000000000000000 (by decide +kernel)
private def pv600 := integerPair bk1 bk862 103693494807399395893905862839416621511791 433343905280000000000000000000000000000000 (by decide +kernel)
private def pv601 := integerPair bk1 bk864 13824163249938393142403757501021286772284851 59563781763200000000000000000000000000000000 (by decide +kernel)
private def pv602 := integerPair bk1 bk872 30655520810769011942968233096046750867640337 122272349056000000000000000000000000000000000 (by decide +kernel)
private def pv603 := integerPair bk876 bk395 908729116730563743081523313401421846990157287 347558502720000000000000000000000000000000000 (by decide +kernel)
private def pv604 := integerPair bk194 bk395 252964083697667206144354980537063111269964827 95959666880000000000000000000000000000000000 (by decide +kernel)
private def pv605 := integerPair bk196 bk395 79716160878870230653506676701709293514122461 13708523840000000000000000000000000000000000 (by decide +kernel)
private def pv606 := integerPair bk195 bk395 185638105703965462684866803629742954229481 50930704000000000000000000000000000000000 (by decide +kernel)
private def pv607 := integerPair bk880 bk395 1554839300770302836640132778697939953237197403 699572883680000000000000000000000000000000000 (by decide +kernel)
private def pv608 := integerPair bk885 bk395 24545618903696504203525095506815820665742144719 10450318369920000000000000000000000000000000000 (by decide +kernel)
private def pv609 := integerPair bk1 bk889 124362052825509208241528149201748738532602153 327878296345600000000000000000000000000000000 (by decide +kernel)
private def pv610 := integerPair bk1 bk891 3913926536397031403918257561023635142473253 10815156352000000000000000000000000000000000 (by decide +kernel)
private def pv611 := integerPair bk1 bk890 1312246431201754352304170648685953614421689 3824528730880000000000000000000000000000000 (by decide +kernel)
private def pv612 := integerPair bk1 bk894 2573775925330345577115538963560890001089063 7649057461760000000000000000000000000000000 (by decide +kernel)
private def pv613 := integerPair bk1 bk896 7553897125660871546069467481677297314427391 22686102982400000000000000000000000000000000 (by decide +kernel)
private def pv614 := integerPair bk1 bk904 112513451055046547842281546231694894782564281 327878296345600000000000000000000000000000000 (by decide +kernel)
private def pv615 := integerPair bk908 bk395 1159492424817905676084428299052270206368194707 1395314011520000000000000000000000000000000000 (by decide +kernel)
private def pv616 := integerPair bk912 bk395 136752326685545880812428415851797159384308873 186269061440000000000000000000000000000000000 (by decide +kernel)
private def pv617 := integerPair bk914 bk395 389526955279851692638185525600979831892023673 186269061440000000000000000000000000000000000 (by decide +kernel)
private def pv618 := integerPair bk915 bk395 568107598830510095459485378151920541413703 435964480000000000000000000000000000000000 (by decide +kernel)
private def pv619 := integerPair bk918 bk395 10969955247876920780757208121102783158947819173 16851099985280000000000000000000000000000000000 (by decide +kernel)
private def pv620 := integerPair bk923 bk395 291080256232678739161148984955723558012130831 415957850880000000000000000000000000000000000 (by decide +kernel)
private def pv621 := integerPair bk1 bk927 465863777524095294805689829784433306310100849 1350242205312000000000000000000000000000000000 (by decide +kernel)
private def pv622 := integerPair bk1 bk929 908955150583381162474869120729170372851621 2821872768000000000000000000000000000000000 (by decide +kernel)
private def pv623 := integerPair bk1 bk930 553262974018487517994874870990605953422263 1832468352000000000000000000000000000000000 (by decide +kernel)
private def pv624 := integerPair bk1 bk928 39959468616430159247045924421533674383533 148961967440000000000000000000000000000000 (by decide +kernel)
private def pv625 := integerPair bk1 bk937 53579704853882343548599878648630263750041367 192891743616000000000000000000000000000000000 (by decide +kernel)
private def pv626 := integerPair bk1 bk943 110320552605240255362615048427979080611751 433343905280000000000000000000000000000000 (by decide +kernel)
private def pv627 := integerPair bk1 bk948 18034817615324649207024503129740208198121301 73374843027200000000000000000000000000000000 (by decide +kernel)
private def pv628 := integerPair bk952 bk395 806185393971665616549210398558355972310184287 347558502720000000000000000000000000000000000 (by decide +kernel)
private def pv629 := integerPair bk242 bk395 4549335130052392995425799107321943236169051 1713565480000000000000000000000000000000000 (by decide +kernel)
private def pv630 := integerPair bk244 bk395 455794274333778040348658023603063585554517 77889340000000000000000000000000000000000 (by decide +kernel)
private def pv631 := integerPair bk960 bk395 802946951705125847170127282507549430026849 203722816000000000000000000000000000000000 (by decide +kernel)
private def pv632 := integerPair bk962 bk395 8089964298419042641300687112475008283572776793 4197437302080000000000000000000000000000000000 (by decide +kernel)
private def pv633 := integerPair bk968 bk395 21711488117089189153433093134700697847216416719 10450318369920000000000000000000000000000000000 (by decide +kernel)
private def pv634 := integerPair bk972 bk395 169057808088608620763341125771474563524181 50930704000000000000000000000000000000000 (by decide +kernel)
private def pv635 := integerPair bk1 bk973 377193822947290370962312512866603257529597099 1350242205312000000000000000000000000000000000 (by decide +kernel)
private def pv636 := integerPair bk1 bk975 685331658793637203326789282274008946092773 2821872768000000000000000000000000000000000 (by decide +kernel)
private def pv637 := integerPair bk1 bk976 377537511340059875829837894068353194060269 1832468352000000000000000000000000000000000 (by decide +kernel)
private def pv638 := integerPair bk984 bk976 295236096248121466075443745572113645927 1126527950000000000000000000000000000000 (by decide +kernel)
private def pv639 := integerPair bk1 bk974 25326441088584332192756647266226834195713 216671952640000000000000000000000000000000 (by decide +kernel)
private def pv640 := integerPair bk1 bk983 28752117572376964872454229911637850091500317 192891743616000000000000000000000000000000000 (by decide +kernel)
private def pv641 := integerPair bk984 bk974 48383044651194645113638480809351670983190063 292573804357120000000000000000000000000000000 (by decide +kernel)
private def pv642 := integerPair bk986 bk395 54324831089848176021893747079099640070147 11136840000000000000000000000000000000000 (by decide +kernel)
private def pv643 := integerPair bk994 bk395 6761131249412381725569173733667405120509997 1246229440000000000000000000000000000000000 (by decide +kernel)
private def pv644 := integerPair bk996 bk395 14059655198259487539668969804472759979548397 1246229440000000000000000000000000000000000 (by decide +kernel)
private def pv645 := integerPair bk997 bk395 196741016963290036436876156710934407435153 25465352000000000000000000000000000000000 (by decide +kernel)
private def pv646 := integerPair bk1000 bk395 4364298803483429764304459035234584175012103417 1049359325520000000000000000000000000000000000 (by decide +kernel)
private def pv647 := integerPair bk1006 bk395 246207399452213934465965562229804996647775831 55586799840000000000000000000000000000000000 (by decide +kernel)
private def pv648 := integerPair bk1010 bk395 29817267105100348641089867721459590786167 4334528000000000000000000000000000000000 (by decide +kernel)
private def pv649 := integerPair bk1 bk1011 2909922145674638686288702641091243126916602643 7570747696512000000000000000000000000000000000 (by decide +kernel)
private def pv650 := integerPair bk1 bk1013 5296845017671562098309082849805528269838511 14193598848000000000000000000000000000000000 (by decide +kernel)
private def pv651 := integerPair bk1 bk1014 3967356683094959154953746310214425390499253 10815156352000000000000000000000000000000000 (by decide +kernel)
private def pv652 := integerPair bk1 bk1012 1337703361233921154412020664020221426246649 3824528730880000000000000000000000000000000 (by decide +kernel)
private def pv653 := integerPair bk1 bk1021 381695805305898329608835551669742835942223109 1081535385216000000000000000000000000000000000 (by decide +kernel)
private def pv654 := integerPair bk1 bk1027 238857524544517427595018362576784051185453 695368860160000000000000000000000000000000 (by decide +kernel)
private def pv655 := integerPair bk1 bk1032 345821091021049271325763187921518755628389847 1018082016265600000000000000000000000000000000 (by decide +kernel)
private def pv656 := integerPair bk1036 bk1037 2949717358183475395148476721134006121095647199 3634927943337600000000000000000000000000000000 (by decide +kernel)
private def pv657 := integerPair bk1044 bk1037 2603897427882172540194857602555346742503911 3032805746670000000000000000000000000000000 (by decide +kernel)
private def pv658 := integerPair bk1046 bk1037 24252659889899592085975539983365400605442161 10831449095250000000000000000000000000000000 (by decide +kernel)
private def pv659 := integerPair bk1047 bk1037 17442449053822940938283978565556245173981 11154487470000000000000000000000000000000 (by decide +kernel)
private def pv660 := integerPair bk1050 bk395 8686138956079507192133505967248870328193330923 16851099985280000000000000000000000000000000000 (by decide +kernel)
private def pv661 := integerPair bk1044 bk395 138242780717351007647493324634188273662421373 186269061440000000000000000000000000000000000 (by decide +kernel)
private def pv662 := integerPair bk1046 bk395 392448245182189741234912746814466415877124173 186269061440000000000000000000000000000000000 (by decide +kernel)
private def pv663 := integerPair bk1047 bk395 627417857475043977174632598402538844496703 435964480000000000000000000000000000000000 (by decide +kernel)
private def pv664 := integerPair bk1036 bk395 970487170895132197638482556373370891808236707 1395314011520000000000000000000000000000000000 (by decide +kernel)
private def pv665 := integerPair bk1056 bk395 239630515928046003608045521773008325413978831 415957850880000000000000000000000000000000000 (by decide +kernel)
private def pv666 := integerPair bk1060 bk395 502977080682203253892083510454789068051703 435964480000000000000000000000000000000000 (by decide +kernel)
private def pv667 := integerPair bk1 bk1061 9930712089533486202529957561424565134434721817 24871916381312000000000000000000000000000000000 (by decide +kernel)
private def pv668 := integerPair bk1 bk1063 8612214978110741107102650213712139418087023 21931916864000000000000000000000000000000000 (by decide +kernel)
private def pv669 := integerPair bk1 bk1064 13990783962787550735928383588466300699821743 35883399552000000000000000000000000000000000 (by decide +kernel)
private def pv670 := integerPair bk1 bk1062 4465047232825007898161896434070933161210043 11759894798080000000000000000000000000000000 (by decide +kernel)
private def pv671 := integerPair bk1 bk1071 1354184236119691687126567753307826147072982191 3553130911616000000000000000000000000000000000 (by decide +kernel)
private def pv672 := integerPair bk1 bk1077 804161517685568323846611972363368820836861 2138162690560000000000000000000000000000000 (by decide +kernel)
private def pv673 := integerPair bk1 bk1082 29442338406447947767267429972477609901368619 78727478086400000000000000000000000000000000 (by decide +kernel)
private def pv674 := integerPair bk1086 bk1087 149761971770281128194205098385576528216860647 569221072178304000000000000000000000000000000 (by decide +kernel)
private def pv675 := integerPair bk1086 bk395 85688105991799528557670441860139825329622253 2526815923328125000000000000000000000000000000 (by decide +kernel)
private def pv676 := integerPair bk1092 bk395 3978833017733635391199369681855766569446693 38825798352000000000000000000000000000000000 (by decide +kernel)
private def pv677 := integerPair bk1094 bk395 33198119437681332464716474742024759538257633 38825798352000000000000000000000000000000000 (by decide +kernel)
private def pv678 := integerPair bk1095 bk395 22717190261899355894293960426083157602823 42764736000000000000000000000000000000000 (by decide +kernel)
private def pv679 := integerPair bk1098 bk1087 36997667310257971707072467607183886589 61599417600000000000000000000000000000 (by decide +kernel)
private def pv680 := integerPair bk1098 bk395 173031033576459312039649850691202981587689 470412096000000000000000000000000000000000 (by decide +kernel)
private def pv681 := integerPair bk1 bk258 2677469963919555165847984125984461300769742643 7570747696512000000000000000000000000000000000 (by decide +kernel)
private def pv682 := integerPair bk1 bk260 4765305624451927529984298901495953924024893 14193598848000000000000000000000000000000000 (by decide +kernel)
private def pv683 := integerPair bk1 bk261 3506523904277743911699168490834382906105989 10815156352000000000000000000000000000000000 (by decide +kernel)
private def pv684 := integerPair bk1 bk259 268040704050230974561060175880329363181401 956132182720000000000000000000000000000000 (by decide +kernel)
private def pv685 := integerPair bk1 bk268 316609194414474943885434367439843924621102309 1081535385216000000000000000000000000000000000 (by decide +kernel)
private def pv686 := integerPair bk272 bk395 55519193044925977755180926192617966364635781 29687532160000000000000000000000000000000000 (by decide +kernel)
private def pv687 := integerPair bk280 bk395 358530979277755985104871805594917708049958873 186269061440000000000000000000000000000000000 (by decide +kernel)
private def pv688 := integerPair bk282 bk395 164842622872116699410274913899499108270904437 37253812288000000000000000000000000000000000 (by decide +kernel)
private def pv689 := integerPair bk283 bk395 648090755682617466800820172207776239836327 204068480000000000000000000000000000000000 (by decide +kernel)
private def pv690 := integerPair bk286 bk395 25951514252652459069898808758630644821187377173 16851099985280000000000000000000000000000000000 (by decide +kernel)
private def pv691 := integerPair bk292 bk395 685764918810196376846998633213048710972758831 415957850880000000000000000000000000000000000 (by decide +kernel)
private def pv692 := integerPair bk296 bk395 1215138152689424260629563230637694415176703 435964480000000000000000000000000000000000 (by decide +kernel)
private def pv693 := integerPair bk1 bk298 9489907782307692570334012385540683913422943067 24871916381312000000000000000000000000000000000 (by decide +kernel)
private def pv694 := integerPair bk1 bk300 16270931735116441996267996032277175814849013 43863833728000000000000000000000000000000000 (by decide +kernel)
private def pv695 := integerPair bk1 bk301 13130800941376032851148448589645352520279709 35883399552000000000000000000000000000000000 (by decide +kernel)
private def pv696 := integerPair bk1 bk299 1999170038693573734534536342013552676941549 5879947399040000000000000000000000000000000 (by decide +kernel)
private def pv697 := integerPair bk1 bk308 1230759030096469470111703104060339405189684141 3553130911616000000000000000000000000000000000 (by decide +kernel)
private def pv698 := integerPair bk312 bk395 1423923741437956865692786599426127348136180161 2202093196160000000000000000000000000000000000 (by decide +kernel)
private def pv699 := integerPair bk318 bk395 58599094867230966998300677407916968621362761 77651596704000000000000000000000000000000000 (by decide +kernel)
private def pv700 := integerPair bk320 bk395 165653439385619509512600748050692172622155241 77651596704000000000000000000000000000000000 (by decide +kernel)
private def pv701 := integerPair bk321 bk395 65229041246279388109824930379899111181573 42764736000000000000000000000000000000000 (by decide +kernel)
private def pv702 := integerPair bk324 bk395 55716488451754747237834832152609600776823 42764736000000000000000000000000000000000 (by decide +kernel)
private def pv703 := integerPair bk601 bk584 269925102805225046794947197575560336952031 956194810445000000000000000000000000000000 (by decide +kernel)
private def pv704 := integerPair bk1104 bk584 670188483833233981792904948345176120070767 2190209530260500000000000000000000000000000 (by decide +kernel)
private def pv705 := integerPair bk1106 bk584 8861200330124042608795455993180791113012781 10951047651302500000000000000000000000000000 (by decide +kernel)
private def pv706 := integerPair bk1107 bk584 426539475592342311816720794619211213618309 730154646515000000000000000000000000000000 (by decide +kernel)
private def pv707 := integerPair bk601 bk585 4743170116830699682299044428609594966829 22035731840000000000000000000000000000000 (by decide +kernel)
private def pv708 := integerPair bk1104 bk585 4612861648605232936362637870322405905561 19322035295500000000000000000000000000000 (by decide +kernel)
private def pv709 := integerPair bk1106 bk585 10237108167727151236959663208714779441737 13801453782500000000000000000000000000000 (by decide +kernel)
private def pv710 := integerPair bk1107 bk585 13587535170099519821191732150314446441 26291537000000000000000000000000000000 (by decide +kernel)
private def pv711 := integerPair bk601 bk1100 1241210313682753895380699327149329201887 6977760070000000000000000000000000000000 (by decide +kernel)
private def pv712 := integerPair bk601 bk1099 7829688235435744628919707091251011263392051 118839688638825000000000000000000000000000000 (by decide +kernel)
private def pv713 := integerPair bk1104 bk1105 72403844968153819813999770002035048517138477 1537298459842862080000000000000000000000000000 (by decide +kernel)
private def pv714 := integerPair bk1106 bk1099 1376037796320863988072026247377107913647462429 2322841079432896000000000000000000000000000000 (by decide +kernel)
private def pv715 := integerPair bk1107 bk1108 3314960567799543283281026458799843892188124497 10975218454204928000000000000000000000000000000 (by decide +kernel)
private def pv716 := integerPair bk601 bk591 251065730381647404429057970125835650711269 3414981465875000000000000000000000000000000 (by decide +kernel)
private def pv717 := integerPair bk1104 bk591 5287946153039101608697686211639077320172853 54755238256512500000000000000000000000000000 (by decide +kernel)
private def pv718 := integerPair bk1106 bk591 4691319386832637872550334638416232840495369 7822176893787500000000000000000000000000000 (by decide +kernel)
private def pv719 := integerPair bk1107 bk591 27915704920902510933423649478270624923733 74505576175000000000000000000000000000000 (by decide +kernel)
private def pv720 := integerPair bk564 bk1100 173824691282223516417812163311487329987 395919616000000000000000000000000000000 (by decide +kernel)
private def pv721 := integerPair bk564 bk1099 10959310713606688566340107473278079075127 33547212160000000000000000000000000000000 (by decide +kernel)
private def pv722 := integerPair bk564 bk1105 3027578815300294263004302093150595257317301 10625317015040000000000000000000000000000000 (by decide +kernel)
private def pv723 := integerPair bk1116 bk395 9556106702208294841106885885456754792330477 1251181360000000000000000000000000000000000 (by decide +kernel)
private def pv724 := integerPair bk1121 bk395 1189049125931781980250177441647416617531710959 181325052480000000000000000000000000000000000 (by decide +kernel)
private def pv725 := integerPair bk1125 bk395 428975616123360612461581322561158096679117 62048272000000000000000000000000000000000 (by decide +kernel)
private def pv726 := integerPair bk1127 bk395 54175734171608272940684510019722614416521 5141875200000000000000000000000000000000 (by decide +kernel)
private def pv727 := integerPair bk1131 bk395 1676627526644953108428923099732677817520861 214244800000000000000000000000000000000000 (by decide +kernel)
private def pv728 := integerPair bk1135 bk395 489165662780071534070580665521170023099883 30606400000000000000000000000000000000000 (by decide +kernel)
private def pv729 := integerPair bk1136 bk395 2934738342647204648791246897519516836501 244851200000000000000000000000000000000 (by decide +kernel)
private def pv730 := integerPair bk1 bk1141 1160676106784085562789414418122243727963476301 3637150239923200000000000000000000000000000000 (by decide +kernel)
private def pv731 := integerPair bk1 bk1143 9698719567486726275537311483205751015100653 34256378956800000000000000000000000000000000 (by decide +kernel)
private def pv732 := integerPair bk1 bk1142 243642967259990888380708507154417381694791 986249291456000000000000000000000000000000 (by decide +kernel)
private def pv733 := integerPair bk1 bk1146 114106764162844652628722064530327487676239 493124645728000000000000000000000000000000 (by decide +kernel)
private def pv734 := integerPair bk1 bk1148 54978364192147853632686846617457862730439579 244013839097600000000000000000000000000000000 (by decide +kernel)
private def pv735 := integerPair bk1 bk1144 406584047735278309266507018597573451819637019 1741491354803200000000000000000000000000000000 (by decide +kernel)
private def pv736 := integerPair bk1 bk1157 120566485080976440420849707874997593855828603 519592891417600000000000000000000000000000000 (by decide +kernel)
private def pv737 := integerPair bk1160 bk559 2186603354280210118231616265530952668135467369 778780126269600000000000000000000000000000000 (by decide +kernel)
private def pv738 := integerPair bk1122 bk559 8166075601516079421219231343772952995379349 2743253318400000000000000000000000000000000 (by decide +kernel)
private def pv739 := integerPair bk1124 bk559 8836349445342773081216982182823462097326349 1399619040000000000000000000000000000000000 (by decide +kernel)
private def pv740 := integerPair bk1123 bk559 145837734767548575761792444688589785765019 36784608000000000000000000000000000000000 (by decide +kernel)
private def pv741 := integerPair bk1164 bk559 17252253574178023426257731004843210599151176567 7165918231462400000000000000000000000000000000 (by decide +kernel)
private def pv742 := integerPair bk1169 bk559 15319500017153669757877793428751016995005300811 6013092530335800000000000000000000000000000000 (by decide +kernel)
private def pv743 := integerPair bk1 bk1174 218475727506470648285015097389424805199671504641 6267754578800000000000000000000000000000000000000 (by decide +kernel)

end State1Pairs17
set_option maxRecDepth 262144
set_option maxHeartbeats 0
private def state1ValidPairs := [State1Pairs17.pv001,
  State1Pairs17.pv002,
  State1Pairs17.pv003,
  State1Pairs17.pv004,
  State1Pairs17.pv005,
  State1Pairs17.pv006,
  State1Pairs17.pv007,
  State1Pairs17.pv008,
  State1Pairs17.pv009,
  State1Pairs17.pv010,
  State1Pairs17.pv011,
  State1Pairs17.pv012,
  State1Pairs17.pv013,
  State1Pairs17.pv014,
  State1Pairs17.pv015,
  State1Pairs17.pv016,
  State1Pairs17.pv017,
  State1Pairs17.pv018,
  State1Pairs17.pv019,
  State1Pairs17.pv020,
  State1Pairs17.pv021,
  State1Pairs17.pv022,
  State1Pairs17.pv023,
  State1Pairs17.pv024,
  State1Pairs17.pv025,
  State1Pairs17.pv026,
  State1Pairs17.pv027,
  State1Pairs17.pv028,
  State1Pairs17.pv029,
  State1Pairs17.pv030,
  State1Pairs17.pv031,
  State1Pairs17.pv032,
  State1Pairs17.pv033,
  State1Pairs17.pv034,
  State1Pairs17.pv035,
  State1Pairs17.pv036,
  State1Pairs17.pv037,
  State1Pairs17.pv038,
  State1Pairs17.pv039,
  State1Pairs17.pv040,
  State1Pairs17.pv041,
  State1Pairs17.pv042,
  State1Pairs17.pv043,
  State1Pairs17.pv044,
  State1Pairs17.pv045,
  State1Pairs17.pv046,
  State1Pairs17.pv047,
  State1Pairs17.pv048,
  State1Pairs17.pv049,
  State1Pairs17.pv050,
  State1Pairs17.pv051,
  State1Pairs17.pv052,
  State1Pairs17.pv053,
  State1Pairs17.pv054,
  State1Pairs17.pv055,
  State1Pairs17.pv056,
  State1Pairs17.pv057,
  State1Pairs17.pv058,
  State1Pairs17.pv059,
  State1Pairs17.pv060,
  State1Pairs17.pv061,
  State1Pairs17.pv062,
  State1Pairs17.pv063,
  State1Pairs17.pv064,
  State1Pairs17.pv065,
  State1Pairs17.pv066,
  State1Pairs17.pv067,
  State1Pairs17.pv068,
  State1Pairs17.pv069,
  State1Pairs17.pv070,
  State1Pairs17.pv071,
  State1Pairs17.pv072,
  State1Pairs17.pv073,
  State1Pairs17.pv074,
  State1Pairs17.pv075,
  State1Pairs17.pv076,
  State1Pairs17.pv077,
  State1Pairs17.pv078,
  State1Pairs17.pv079,
  State1Pairs17.pv080,
  State1Pairs17.pv081,
  State1Pairs17.pv082,
  State1Pairs17.pv083,
  State1Pairs17.pv084,
  State1Pairs17.pv085,
  State1Pairs17.pv086,
  State1Pairs17.pv087,
  State1Pairs17.pv088,
  State1Pairs17.pv089,
  State1Pairs17.pv090,
  State1Pairs17.pv091,
  State1Pairs17.pv092,
  State1Pairs17.pv093,
  State1Pairs17.pv094,
  State1Pairs17.pv095,
  State1Pairs17.pv096,
  State1Pairs17.pv097,
  State1Pairs17.pv098,
  State1Pairs17.pv099,
  State1Pairs17.pv100,
  State1Pairs17.pv101,
  State1Pairs17.pv102,
  State1Pairs17.pv103,
  State1Pairs17.pv104,
  State1Pairs17.pv105,
  State1Pairs17.pv106,
  State1Pairs17.pv107,
  State1Pairs17.pv108,
  State1Pairs17.pv109,
  State1Pairs17.pv110,
  State1Pairs17.pv111,
  State1Pairs17.pv112,
  State1Pairs17.pv113,
  State1Pairs17.pv114,
  State1Pairs17.pv115,
  State1Pairs17.pv116,
  State1Pairs17.pv117,
  State1Pairs17.pv118,
  State1Pairs17.pv119,
  State1Pairs17.pv120,
  State1Pairs17.pv121,
  State1Pairs17.pv122,
  State1Pairs17.pv123,
  State1Pairs17.pv124,
  State1Pairs17.pv125,
  State1Pairs17.pv126,
  State1Pairs17.pv127,
  State1Pairs17.pv128,
  State1Pairs17.pv129,
  State1Pairs17.pv130,
  State1Pairs17.pv131,
  State1Pairs17.pv132,
  State1Pairs17.pv133,
  State1Pairs17.pv134,
  State1Pairs17.pv135,
  State1Pairs17.pv136,
  State1Pairs17.pv137,
  State1Pairs17.pv138,
  State1Pairs17.pv139,
  State1Pairs17.pv140,
  State1Pairs17.pv141,
  State1Pairs17.pv142,
  State1Pairs17.pv143,
  State1Pairs17.pv144,
  State1Pairs17.pv145,
  State1Pairs17.pv146,
  State1Pairs17.pv147,
  State1Pairs17.pv148,
  State1Pairs17.pv149,
  State1Pairs17.pv150,
  State1Pairs17.pv151,
  State1Pairs17.pv152,
  State1Pairs17.pv153,
  State1Pairs17.pv154,
  State1Pairs17.pv155,
  State1Pairs17.pv156,
  State1Pairs17.pv157,
  State1Pairs17.pv158,
  State1Pairs17.pv159,
  State1Pairs17.pv160,
  State1Pairs17.pv161,
  State1Pairs17.pv162,
  State1Pairs17.pv163,
  State1Pairs17.pv164,
  State1Pairs17.pv165,
  State1Pairs17.pv166,
  State1Pairs17.pv167,
  State1Pairs17.pv168,
  State1Pairs17.pv169,
  State1Pairs17.pv170,
  State1Pairs17.pv171,
  State1Pairs17.pv172,
  State1Pairs17.pv173,
  State1Pairs17.pv174,
  State1Pairs17.pv175,
  State1Pairs17.pv176,
  State1Pairs17.pv177,
  State1Pairs17.pv178,
  State1Pairs17.pv179,
  State1Pairs17.pv180,
  State1Pairs17.pv181,
  State1Pairs17.pv182,
  State1Pairs17.pv183,
  State1Pairs17.pv184,
  State1Pairs17.pv185,
  State1Pairs17.pv186,
  State1Pairs17.pv187,
  State1Pairs17.pv188,
  State1Pairs17.pv189,
  State1Pairs17.pv190,
  State1Pairs17.pv191,
  State1Pairs17.pv192,
  State1Pairs17.pv193,
  State1Pairs17.pv194,
  State1Pairs17.pv195,
  State1Pairs17.pv196,
  State1Pairs17.pv197,
  State1Pairs17.pv198,
  State1Pairs17.pv199,
  State1Pairs17.pv200,
  State1Pairs17.pv201,
  State1Pairs17.pv202,
  State1Pairs17.pv203,
  State1Pairs17.pv204,
  State1Pairs17.pv205,
  State1Pairs17.pv206,
  State1Pairs17.pv207,
  State1Pairs17.pv208,
  State1Pairs17.pv209,
  State1Pairs17.pv210,
  State1Pairs17.pv211,
  State1Pairs17.pv212,
  State1Pairs17.pv213,
  State1Pairs17.pv214,
  State1Pairs17.pv215,
  State1Pairs17.pv216,
  State1Pairs17.pv217,
  State1Pairs17.pv218,
  State1Pairs17.pv219,
  State1Pairs17.pv220,
  State1Pairs17.pv221,
  State1Pairs17.pv222,
  State1Pairs17.pv223,
  State1Pairs17.pv224,
  State1Pairs17.pv225,
  State1Pairs17.pv226,
  State1Pairs17.pv227,
  State1Pairs17.pv228,
  State1Pairs17.pv229,
  State1Pairs17.pv230,
  State1Pairs17.pv231,
  State1Pairs17.pv232,
  State1Pairs17.pv233,
  State1Pairs17.pv234,
  State1Pairs17.pv235,
  State1Pairs17.pv236,
  State1Pairs17.pv237,
  State1Pairs17.pv238,
  State1Pairs17.pv239,
  State1Pairs17.pv240,
  State1Pairs17.pv241,
  State1Pairs17.pv242,
  State1Pairs17.pv243,
  State1Pairs17.pv244,
  State1Pairs17.pv245,
  State1Pairs17.pv246,
  State1Pairs17.pv247,
  State1Pairs17.pv248,
  State1Pairs17.pv249,
  State1Pairs17.pv250,
  State1Pairs17.pv251,
  State1Pairs17.pv252,
  State1Pairs17.pv253,
  State1Pairs17.pv254,
  State1Pairs17.pv255,
  State1Pairs17.pv256,
  State1Pairs17.pv257,
  State1Pairs17.pv258,
  State1Pairs17.pv259,
  State1Pairs17.pv260,
  State1Pairs17.pv261,
  State1Pairs17.pv262,
  State1Pairs17.pv263,
  State1Pairs17.pv264,
  State1Pairs17.pv265,
  State1Pairs17.pv266,
  State1Pairs17.pv267,
  State1Pairs17.pv268,
  State1Pairs17.pv269,
  State1Pairs17.pv270,
  State1Pairs17.pv271,
  State1Pairs17.pv272,
  State1Pairs17.pv273,
  State1Pairs17.pv274,
  State1Pairs17.pv275,
  State1Pairs17.pv276,
  State1Pairs17.pv277,
  State1Pairs17.pv278,
  State1Pairs17.pv279,
  State1Pairs17.pv280,
  State1Pairs17.pv281,
  State1Pairs17.pv282,
  State1Pairs17.pv283,
  State1Pairs17.pv284,
  State1Pairs17.pv285,
  State1Pairs17.pv286,
  State1Pairs17.pv287,
  State1Pairs17.pv288,
  State1Pairs17.pv289,
  State1Pairs17.pv290,
  State1Pairs17.pv291,
  State1Pairs17.pv292,
  State1Pairs17.pv293,
  State1Pairs17.pv294,
  State1Pairs17.pv295,
  State1Pairs17.pv296,
  State1Pairs17.pv297,
  State1Pairs17.pv298,
  State1Pairs17.pv299,
  State1Pairs17.pv300,
  State1Pairs17.pv301,
  State1Pairs17.pv302,
  State1Pairs17.pv303,
  State1Pairs17.pv304,
  State1Pairs17.pv305,
  State1Pairs17.pv306,
  State1Pairs17.pv307,
  State1Pairs17.pv308,
  State1Pairs17.pv309,
  State1Pairs17.pv310,
  State1Pairs17.pv311,
  State1Pairs17.pv312,
  State1Pairs17.pv313,
  State1Pairs17.pv314,
  State1Pairs17.pv315,
  State1Pairs17.pv316,
  State1Pairs17.pv317,
  State1Pairs17.pv318,
  State1Pairs17.pv319,
  State1Pairs17.pv320,
  State1Pairs17.pv321,
  State1Pairs17.pv322,
  State1Pairs17.pv323,
  State1Pairs17.pv324,
  State1Pairs17.pv325,
  State1Pairs17.pv326,
  State1Pairs17.pv327,
  State1Pairs17.pv328,
  State1Pairs17.pv329,
  State1Pairs17.pv330,
  State1Pairs17.pv331,
  State1Pairs17.pv332,
  State1Pairs17.pv333,
  State1Pairs17.pv334,
  State1Pairs17.pv335,
  State1Pairs17.pv336,
  State1Pairs17.pv337,
  State1Pairs17.pv338,
  State1Pairs17.pv339,
  State1Pairs17.pv340,
  State1Pairs17.pv341,
  State1Pairs17.pv342,
  State1Pairs17.pv343,
  State1Pairs17.pv344,
  State1Pairs17.pv345,
  State1Pairs17.pv346,
  State1Pairs17.pv347,
  State1Pairs17.pv348,
  State1Pairs17.pv349,
  State1Pairs17.pv350,
  State1Pairs17.pv351,
  State1Pairs17.pv352,
  State1Pairs17.pv353,
  State1Pairs17.pv354,
  State1Pairs17.pv355,
  State1Pairs17.pv356,
  State1Pairs17.pv357,
  State1Pairs17.pv358,
  State1Pairs17.pv359,
  State1Pairs17.pv360,
  State1Pairs17.pv361,
  State1Pairs17.pv362,
  State1Pairs17.pv363,
  State1Pairs17.pv364,
  State1Pairs17.pv365,
  State1Pairs17.pv366,
  State1Pairs17.pv367,
  State1Pairs17.pv368,
  State1Pairs17.pv369,
  State1Pairs17.pv370,
  State1Pairs17.pv371,
  State1Pairs17.pv372,
  State1Pairs17.pv373,
  State1Pairs17.pv374,
  State1Pairs17.pv375,
  State1Pairs17.pv376,
  State1Pairs17.pv377,
  State1Pairs17.pv378,
  State1Pairs17.pv379,
  State1Pairs17.pv380,
  State1Pairs17.pv381,
  State1Pairs17.pv382,
  State1Pairs17.pv383,
  State1Pairs17.pv384,
  State1Pairs17.pv385,
  State1Pairs17.pv386,
  State1Pairs17.pv387,
  State1Pairs17.pv388,
  State1Pairs17.pv389,
  State1Pairs17.pv390,
  State1Pairs17.pv391,
  State1Pairs17.pv392,
  State1Pairs17.pv393,
  State1Pairs17.pv394,
  State1Pairs17.pv395,
  State1Pairs17.pv396,
  State1Pairs17.pv397,
  State1Pairs17.pv398,
  State1Pairs17.pv399,
  State1Pairs17.pv400,
  State1Pairs17.pv401,
  State1Pairs17.pv402,
  State1Pairs17.pv403,
  State1Pairs17.pv404,
  State1Pairs17.pv405,
  State1Pairs17.pv406,
  State1Pairs17.pv407,
  State1Pairs17.pv408,
  State1Pairs17.pv409,
  State1Pairs17.pv410,
  State1Pairs17.pv411,
  State1Pairs17.pv412,
  State1Pairs17.pv413,
  State1Pairs17.pv414,
  State1Pairs17.pv415,
  State1Pairs17.pv416,
  State1Pairs17.pv417,
  State1Pairs17.pv418,
  State1Pairs17.pv419,
  State1Pairs17.pv420,
  State1Pairs17.pv421,
  State1Pairs17.pv422,
  State1Pairs17.pv423,
  State1Pairs17.pv424,
  State1Pairs17.pv425,
  State1Pairs17.pv426,
  State1Pairs17.pv427,
  State1Pairs17.pv428,
  State1Pairs17.pv429,
  State1Pairs17.pv430,
  State1Pairs17.pv431,
  State1Pairs17.pv432,
  State1Pairs17.pv433,
  State1Pairs17.pv434,
  State1Pairs17.pv435,
  State1Pairs17.pv436,
  State1Pairs17.pv437,
  State1Pairs17.pv438,
  State1Pairs17.pv439,
  State1Pairs17.pv440,
  State1Pairs17.pv441,
  State1Pairs17.pv442,
  State1Pairs17.pv443,
  State1Pairs17.pv444,
  State1Pairs17.pv445,
  State1Pairs17.pv446,
  State1Pairs17.pv447,
  State1Pairs17.pv448,
  State1Pairs17.pv449,
  State1Pairs17.pv450,
  State1Pairs17.pv451,
  State1Pairs17.pv452,
  State1Pairs17.pv453,
  State1Pairs17.pv454,
  State1Pairs17.pv455,
  State1Pairs17.pv456,
  State1Pairs17.pv457,
  State1Pairs17.pv458,
  State1Pairs17.pv459,
  State1Pairs17.pv460,
  State1Pairs17.pv461,
  State1Pairs17.pv462,
  State1Pairs17.pv463,
  State1Pairs17.pv464,
  State1Pairs17.pv465,
  State1Pairs17.pv466,
  State1Pairs17.pv467,
  State1Pairs17.pv468,
  State1Pairs17.pv469,
  State1Pairs17.pv470,
  State1Pairs17.pv471,
  State1Pairs17.pv472,
  State1Pairs17.pv473,
  State1Pairs17.pv474,
  State1Pairs17.pv475,
  State1Pairs17.pv476,
  State1Pairs17.pv477,
  State1Pairs17.pv478,
  State1Pairs17.pv479,
  State1Pairs17.pv480,
  State1Pairs17.pv481,
  State1Pairs17.pv482,
  State1Pairs17.pv483,
  State1Pairs17.pv484,
  State1Pairs17.pv485,
  State1Pairs17.pv486,
  State1Pairs17.pv487,
  State1Pairs17.pv488,
  State1Pairs17.pv489,
  State1Pairs17.pv490,
  State1Pairs17.pv491,
  State1Pairs17.pv492,
  State1Pairs17.pv493,
  State1Pairs17.pv494,
  State1Pairs17.pv495,
  State1Pairs17.pv496,
  State1Pairs17.pv497,
  State1Pairs17.pv498,
  State1Pairs17.pv499,
  State1Pairs17.pv500,
  State1Pairs17.pv501,
  State1Pairs17.pv502,
  State1Pairs17.pv503,
  State1Pairs17.pv504,
  State1Pairs17.pv505,
  State1Pairs17.pv506,
  State1Pairs17.pv507,
  State1Pairs17.pv508,
  State1Pairs17.pv509,
  State1Pairs17.pv510,
  State1Pairs17.pv511,
  State1Pairs17.pv512,
  State1Pairs17.pv513,
  State1Pairs17.pv514,
  State1Pairs17.pv515,
  State1Pairs17.pv516,
  State1Pairs17.pv517,
  State1Pairs17.pv518,
  State1Pairs17.pv519,
  State1Pairs17.pv520,
  State1Pairs17.pv521,
  State1Pairs17.pv522,
  State1Pairs17.pv523,
  State1Pairs17.pv524,
  State1Pairs17.pv525,
  State1Pairs17.pv526,
  State1Pairs17.pv527,
  State1Pairs17.pv528,
  State1Pairs17.pv529,
  State1Pairs17.pv530,
  State1Pairs17.pv531,
  State1Pairs17.pv532,
  State1Pairs17.pv533,
  State1Pairs17.pv534,
  State1Pairs17.pv535,
  State1Pairs17.pv536,
  State1Pairs17.pv537,
  State1Pairs17.pv538,
  State1Pairs17.pv539,
  State1Pairs17.pv540,
  State1Pairs17.pv541,
  State1Pairs17.pv542,
  State1Pairs17.pv543,
  State1Pairs17.pv544,
  State1Pairs17.pv545,
  State1Pairs17.pv546,
  State1Pairs17.pv547,
  State1Pairs17.pv548,
  State1Pairs17.pv549,
  State1Pairs17.pv550,
  State1Pairs17.pv551,
  State1Pairs17.pv552,
  State1Pairs17.pv553,
  State1Pairs17.pv554,
  State1Pairs17.pv555,
  State1Pairs17.pv556,
  State1Pairs17.pv557,
  State1Pairs17.pv558,
  State1Pairs17.pv559,
  State1Pairs17.pv560,
  State1Pairs17.pv561,
  State1Pairs17.pv562,
  State1Pairs17.pv563,
  State1Pairs17.pv564,
  State1Pairs17.pv565,
  State1Pairs17.pv566,
  State1Pairs17.pv567,
  State1Pairs17.pv568,
  State1Pairs17.pv569,
  State1Pairs17.pv570,
  State1Pairs17.pv571,
  State1Pairs17.pv572,
  State1Pairs17.pv573,
  State1Pairs17.pv574,
  State1Pairs17.pv575,
  State1Pairs17.pv576,
  State1Pairs17.pv577,
  State1Pairs17.pv578,
  State1Pairs17.pv579,
  State1Pairs17.pv580,
  State1Pairs17.pv581,
  State1Pairs17.pv582,
  State1Pairs17.pv583,
  State1Pairs17.pv584,
  State1Pairs17.pv585,
  State1Pairs17.pv586,
  State1Pairs17.pv587,
  State1Pairs17.pv588,
  State1Pairs17.pv589,
  State1Pairs17.pv590,
  State1Pairs17.pv591,
  State1Pairs17.pv592,
  State1Pairs17.pv593,
  State1Pairs17.pv594,
  State1Pairs17.pv595,
  State1Pairs17.pv596,
  State1Pairs17.pv597,
  State1Pairs17.pv598,
  State1Pairs17.pv599,
  State1Pairs17.pv600,
  State1Pairs17.pv601,
  State1Pairs17.pv602,
  State1Pairs17.pv603,
  State1Pairs17.pv604,
  State1Pairs17.pv605,
  State1Pairs17.pv606,
  State1Pairs17.pv607,
  State1Pairs17.pv608,
  State1Pairs17.pv609,
  State1Pairs17.pv610,
  State1Pairs17.pv611,
  State1Pairs17.pv612,
  State1Pairs17.pv613,
  State1Pairs17.pv614,
  State1Pairs17.pv615,
  State1Pairs17.pv616,
  State1Pairs17.pv617,
  State1Pairs17.pv618,
  State1Pairs17.pv619,
  State1Pairs17.pv620,
  State1Pairs17.pv621,
  State1Pairs17.pv622,
  State1Pairs17.pv623,
  State1Pairs17.pv624,
  State1Pairs17.pv625,
  State1Pairs17.pv626,
  State1Pairs17.pv627,
  State1Pairs17.pv628,
  State1Pairs17.pv629,
  State1Pairs17.pv630,
  State1Pairs17.pv631,
  State1Pairs17.pv632,
  State1Pairs17.pv633,
  State1Pairs17.pv634,
  State1Pairs17.pv635,
  State1Pairs17.pv636,
  State1Pairs17.pv637,
  State1Pairs17.pv638,
  State1Pairs17.pv639,
  State1Pairs17.pv640,
  State1Pairs17.pv641,
  State1Pairs17.pv642,
  State1Pairs17.pv643,
  State1Pairs17.pv644,
  State1Pairs17.pv645,
  State1Pairs17.pv646,
  State1Pairs17.pv647,
  State1Pairs17.pv648,
  State1Pairs17.pv649,
  State1Pairs17.pv650,
  State1Pairs17.pv651,
  State1Pairs17.pv652,
  State1Pairs17.pv653,
  State1Pairs17.pv654,
  State1Pairs17.pv655,
  State1Pairs17.pv656,
  State1Pairs17.pv657,
  State1Pairs17.pv658,
  State1Pairs17.pv659,
  State1Pairs17.pv660,
  State1Pairs17.pv661,
  State1Pairs17.pv662,
  State1Pairs17.pv663,
  State1Pairs17.pv664,
  State1Pairs17.pv665,
  State1Pairs17.pv666,
  State1Pairs17.pv667,
  State1Pairs17.pv668,
  State1Pairs17.pv669,
  State1Pairs17.pv670,
  State1Pairs17.pv671,
  State1Pairs17.pv672,
  State1Pairs17.pv673,
  State1Pairs17.pv674,
  State1Pairs17.pv675,
  State1Pairs17.pv676,
  State1Pairs17.pv677,
  State1Pairs17.pv678,
  State1Pairs17.pv679,
  State1Pairs17.pv680,
  State1Pairs17.pv681,
  State1Pairs17.pv682,
  State1Pairs17.pv683,
  State1Pairs17.pv684,
  State1Pairs17.pv685,
  State1Pairs17.pv686,
  State1Pairs17.pv687,
  State1Pairs17.pv688,
  State1Pairs17.pv689,
  State1Pairs17.pv690,
  State1Pairs17.pv691,
  State1Pairs17.pv692,
  State1Pairs17.pv693,
  State1Pairs17.pv694,
  State1Pairs17.pv695,
  State1Pairs17.pv696,
  State1Pairs17.pv697,
  State1Pairs17.pv698,
  State1Pairs17.pv699,
  State1Pairs17.pv700,
  State1Pairs17.pv701,
  State1Pairs17.pv702,
  State1Pairs17.pv703,
  State1Pairs17.pv704,
  State1Pairs17.pv705,
  State1Pairs17.pv706,
  State1Pairs17.pv707,
  State1Pairs17.pv708,
  State1Pairs17.pv709,
  State1Pairs17.pv710,
  State1Pairs17.pv711,
  State1Pairs17.pv712,
  State1Pairs17.pv713,
  State1Pairs17.pv714,
  State1Pairs17.pv715,
  State1Pairs17.pv716,
  State1Pairs17.pv717,
  State1Pairs17.pv718,
  State1Pairs17.pv719,
  State1Pairs17.pv720,
  State1Pairs17.pv721,
  State1Pairs17.pv722,
  State1Pairs17.pv723,
  State1Pairs17.pv724,
  State1Pairs17.pv725,
  State1Pairs17.pv726,
  State1Pairs17.pv727,
  State1Pairs17.pv728,
  State1Pairs17.pv729,
  State1Pairs17.pv730,
  State1Pairs17.pv731,
  State1Pairs17.pv732,
  State1Pairs17.pv733,
  State1Pairs17.pv734,
  State1Pairs17.pv735,
  State1Pairs17.pv736,
  State1Pairs17.pv737,
  State1Pairs17.pv738,
  State1Pairs17.pv739,
  State1Pairs17.pv740,
  State1Pairs17.pv741,
  State1Pairs17.pv742,
  State1Pairs17.pv743]
theorem solution : ∀ p ∈ lowerEarlyTerminalState1.pairs,
    lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p := by
  intro p hp
  have h : lowerEarlyTerminalState1.pairs = state1ValidPairs.map Subtype.val := by rfl
  rw [h] at hp
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
  exact v.property
#print axioms solution
