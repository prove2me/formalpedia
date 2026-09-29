-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal3_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:20:36.926347+00:00
-- url     : https://prove2.me/submissions/b86ae2e1-5bc4-4e85-bea7-b208744d115c

import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Tactic

set_option Elab.async false
set_option linter.all false

open Freiman
namespace Terminal3Pairs17
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

private def earlyRect : CertRectangle := ⟨(1/4),(1/3),(3/4),(4/5)⟩
private theorem bounds_length : lowerEarlyTerminalTerminal3.bounds.length = 1238 := by decide +kernel



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

private def rE : Fin 3 → ℤ := ![36,42,48]
private def rF : Fin 3 → ℤ := ![9,12,16]
private def sE : Fin 3 → ℤ := ![300,310,320]
private def sF : Fin 3 → ℤ := ![225,240,256]

private theorem r_blend_scaled (x y : IntField) (dx dy : ℤ)
    (hx : 0 < dx) (hy : 0 < dy) :
    productBlend (1/4) (1/3) (scaled x dx) (scaled y dy) =
      fun i => scaled (blendN 144 rE rF x y dx dy i) (144*dx*dy) := by
  funext i
  fin_cases i <;>
    apply field_ext <;>
    dsimp [productBlend, certQuadBlend, certProductCoefficients, certFieldAdd,
      certFieldScale, certFieldMul, scaled, blendN, addN, smulN, oneN, mulN, rE, rF] <;>
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
  lookup : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 id = b
  orient : b.lower = lo
  thresholdValid : certThresholdDataValid b.threshold
  cn : IntField
  cd : ℤ
  cdpos : 0 < cd
  cscaled : b.threshold.c = scaled cn cd
  xn : Fin 3 → IntField
  xd : Fin 3 → ℤ
  xdpos : ∀ i, 0 < xd i
  xscaled : productBlend (1/4) (1/3) b.threshold.x0 b.threshold.x1 =
    fun i => scaled (xn i) (xd i)
  yn : Fin 3 → IntField
  yd : Fin 3 → ℤ
  ydpos : ∀ i, 0 < yd i
  yscaled : productBlend (3/4) (4/5) b.threshold.y0 b.threshold.y1 =
    fun i => scaled (yn i) (yd i)
private def n1 : IntField := ⟨31,0,0,0⟩
private theorem pos1 : (0:ℤ) < 100 := by decide +kernel
private theorem cp1 : (⟨(31/100),0,0,0⟩ : CertField) = scaled n1 100 := by decide +kernel
private def n2 : IntField := ⟨2619,0,0,(-451)⟩
private theorem pos2 : (0:ℤ) < 1938 := by decide +kernel
private theorem cp2 : (⟨(873/646),0,0,(-451/1938)⟩ : CertField) = scaled n2 1938 := by decide +kernel
private def n3 : IntField := ⟨(-1),0,0,1⟩
private theorem pos3 : (0:ℤ) < 10 := by decide +kernel
private theorem cp3 : (⟨(-1/10),0,0,(1/10)⟩ : CertField) = scaled n3 10 := by decide +kernel
private def n4 : IntField := ⟨189,0,0,(-1)⟩
private theorem pos4 : (0:ℤ) < 510 := by decide +kernel
private theorem cp4 : (⟨(63/170),0,0,(-1/510)⟩ : CertField) = scaled n4 510 := by decide +kernel
private def n5 : IntField := ⟨4,1,0,0⟩
private theorem pos5 : (0:ℤ) < 13 := by decide +kernel
private theorem cp5 : (⟨(4/13),(1/13),0,0⟩ : CertField) = scaled n5 13 := by decide +kernel
private def n6 : IntField := ⟨9,(-1),0,0⟩
private theorem pos6 : (0:ℤ) < 13 := by decide +kernel
private theorem cp6 : (⟨(9/13),(-1/13),0,0⟩ : CertField) = scaled n6 13 := by decide +kernel
private def n7 : IntField := ⟨5,1,0,0⟩
private theorem pos7 : (0:ℤ) < 22 := by decide +kernel
private theorem cp7 : (⟨(5/22),(1/22),0,0⟩ : CertField) = scaled n7 22 := by decide +kernel
private def n8 : IntField := ⟨2,(-1),0,0⟩
private theorem pos8 : (0:ℤ) < 1 := by decide +kernel
private theorem cp8 : (⟨2,-1,0,0⟩ : CertField) = scaled n8 1 := by decide +kernel
private def n9 : IntField := ⟨27,0,0,1⟩
private theorem pos9 : (0:ℤ) < 118 := by decide +kernel
private theorem cp9 : (⟨(27/118),0,0,(1/118)⟩ : CertField) = scaled n9 118 := by decide +kernel
private def n10 : IntField := ⟨121,0,0,(-1)⟩
private theorem pos10 : (0:ℤ) < 430 := by decide +kernel
private theorem cp10 : (⟨(121/430),0,0,(-1/430)⟩ : CertField) = scaled n10 430 := by decide +kernel
private def n11 : IntField := ⟨49761,0,0,(-8569)⟩
private theorem pos11 : (0:ℤ) < 2550 := by decide +kernel
private theorem cp11 : (⟨(16587/850),0,0,(-8569/2550)⟩ : CertField) = scaled n11 2550 := by decide +kernel
private def n12 : IntField := ⟨153,0,0,0⟩
private theorem pos12 : (0:ℤ) < 250 := by decide +kernel
private theorem cp12 : (⟨(153/250),0,0,0⟩ : CertField) = scaled n12 250 := by decide +kernel
private def n13 : IntField := ⟨35,1,0,0⟩
private theorem pos13 : (0:ℤ) < 94 := by decide +kernel
private theorem cp13 : (⟨(35/94),(1/94),0,0⟩ : CertField) = scaled n13 94 := by decide +kernel
private def n14 : IntField := ⟨1635,0,0,(-299)⟩
private theorem pos14 : (0:ℤ) < 1938 := by decide +kernel
private theorem cp14 : (⟨(545/646),0,0,(-299/1938)⟩ : CertField) = scaled n14 1938 := by decide +kernel
private def n15 : IntField := ⟨41,0,0,1⟩
private theorem pos15 : (0:ℤ) < 166 := by decide +kernel
private theorem cp15 : (⟨(41/166),0,0,(1/166)⟩ : CertField) = scaled n15 166 := by decide +kernel
private def n16 : IntField := ⟨31,0,0,(-1)⟩
private theorem pos16 : (0:ℤ) < 94 := by decide +kernel
private theorem cp16 : (⟨(31/94),0,0,(-1/94)⟩ : CertField) = scaled n16 94 := by decide +kernel
private def n17 : IntField := ⟨31065,0,0,(-5681)⟩
private theorem pos17 : (0:ℤ) < 2550 := by decide +kernel
private theorem cp17 : (⟨(2071/170),0,0,(-5681/2550)⟩ : CertField) = scaled n17 2550 := by decide +kernel
private def n18 : IntField := ⟨7833,0,0,(-187)⟩
private theorem pos18 : (0:ℤ) < 29526 := by decide +kernel
private theorem cp18 : (⟨(373/1406),0,0,(-187/29526)⟩ : CertField) = scaled n18 29526 := by decide +kernel
private def n19 : IntField := ⟨21,0,0,1⟩
private theorem pos19 : (0:ℤ) < 70 := by decide +kernel
private theorem cp19 : (⟨(3/10),0,0,(1/70)⟩ : CertField) = scaled n19 70 := by decide +kernel
private def n20 : IntField := ⟨87,0,0,(-1)⟩
private theorem pos20 : (0:ℤ) < 222 := by decide +kernel
private theorem cp20 : (⟨(29/74),0,0,(-1/222)⟩ : CertField) = scaled n20 222 := by decide +kernel
private def n21 : IntField := ⟨148827,0,0,(-3553)⟩
private theorem pos21 : (0:ℤ) < 38850 := by decide +kernel
private theorem cp21 : (⟨(7087/1850),0,0,(-3553/38850)⟩ : CertField) = scaled n21 38850 := by decide +kernel
private def n22 : IntField := ⟨241,0,0,(-44)⟩
private theorem pos22 : (0:ℤ) < 323 := by decide +kernel
private theorem cp22 : (⟨(241/323),0,0,(-44/323)⟩ : CertField) = scaled n22 323 := by decide +kernel
private def n23 : IntField := ⟨39,0,0,1⟩
private theorem pos23 : (0:ℤ) < 150 := by decide +kernel
private theorem cp23 : (⟨(13/50),0,0,(1/150)⟩ : CertField) = scaled n23 150 := by decide +kernel
private def n24 : IntField := ⟨29,0,0,(-1)⟩
private theorem pos24 : (0:ℤ) < 82 := by decide +kernel
private theorem cp24 : (⟨(29/82),0,0,(-1/82)⟩ : CertField) = scaled n24 82 := by decide +kernel
private def n25 : IntField := ⟨4579,0,0,(-836)⟩
private theorem pos25 : (0:ℤ) < 425 := by decide +kernel
private theorem cp25 : (⟨(4579/425),0,0,(-836/425)⟩ : CertField) = scaled n25 425 := by decide +kernel
private def n26 : IntField := ⟨341,0,0,(-43)⟩
private theorem pos26 : (0:ℤ) < 646 := by decide +kernel
private theorem cp26 : (⟨(341/646),0,0,(-43/646)⟩ : CertField) = scaled n26 646 := by decide +kernel
private def n27 : IntField := ⟨117,0,0,1⟩
private theorem pos27 : (0:ℤ) < 402 := by decide +kernel
private theorem cp27 : (⟨(39/134),0,0,(1/402)⟩ : CertField) = scaled n27 402 := by decide +kernel
private def n28 : IntField := ⟨15,0,0,(-1)⟩
private theorem pos28 : (0:ℤ) < 34 := by decide +kernel
private theorem cp28 : (⟨(15/34),0,0,(-1/34)⟩ : CertField) = scaled n28 34 := by decide +kernel
private def n29 : IntField := ⟨6479,0,0,(-817)⟩
private theorem pos29 : (0:ℤ) < 850 := by decide +kernel
private theorem cp29 : (⟨(6479/850),0,0,(-817/850)⟩ : CertField) = scaled n29 850 := by decide +kernel
private def n30 : IntField := ⟨2317,0,0,(-53)⟩
private theorem pos30 : (0:ℤ) < 9842 := by decide +kernel
private theorem cp30 : (⟨(331/1406),0,0,(-53/9842)⟩ : CertField) = scaled n30 9842 := by decide +kernel
private def n31 : IntField := ⟨44023,0,0,(-1007)⟩
private theorem pos31 : (0:ℤ) < 12950 := by decide +kernel
private theorem cp31 : (⟨(6289/1850),0,0,(-1007/12950)⟩ : CertField) = scaled n31 12950 := by decide +kernel
private def n32 : IntField := ⟨49165,0,0,(-855)⟩
private theorem pos32 : (0:ℤ) < 233966 := by decide +kernel
private theorem cp32 : (⟨(49165/233966),0,0,(-45/12314)⟩ : CertField) = scaled n32 233966 := by decide +kernel
private def n33 : IntField := ⟨31,0,0,1⟩
private theorem pos33 : (0:ℤ) < 94 := by decide +kernel
private theorem cp33 : (⟨(31/94),0,0,(1/94)⟩ : CertField) = scaled n33 94 := by decide +kernel
private def n34 : IntField := ⟨105,0,0,(-1)⟩
private theorem pos34 : (0:ℤ) < 262 := by decide +kernel
private theorem cp34 : (⟨(105/262),0,0,(-1/262)⟩ : CertField) = scaled n34 262 := by decide +kernel
private def n35 : IntField := ⟨186827,0,0,(-3249)⟩
private theorem pos35 : (0:ℤ) < 61570 := by decide +kernel
private theorem cp35 : (⟨(186827/61570),0,0,(-3249/61570)⟩ : CertField) = scaled n35 61570 := by decide +kernel
private def n36 : IntField := ⟨106715,0,0,(-1955)⟩
private theorem pos36 : (0:ℤ) < 1101506 := by decide +kernel
private theorem cp36 : (⟨(15245/157358),0,0,(-1955/1101506)⟩ : CertField) = scaled n36 1101506 := by decide +kernel
private def n37 : IntField := ⟨217,0,0,1⟩
private theorem pos37 : (0:ℤ) < 574 := by decide +kernel
private theorem cp37 : (⟨(31/82),0,0,(1/574)⟩ : CertField) = scaled n37 574 := by decide +kernel
private def n38 : IntField := ⟨83,0,0,(-1)⟩
private theorem pos38 : (0:ℤ) < 202 := by decide +kernel
private theorem cp38 : (⟨(83/202),0,0,(-1/202)⟩ : CertField) = scaled n38 202 := by decide +kernel
private def n39 : IntField := ⟨405517,0,0,(-7429)⟩
private theorem pos39 : (0:ℤ) < 289870 := by decide +kernel
private theorem cp39 : (⟨(57931/41410),0,0,(-7429/289870)⟩ : CertField) = scaled n39 289870 := by decide +kernel
private def n40 : IntField := ⟨43635,0,0,(-715)⟩
private theorem pos40 : (0:ℤ) < 233966 := by decide +kernel
private theorem cp40 : (⟨(43635/233966),0,0,(-715/233966)⟩ : CertField) = scaled n40 233966 := by decide +kernel
private def n41 : IntField := ⟨165813,0,0,(-2717)⟩
private theorem pos41 : (0:ℤ) < 61570 := by decide +kernel
private theorem cp41 : (⟨(165813/61570),0,0,(-2717/61570)⟩ : CertField) = scaled n41 61570 := by decide +kernel
private def n42 : IntField := ⟨25575,0,0,2470⟩
private theorem pos42 : (0:ℤ) < 116983 := by decide +kernel
private theorem cp42 : (⟨(25575/116983),0,0,(130/6157)⟩ : CertField) = scaled n42 116983 := by decide +kernel
private def n43 : IntField := ⟨97185,0,0,9386⟩
private theorem pos43 : (0:ℤ) < 30785 := by decide +kernel
private theorem cp43 : (⟨(19437/6157),0,0,(9386/30785)⟩ : CertField) = scaled n43 30785 := by decide +kernel
private def n44 : IntField := ⟨1155,0,0,(-20)⟩
private theorem pos44 : (0:ℤ) < 13433 := by decide +kernel
private theorem cp44 : (⟨(165/1919),0,0,(-20/13433)⟩ : CertField) = scaled n44 13433 := by decide +kernel
private def n45 : IntField := ⟨4389,0,0,(-76)⟩
private theorem pos45 : (0:ℤ) < 3535 := by decide +kernel
private theorem cp45 : (⟨(627/505),0,0,(-76/3535)⟩ : CertField) = scaled n45 3535 := by decide +kernel
private def n46 : IntField := ⟨33845,0,0,(-5605)⟩
private theorem pos46 : (0:ℤ) < 180082 := by decide +kernel
private theorem cp46 : (⟨(4835/25726),0,0,(-295/9478)⟩ : CertField) = scaled n46 180082 := by decide +kernel
private def n47 : IntField := ⟨523,0,0,1⟩
private theorem pos47 : (0:ℤ) < 1354 := by decide +kernel
private theorem cp47 : (⟨(523/1354),0,0,(1/1354)⟩ : CertField) = scaled n47 1354 := by decide +kernel
private def n48 : IntField := ⟨21,0,0,(-1)⟩
private theorem pos48 : (0:ℤ) < 42 := by decide +kernel
private theorem cp48 : (⟨(1/2),0,0,(-1/42)⟩ : CertField) = scaled n48 42 := by decide +kernel
private def n49 : IntField := ⟨128611,0,0,(-21299)⟩
private theorem pos49 : (0:ℤ) < 47390 := by decide +kernel
private theorem cp49 : (⟨(18373/6770),0,0,(-21299/47390)⟩ : CertField) = scaled n49 47390 := by decide +kernel
private def n50 : IntField := ⟨110775,0,0,10615⟩
private theorem pos50 : (0:ℤ) < 1101506 := by decide +kernel
private theorem cp50 : (⟨(15825/157358),0,0,(10615/1101506)⟩ : CertField) = scaled n50 1101506 := by decide +kernel
private def n51 : IntField := ⟨420945,0,0,40337⟩
private theorem pos51 : (0:ℤ) < 289870 := by decide +kernel
private theorem cp51 : (⟨(12027/8282),0,0,(40337/289870)⟩ : CertField) = scaled n51 289870 := by decide +kernel
private def n52 : IntField := ⟨(-14207442),10860688,0,0⟩
private theorem pos52 : (0:ℤ) < 15174291 := by decide +kernel
private theorem cp52 : (⟨(-4735814/5058097),(10860688/15174291),0,0⟩ : CertField) = scaled n52 15174291 := by decide +kernel
private def n53 : IntField := ⟨4519,(-1),0,0⟩
private theorem pos53 : (0:ℤ) < 12598 := by decide +kernel
private theorem cp53 : (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = scaled n53 12598 := by decide +kernel
private def n54 : IntField := ⟨271,(-1),0,0⟩
private theorem pos54 : (0:ℤ) < 1006 := by decide +kernel
private theorem cp54 : (⟨(271/1006),(-1/1006),0,0⟩ : CertField) = scaled n54 1006 := by decide +kernel
private def n55 : IntField := ⟨13485,0,0,665⟩
private theorem pos55 : (0:ℤ) < 47838 := by decide +kernel
private theorem cp55 : (⟨(4495/15946),0,0,(95/6834)⟩ : CertField) = scaled n55 47838 := by decide +kernel
private def n56 : IntField := ⟨7469552,(-2765481),0,0⟩
private theorem pos56 : (0:ℤ) < 7968235 := by decide +kernel
private theorem cp56 : (⟨(7469552/7968235),(-2765481/7968235),0,0⟩ : CertField) = scaled n56 7968235 := by decide +kernel
private def n57 : IntField := ⟨83,0,0,1⟩
private theorem pos57 : (0:ℤ) < 202 := by decide +kernel
private theorem cp57 : (⟨(83/202),0,0,(1/202)⟩ : CertField) = scaled n57 202 := by decide +kernel
private def n58 : IntField := ⟨9,0,0,(-1)⟩
private theorem pos58 : (0:ℤ) < 10 := by decide +kernel
private theorem cp58 : (⟨(9/10),0,0,(-1/10)⟩ : CertField) = scaled n58 10 := by decide +kernel
private def n59 : IntField := ⟨89,1,0,0⟩
private theorem pos59 : (0:ℤ) < 214 := by decide +kernel
private theorem cp59 : (⟨(89/214),(1/214),0,0⟩ : CertField) = scaled n59 214 := by decide +kernel
private def n60 : IntField := ⟨18879,0,0,931⟩
private theorem pos60 : (0:ℤ) < 34170 := by decide +kernel
private theorem cp60 : (⟨(6293/11390),0,0,(931/34170)⟩ : CertField) = scaled n60 34170 := by decide +kernel
private def n61 : IntField := ⟨75,0,0,(-5)⟩
private theorem pos61 : (0:ℤ) < 102 := by decide +kernel
private theorem cp61 : (⟨(25/34),0,0,(-5/102)⟩ : CertField) = scaled n61 102 := by decide +kernel
private def n62 : IntField := ⟨(-35971057),60750714,0,0⟩
private theorem pos62 : (0:ℤ) < 197265783 := by decide +kernel
private theorem cp62 : (⟨(-35971057/197265783),(20250238/65755261),0,0⟩ : CertField) = scaled n62 197265783 := by decide +kernel
private def n63 : IntField := ⟨126,1,0,0⟩
private theorem pos63 : (0:ℤ) < 429 := by decide +kernel
private theorem cp63 : (⟨(42/143),(1/429),0,0⟩ : CertField) = scaled n63 429 := by decide +kernel
private def n64 : IntField := ⟨(-3),0,0,1⟩
private theorem pos64 : (0:ℤ) < 6 := by decide +kernel
private theorem cp64 : (⟨(-1/2),0,0,(1/6)⟩ : CertField) = scaled n64 6 := by decide +kernel
private def n65 : IntField := ⟨677899,177747,0,0⟩
private theorem pos65 : (0:ℤ) < 922502 := by decide +kernel
private theorem cp65 : (⟨(677899/922502),(177747/922502),0,0⟩ : CertField) = scaled n65 922502 := by decide +kernel
private def n66 : IntField := ⟨83,1,0,0⟩
private theorem pos66 : (0:ℤ) < 313 := by decide +kernel
private theorem cp66 : (⟨(83/313),(1/313),0,0⟩ : CertField) = scaled n66 313 := by decide +kernel
private def n67 : IntField := ⟨15,(-1),0,0⟩
private theorem pos67 : (0:ℤ) < 37 := by decide +kernel
private theorem cp67 : (⟨(15/37),(-1/37),0,0⟩ : CertField) = scaled n67 37 := by decide +kernel
private def n68 : IntField := ⟨93,1,0,0⟩
private theorem pos68 : (0:ℤ) < 262 := by decide +kernel
private theorem cp68 : (⟨(93/262),(1/262),0,0⟩ : CertField) = scaled n68 262 := by decide +kernel
private def n69 : IntField := ⟨34471293,8562275,0,0⟩
private theorem pos69 : (0:ℤ) < 46454565 := by decide +kernel
private theorem cp69 : (⟨(11490431/15484855),(1712455/9290913),0,0⟩ : CertField) = scaled n69 46454565 := by decide +kernel
private def n70 : IntField := ⟨1590,1,0,0⟩
private theorem pos70 : (0:ℤ) < 5893 := by decide +kernel
private theorem cp70 : (⟨(1590/5893),(1/5893),0,0⟩ : CertField) = scaled n70 5893 := by decide +kernel
private def n71 : IntField := ⟨1759149,0,0,37499⟩
private theorem pos71 : (0:ℤ) < 1315290 := by decide +kernel
private theorem cp71 : (⟨(586383/438430),0,0,(37499/1315290)⟩ : CertField) = scaled n71 1315290 := by decide +kernel
private def n72 : IntField := ⟨1491,0,0,1⟩
private theorem pos72 : (0:ℤ) < 5530 := by decide +kernel
private theorem cp72 : (⟨(213/790),0,0,(1/5530)⟩ : CertField) = scaled n72 5530 := by decide +kernel
private def n73 : IntField := ⟨1859,0,0,1⟩
private theorem pos73 : (0:ℤ) < 5158 := by decide +kernel
private theorem cp73 : (⟨(1859/5158),0,0,(1/5158)⟩ : CertField) = scaled n73 5158 := by decide +kernel
private def n74 : IntField := ⟨59273105,13426007,0,0⟩
private theorem pos74 : (0:ℤ) < 77757764 := by decide +kernel
private theorem cp74 : (⟨(59273105/77757764),(1918001/11108252),0,0⟩ : CertField) = scaled n74 77757764 := by decide +kernel
private def n75 : IntField := ⟨1991,1,0,0⟩
private theorem pos75 : (0:ℤ) < 5521 := by decide +kernel
private theorem cp75 : (⟨(1991/5521),(1/5521),0,0⟩ : CertField) = scaled n75 5521 := by decide +kernel
private def n76 : IntField := ⟨1586290,3840344,0,0⟩
private theorem pos76 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp76 : (⟨(1586290/10727197),(3840344/10727197),0,0⟩ : CertField) = scaled n76 10727197 := by decide +kernel
private def n77 : IntField := ⟨133,(-1),0,0⟩
private theorem pos77 : (0:ℤ) < 478 := by decide +kernel
private theorem cp77 : (⟨(133/478),(-1/478),0,0⟩ : CertField) = scaled n77 478 := by decide +kernel
private def n78 : IntField := ⟨1256535,0,0,26785⟩
private theorem pos78 : (0:ℤ) < 1841406 := by decide +kernel
private theorem cp78 : (⟨(59835/87686),0,0,(26785/1841406)⟩ : CertField) = scaled n78 1841406 := by decide +kernel
private def n79 : IntField := ⟨2619,0,0,(-451)⟩
private theorem pos79 : (0:ℤ) < 510 := by decide +kernel
private theorem cp79 : (⟨(873/170),0,0,(-451/510)⟩ : CertField) = scaled n79 510 := by decide +kernel
private def n80 : IntField := ⟨615684,448863,0,0⟩
private theorem pos80 : (0:ℤ) < 1064531 := by decide +kernel
private theorem cp80 : (⟨(615684/1064531),(448863/1064531),0,0⟩ : CertField) = scaled n80 1064531 := by decide +kernel
private def n81 : IntField := ⟨241,0,0,(-44)⟩
private theorem pos81 : (0:ℤ) < 85 := by decide +kernel
private theorem cp81 : (⟨(241/85),0,0,(-44/85)⟩ : CertField) = scaled n81 85 := by decide +kernel
private def n82 : IntField := ⟨48,1,0,0⟩
private theorem pos82 : (0:ℤ) < 177 := by decide +kernel
private theorem cp82 : (⟨(16/59),(1/177),0,0⟩ : CertField) = scaled n82 177 := by decide +kernel
private def n83 : IntField := ⟨43,(-1),0,0⟩
private theorem pos83 : (0:ℤ) < 142 := by decide +kernel
private theorem cp83 : (⟨(43/142),(-1/142),0,0⟩ : CertField) = scaled n83 142 := by decide +kernel
private def n84 : IntField := ⟨61,1,0,0⟩
private theorem pos84 : (0:ℤ) < 169 := by decide +kernel
private theorem cp84 : (⟨(61/169),(1/169),0,0⟩ : CertField) = scaled n84 169 := by decide +kernel
private def n85 : IntField := ⟨210711,0,0,14399⟩
private theorem pos85 : (0:ℤ) < 458430 := by decide +kernel
private theorem cp85 : (⟨(70237/152810),0,0,(2057/65490)⟩ : CertField) = scaled n85 458430 := by decide +kernel
private def n86 : IntField := ⟨1089,0,0,1⟩
private theorem pos86 : (0:ℤ) < 2950 := by decide +kernel
private theorem cp86 : (⟨(1089/2950),0,0,(1/2950)⟩ : CertField) = scaled n86 2950 := by decide +kernel
private def n87 : IntField := ⟨725,0,0,1⟩
private theorem pos87 : (0:ℤ) < 2602 := by decide +kernel
private theorem cp87 : (⟨(725/2602),0,0,(1/2602)⟩ : CertField) = scaled n87 2602 := by decide +kernel
private def n88 : IntField := ⟨77513961,66212564,0,0⟩
private theorem pos88 : (0:ℤ) < 167131367 := by decide +kernel
private theorem cp88 : (⟨(77513961/167131367),(66212564/167131367),0,0⟩ : CertField) = scaled n88 167131367 := by decide +kernel
private def n89 : IntField := ⟨767,1,0,0⟩
private theorem pos89 : (0:ℤ) < 2749 := by decide +kernel
private theorem cp89 : (⟨(767/2749),(1/2749),0,0⟩ : CertField) = scaled n89 2749 := by decide +kernel
private def n90 : IntField := ⟨88747320,37227830,0,0⟩
private theorem pos90 : (0:ℤ) < 128644477 := by decide +kernel
private theorem cp90 : (⟨(88747320/128644477),(37227830/128644477),0,0⟩ : CertField) = scaled n90 128644477 := by decide +kernel
private def n91 : IntField := ⟨1161,1,0,0⟩
private theorem pos91 : (0:ℤ) < 3142 := by decide +kernel
private theorem cp91 : (⟨(1161/3142),(1/3142),0,0⟩ : CertField) = scaled n91 3142 := by decide +kernel
private def n92 : IntField := ⟨1384994,(-714779),0,0⟩
private theorem pos92 : (0:ℤ) < 867613 := by decide +kernel
private theorem cp92 : (⟨(1384994/867613),(-714779/867613),0,0⟩ : CertField) = scaled n92 867613 := by decide +kernel
private def n93 : IntField := ⟨198,(-1),0,0⟩
private theorem pos93 : (0:ℤ) < 537 := by decide +kernel
private theorem cp93 : (⟨(66/179),(-1/537),0,0⟩ : CertField) = scaled n93 537 := by decide +kernel
private def n94 : IntField := ⟨4949,0,0,(-451)⟩
private theorem pos94 : (0:ℤ) < 4214 := by decide +kernel
private theorem cp94 : (⟨(101/86),0,0,(-451/4214)⟩ : CertField) = scaled n94 4214 := by decide +kernel
private def n95 : IntField := ⟨20949305,(-9833499),0,0⟩
private theorem pos95 : (0:ℤ) < 22604836 := by decide +kernel
private theorem cp95 : (⟨(20949305/22604836),(-9833499/22604836),0,0⟩ : CertField) = scaled n95 22604836 := by decide +kernel
private def n96 : IntField := ⟨1851,0,0,(-1)⟩
private theorem pos96 : (0:ℤ) < 6718 := by decide +kernel
private theorem cp96 : (⟨(1851/6718),0,0,(-1/6718)⟩ : CertField) = scaled n96 6718 := by decide +kernel
private def n97 : IntField := ⟨2615,0,0,(-1)⟩
private theorem pos97 : (0:ℤ) < 7138 := by decide +kernel
private theorem cp97 : (⟨(2615/7138),0,0,(-1/7138)⟩ : CertField) = scaled n97 7138 := by decide +kernel
private def n98 : IntField := ⟨1950,(-1),0,0⟩
private theorem pos98 : (0:ℤ) < 7081 := by decide +kernel
private theorem cp98 : (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) = scaled n98 7081 := by decide +kernel
private def n99 : IntField := ⟨4949,0,0,(-451)⟩
private theorem pos99 : (0:ℤ) < 2150 := by decide +kernel
private theorem cp99 : (⟨(4949/2150),0,0,(-451/2150)⟩ : CertField) = scaled n99 2150 := by decide +kernel
private def n100 : IntField := ⟨7833,0,0,(-187)⟩
private theorem pos100 : (0:ℤ) < 7770 := by decide +kernel
private theorem cp100 : (⟨(373/370),0,0,(-187/7770)⟩ : CertField) = scaled n100 7770 := by decide +kernel
private def n101 : IntField := ⟨3510339,(-1718470),0,0⟩
private theorem pos101 : (0:ℤ) < 2796719 := by decide +kernel
private theorem cp101 : (⟨(3510339/2796719),(-1718470/2796719),0,0⟩ : CertField) = scaled n101 2796719 := by decide +kernel
private def n102 : IntField := ⟨2747,(-1),0,0⟩
private theorem pos102 : (0:ℤ) < 7501 := by decide +kernel
private theorem cp102 : (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = scaled n102 7501 := by decide +kernel
private def n103 : IntField := ⟨789249,0,0,121589⟩
private theorem pos103 : (0:ℤ) < 1841406 := by decide +kernel
private theorem cp103 : (⟨(263083/613802),0,0,(121589/1841406)⟩ : CertField) = scaled n103 1841406 := by decide +kernel
private def n104 : IntField := ⟨30157521,(-14005655),0,0⟩
private theorem pos104 : (0:ℤ) < 33907254 := by decide +kernel
private theorem cp104 : (⟨(10052507/11302418),(-14005655/33907254),0,0⟩ : CertField) = scaled n104 33907254 := by decide +kernel
private def n105 : IntField := ⟨1719,0,0,1⟩
private theorem pos105 : (0:ℤ) < 5794 := by decide +kernel
private theorem cp105 : (⟨(1719/5794),0,0,(1/5794)⟩ : CertField) = scaled n105 5794 := by decide +kernel
private def n106 : IntField := ⟨1809,1,0,0⟩
private theorem pos106 : (0:ℤ) < 6094 := by decide +kernel
private theorem cp106 : (⟨(1809/6094),(1/6094),0,0⟩ : CertField) = scaled n106 6094 := by decide +kernel
private def n107 : IntField := ⟨303972265,(-127591766),0,0⟩
private theorem pos107 : (0:ℤ) < 465908181 := by decide +kernel
private theorem cp107 : (⟨(303972265/465908181),(-127591766/465908181),0,0⟩ : CertField) = scaled n107 465908181 := by decide +kernel
private def n108 : IntField := ⟨338003377,(-141533453),0,0⟩
private theorem pos108 : (0:ℤ) < 473628142 := by decide +kernel
private theorem cp108 : (⟨(338003377/473628142),(-141533453/473628142),0,0⟩ : CertField) = scaled n108 473628142 := by decide +kernel
private def n109 : IntField := ⟨5524743,0,0,851123⟩
private theorem pos109 : (0:ℤ) < 6576450 := by decide +kernel
private theorem cp109 : (⟨(1841581/2192150),0,0,(851123/6576450)⟩ : CertField) = scaled n109 6576450 := by decide +kernel
private def n110 : IntField := ⟨2103,0,0,(-329)⟩
private theorem pos110 : (0:ℤ) < 510 := by decide +kernel
private theorem cp110 : (⟨(701/170),0,0,(-329/510)⟩ : CertField) = scaled n110 510 := by decide +kernel
private def n111 : IntField := ⟨30853093,(-13656585),0,0⟩
private theorem pos111 : (0:ℤ) < 36565583 := by decide +kernel
private theorem cp111 : (⟨(30853093/36565583),(-13656585/36565583),0,0⟩ : CertField) = scaled n111 36565583 := by decide +kernel
private def n112 : IntField := ⟨147,0,0,1⟩
private theorem pos112 : (0:ℤ) < 514 := by decide +kernel
private theorem cp112 : (⟨(147/514),0,0,(1/514)⟩ : CertField) = scaled n112 514 := by decide +kernel
private def n113 : IntField := ⟨245288306,(-86222743),0,0⟩
private theorem pos113 : (0:ℤ) < 476340838 := by decide +kernel
private theorem cp113 : (⟨(122644153/238170419),(-86222743/476340838),0,0⟩ : CertField) = scaled n113 476340838 := by decide +kernel
private def n114 : IntField := ⟨59241606,(-19341618),0,0⟩
private theorem pos114 : (0:ℤ) < 117867829 := by decide +kernel
private theorem cp114 : (⟨(59241606/117867829),(-19341618/117867829),0,0⟩ : CertField) = scaled n114 117867829 := by decide +kernel
private def n115 : IntField := ⟨1385355,3126197,0,0⟩
private theorem pos115 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp115 : (⟨(1385355/10727197),(3126197/10727197),0,0⟩ : CertField) = scaled n115 10727197 := by decide +kernel
private def n116 : IntField := ⟨71,(-1),0,0⟩
private theorem pos116 : (0:ℤ) < 229 := by decide +kernel
private theorem cp116 : (⟨(71/229),(-1/229),0,0⟩ : CertField) = scaled n116 229 := by decide +kernel
private def n117 : IntField := ⟨341,0,0,(-43)⟩
private theorem pos117 : (0:ℤ) < 170 := by decide +kernel
private theorem cp117 : (⟨(341/170),0,0,(-43/170)⟩ : CertField) = scaled n117 170 := by decide +kernel
private def n118 : IntField := ⟨295575,0,0,(-45425)⟩
private theorem pos118 : (0:ℤ) < 349762 := by decide +kernel
private theorem cp118 : (⟨(42225/49966),0,0,(-45425/349762)⟩ : CertField) = scaled n118 349762 := by decide +kernel
private def n119 : IntField := ⟨689,0,0,(-1)⟩
private theorem pos119 : (0:ℤ) < 2350 := by decide +kernel
private theorem cp119 : (⟨(689/2350),0,0,(-1/2350)⟩ : CertField) = scaled n119 2350 := by decide +kernel
private def n120 : IntField := ⟨35662395,(-15351928),0,0⟩
private theorem pos120 : (0:ℤ) < 32359620 := by decide +kernel
private theorem cp120 : (⟨(2377493/2157308),(-3837982/8089905),0,0⟩ : CertField) = scaled n120 32359620 := by decide +kernel
private def n121 : IntField := ⟨731,(-1),0,0⟩
private theorem pos121 : (0:ℤ) < 2497 := by decide +kernel
private theorem cp121 : (⟨(731/2497),(-1/2497),0,0⟩ : CertField) = scaled n121 2497 := by decide +kernel
private def n122 : IntField := ⟨3289,1,0,0⟩
private theorem pos122 : (0:ℤ) < 10753 := by decide +kernel
private theorem cp122 : (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = scaled n122 10753 := by decide +kernel
private def n123 : IntField := ⟨11823,0,0,(-1817)⟩
private theorem pos123 : (0:ℤ) < 7138 := by decide +kernel
private theorem cp123 : (⟨(11823/7138),0,0,(-1817/7138)⟩ : CertField) = scaled n123 7138 := by decide +kernel
private def n124 : IntField := ⟨(-5855080),4134061,0,0⟩
private theorem pos124 : (0:ℤ) < 5135331 := by decide +kernel
private theorem cp124 : (⟨(-5855080/5135331),(4134061/5135331),0,0⟩ : CertField) = scaled n124 5135331 := by decide +kernel
private def n125 : IntField := ⟨(-178397697),138588056,0,0⟩
private theorem pos125 : (0:ℤ) < 215196189 := by decide +kernel
private theorem cp125 : (⟨(-59465899/71732063),(138588056/215196189),0,0⟩ : CertField) = scaled n125 215196189 := by decide +kernel
private def n126 : IntField := ⟨2317,0,0,(-53)⟩
private theorem pos126 : (0:ℤ) < 2590 := by decide +kernel
private theorem cp126 : (⟨(331/370),0,0,(-53/2590)⟩ : CertField) = scaled n126 2590 := by decide +kernel
private def n127 : IntField := ⟨194397,139809,0,0⟩
private theorem pos127 : (0:ℤ) < 163774 := by decide +kernel
private theorem cp127 : (⟨(194397/163774),(139809/163774),0,0⟩ : CertField) = scaled n127 163774 := by decide +kernel
private def n128 : IntField := ⟨164975997,132610256,0,0⟩
private theorem pos128 : (0:ℤ) < 167131367 := by decide +kernel
private theorem cp128 : (⟨(164975997/167131367),(132610256/167131367),0,0⟩ : CertField) = scaled n128 167131367 := by decide +kernel
private def n129 : IntField := ⟨179334165,76652585,0,0⟩
private theorem pos129 : (0:ℤ) < 128644477 := by decide +kernel
private theorem cp129 : (⟨(179334165/128644477),(76652585/128644477),0,0⟩ : CertField) = scaled n129 128644477 := by decide +kernel
private def n130 : IntField := ⟨113317,(-58057),0,0⟩
private theorem pos130 : (0:ℤ) < 39923 := by decide +kernel
private theorem cp130 : (⟨(113317/39923),(-58057/39923),0,0⟩ : CertField) = scaled n130 39923 := by decide +kernel
private def n131 : IntField := ⟨96,(-1),0,0⟩
private theorem pos131 : (0:ℤ) < 249 := by decide +kernel
private theorem cp131 : (⟨(32/83),(-1/249),0,0⟩ : CertField) = scaled n131 249 := by decide +kernel
private def n132 : IntField := ⟨9833,0,0,(-171)⟩
private theorem pos132 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp132 : (⟨(9833/12314),0,0,(-171/12314)⟩ : CertField) = scaled n132 12314 := by decide +kernel
private def n133 : IntField := ⟨1520885,0,0,11855⟩
private theorem pos133 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp133 : (⟨(1520885/1160054),0,0,(11855/1160054)⟩ : CertField) = scaled n133 1160054 := by decide +kernel
private def n134 : IntField := ⟨859250,(-397911),0,0⟩
private theorem pos134 : (0:ℤ) < 520078 := by decide +kernel
private theorem cp134 : (⟨(429625/260039),(-397911/520078),0,0⟩ : CertField) = scaled n134 520078 := by decide +kernel
private def n135 : IntField := ⟨1341,0,0,(-1)⟩
private theorem pos135 : (0:ℤ) < 3526 := by decide +kernel
private theorem cp135 : (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) = scaled n135 3526 := by decide +kernel
private def n136 : IntField := ⟨2129239,0,0,16597⟩
private theorem pos136 : (0:ℤ) < 828610 := by decide +kernel
private theorem cp136 : (⟨(2129239/828610),0,0,(16597/828610)⟩ : CertField) = scaled n136 828610 := by decide +kernel
private def n137 : IntField := ⟨22927,0,0,121⟩
private theorem pos137 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp137 : (⟨(22927/12314),0,0,(121/12314)⟩ : CertField) = scaled n137 12314 := by decide +kernel
private def n138 : IntField := ⟨143862,(-68665),0,0⟩
private theorem pos138 : (0:ℤ) < 68783 := by decide +kernel
private theorem cp138 : (⟨(143862/68783),(-68665/68783),0,0⟩ : CertField) = scaled n138 68783 := by decide +kernel
private def n139 : IntField := ⟨1413,(-1),0,0⟩
private theorem pos139 : (0:ℤ) < 3718 := by decide +kernel
private theorem cp139 : (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = scaled n139 3718 := by decide +kernel
private def n140 : IntField := ⟨147,0,0,(-1)⟩
private theorem pos140 : (0:ℤ) < 514 := by decide +kernel
private theorem cp140 : (⟨(147/514),0,0,(-1/514)⟩ : CertField) = scaled n140 514 := by decide +kernel
private def n141 : IntField := ⟨182571,0,0,25714⟩
private theorem pos141 : (0:ℤ) < 229215 := by decide +kernel
private theorem cp141 : (⟨(60857/76405),0,0,(25714/229215)⟩ : CertField) = scaled n141 229215 := by decide +kernel
private def n142 : IntField := ⟨16084572,(-7364405),0,0⟩
private theorem pos142 : (0:ℤ) < 10141521 := by decide +kernel
private theorem cp142 : (⟨(5361524/3380507),(-7364405/10141521),0,0⟩ : CertField) = scaled n142 10141521 := by decide +kernel
private def n143 : IntField := ⟨325056155,(-133599949),0,0⟩
private theorem pos143 : (0:ℤ) < 278702463 := by decide +kernel
private theorem cp143 : (⟨(325056155/278702463),(-133599949/278702463),0,0⟩ : CertField) = scaled n143 278702463 := by decide +kernel
private def n144 : IntField := ⟨1075417,(-428303),0,0⟩
private theorem pos144 : (0:ℤ) < 896038 := by decide +kernel
private theorem cp144 : (⟨(1075417/896038),(-428303/896038),0,0⟩ : CertField) = scaled n144 896038 := by decide +kernel
private def n145 : IntField := ⟨1277997,0,0,179998⟩
private theorem pos145 : (0:ℤ) < 818625 := by decide +kernel
private theorem cp145 : (⟨(425999/272875),0,0,(179998/818625)⟩ : CertField) = scaled n145 818625 := by decide +kernel
private def n146 : IntField := ⟨6531,0,0,286⟩
private theorem pos146 : (0:ℤ) < 3885 := by decide +kernel
private theorem cp146 : (⟨(311/185),0,0,(286/3885)⟩ : CertField) = scaled n146 3885 := by decide +kernel
private def n147 : IntField := ⟨8166794,(-3688227),0,0⟩
private theorem pos147 : (0:ℤ) < 4824541 := by decide +kernel
private theorem cp147 : (⟨(8166794/4824541),(-3688227/4824541),0,0⟩ : CertField) = scaled n147 4824541 := by decide +kernel
private def n148 : IntField := ⟨129082073,(-47154571),0,0⟩
private theorem pos148 : (0:ℤ) < 125698852 := by decide +kernel
private theorem cp148 : (⟨(129082073/125698852),(-47154571/125698852),0,0⟩ : CertField) = scaled n148 125698852 := by decide +kernel
private def n149 : IntField := ⟨102212817,(-33339399),0,0⟩
private theorem pos149 : (0:ℤ) < 108058093 := by decide +kernel
private theorem cp149 : (⟨(102212817/108058093),(-33339399/108058093),0,0⟩ : CertField) = scaled n149 108058093 := by decide +kernel
private def n150 : IntField := ⟨1474639,754191,0,0⟩
private theorem pos150 : (0:ℤ) < 1510223 := by decide +kernel
private theorem cp150 : (⟨(1474639/1510223),(754191/1510223),0,0⟩ : CertField) = scaled n150 1510223 := by decide +kernel
private def n151 : IntField := ⟨193703,0,0,(-4748)⟩
private theorem pos151 : (0:ℤ) < 848225 := by decide +kernel
private theorem cp151 : (⟨(193703/848225),0,0,(-4748/848225)⟩ : CertField) = scaled n151 848225 := by decide +kernel
private def n152 : IntField := ⟨3539,0,0,1⟩
private theorem pos152 : (0:ℤ) < 9250 := by decide +kernel
private theorem cp152 : (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) = scaled n152 9250 := by decide +kernel
private def n153 : IntField := ⟨247,1,0,0⟩
private theorem pos153 : (0:ℤ) < 649 := by decide +kernel
private theorem cp153 : (⟨(247/649),(1/649),0,0⟩ : CertField) = scaled n153 649 := by decide +kernel
private def n154 : IntField := ⟨16314613,7455368,0,0⟩
private theorem pos154 : (0:ℤ) < 18238847 := by decide +kernel
private theorem cp154 : (⟨(16314613/18238847),(7455368/18238847),0,0⟩ : CertField) = scaled n154 18238847 := by decide +kernel
private def n155 : IntField := ⟨4877310,2214722,0,0⟩
private theorem pos155 : (0:ℤ) < 4868149 := by decide +kernel
private theorem cp155 : (⟨(4877310/4868149),(2214722/4868149),0,0⟩ : CertField) = scaled n155 4868149 := by decide +kernel
private def n156 : IntField := ⟨48731319,22981565,0,0⟩
private theorem pos156 : (0:ℤ) < 54716541 := by decide +kernel
private theorem cp156 : (⟨(16243773/18238847),(22981565/54716541),0,0⟩ : CertField) = scaled n156 54716541 := by decide +kernel
private def n157 : IntField := ⟨68144518,22261037,0,0⟩
private theorem pos157 : (0:ℤ) < 74581782 := by decide +kernel
private theorem cp157 : (⟨(34072259/37290891),(22261037/74581782),0,0⟩ : CertField) = scaled n157 74581782 := by decide +kernel
private def n158 : IntField := ⟨13109,0,0,(-176)⟩
private theorem pos158 : (0:ℤ) < 43885 := by decide +kernel
private theorem cp158 : (⟨(13109/43885),0,0,(-176/43885)⟩ : CertField) = scaled n158 43885 := by decide +kernel
private def n159 : IntField := ⟨251,0,0,1⟩
private theorem pos159 : (0:ℤ) < 670 := by decide +kernel
private theorem cp159 : (⟨(251/670),0,0,(1/670)⟩ : CertField) = scaled n159 670 := by decide +kernel
private def n160 : IntField := ⟨720674542,277946054,0,0⟩
private theorem pos160 : (0:ℤ) < 764299393 := by decide +kernel
private theorem cp160 : (⟨(720674542/764299393),(277946054/764299393),0,0⟩ : CertField) = scaled n160 764299393 := by decide +kernel
private def n161 : IntField := ⟨2667,0,0,(-253)⟩
private theorem pos161 : (0:ℤ) < 4690 := by decide +kernel
private theorem cp161 : (⟨(381/670),0,0,(-253/4690)⟩ : CertField) = scaled n161 4690 := by decide +kernel
private def n162 : IntField := ⟨251,0,0,(-1)⟩
private theorem pos162 : (0:ℤ) < 670 := by decide +kernel
private theorem cp162 : (⟨(251/670),0,0,(-1/670)⟩ : CertField) = scaled n162 670 := by decide +kernel
private def n163 : IntField := ⟨22700866,10519166,0,0⟩
private theorem pos163 : (0:ℤ) < 22704539 := by decide +kernel
private theorem cp163 : (⟨(22700866/22704539),(10519166/22704539),0,0⟩ : CertField) = scaled n163 22704539 := by decide +kernel
private def n164 : IntField := ⟨3734,1,0,0⟩
private theorem pos164 : (0:ℤ) < 9757 := by decide +kernel
private theorem cp164 : (⟨(3734/9757),(1/9757),0,0⟩ : CertField) = scaled n164 9757 := by decide +kernel
private def n165 : IntField := ⟨260311300,98013814,0,0⟩
private theorem pos165 : (0:ℤ) < 274200971 := by decide +kernel
private theorem cp165 : (⟨(260311300/274200971),(98013814/274200971),0,0⟩ : CertField) = scaled n165 274200971 := by decide +kernel
private def n166 : IntField := ⟨1355921,0,0,(-33236)⟩
private theorem pos166 : (0:ℤ) < 3029375 := by decide +kernel
private theorem cp166 : (⟨(1355921/3029375),0,0,(-33236/3029375)⟩ : CertField) = scaled n166 3029375 := by decide +kernel
private def n167 : IntField := ⟨75037587,30655035,0,0⟩
private theorem pos167 : (0:ℤ) < 73187257 := by decide +kernel
private theorem cp167 : (⟨(75037587/73187257),(30655035/73187257),0,0⟩ : CertField) = scaled n167 73187257 := by decide +kernel
private def n168 : IntField := ⟨671227,499219,0,0⟩
private theorem pos168 : (0:ℤ) < 1541891 := by decide +kernel
private theorem cp168 : (⟨(671227/1541891),(499219/1541891),0,0⟩ : CertField) = scaled n168 1541891 := by decide +kernel
private def n169 : IntField := ⟨570051,0,0,(-65341)⟩
private theorem pos169 : (0:ℤ) < 2693670 := by decide +kernel
private theorem cp169 : (⟨(190017/897890),0,0,(-65341/2693670)⟩ : CertField) = scaled n169 2693670 := by decide +kernel
private def n170 : IntField := ⟨7389,0,0,1⟩
private theorem pos170 : (0:ℤ) < 19050 := by decide +kernel
private theorem cp170 : (⟨(2463/6350),0,0,(1/19050)⟩ : CertField) = scaled n170 19050 := by decide +kernel
private def n171 : IntField := ⟨553,1,0,0⟩
private theorem pos171 : (0:ℤ) < 1429 := by decide +kernel
private theorem cp171 : (⟨(553/1429),(1/1429),0,0⟩ : CertField) = scaled n171 1429 := by decide +kernel
private def n172 : IntField := ⟨6116773,5788260,0,0⟩
private theorem pos172 : (0:ℤ) < 18621299 := by decide +kernel
private theorem cp172 : (⟨(6116773/18621299),(5788260/18621299),0,0⟩ : CertField) = scaled n172 18621299 := by decide +kernel
private def n173 : IntField := ⟨17121447,7927814,0,0⟩
private theorem pos173 : (0:ℤ) < 34534643 := by decide +kernel
private theorem cp173 : (⟨(17121447/34534643),(7927814/34534643),0,0⟩ : CertField) = scaled n173 34534643 := by decide +kernel
private def n174 : IntField := ⟨19320603,17076737,0,0⟩
private theorem pos174 : (0:ℤ) < 55863897 := by decide +kernel
private theorem cp174 : (⟨(6440201/18621299),(17076737/55863897),0,0⟩ : CertField) = scaled n174 55863897 := by decide +kernel
private def n175 : IntField := ⟨40953,0,0,(-3667)⟩
private theorem pos175 : (0:ℤ) < 178770 := by decide +kernel
private theorem cp175 : (⟨(13651/59590),0,0,(-3667/178770)⟩ : CertField) = scaled n175 178770 := by decide +kernel
private def n176 : IntField := ⟨681,0,0,1⟩
private theorem pos176 : (0:ℤ) < 1770 := by decide +kernel
private theorem cp176 : (⟨(227/590),0,0,(1/1770)⟩ : CertField) = scaled n176 1770 := by decide +kernel
private def n177 : IntField := ⟨12465754,26826693,0,0⟩
private theorem pos177 : (0:ℤ) < 76145694 := by decide +kernel
private theorem cp177 : (⟨(6232877/38072847),(8942231/25381898),0,0⟩ : CertField) = scaled n177 76145694 := by decide +kernel
private def n178 : IntField := ⟨258195,0,0,(-21175)⟩
private theorem pos178 : (0:ℤ) < 165722 := by decide +kernel
private theorem cp178 : (⟨(258195/165722),0,0,(-21175/165722)⟩ : CertField) = scaled n178 165722 := by decide +kernel
private def n179 : IntField := ⟨193668946,77221239,0,0⟩
private theorem pos179 : (0:ℤ) < 417072227 := by decide +kernel
private theorem cp179 : (⟨(193668946/417072227),(77221239/417072227),0,0⟩ : CertField) = scaled n179 417072227 := by decide +kernel
private def n180 : IntField := ⟨21343,0,0,(-391)⟩
private theorem pos180 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp180 : (⟨(3049/8282),0,0,(-391/57974)⟩ : CertField) = scaled n180 57974 := by decide +kernel
private def n181 : IntField := ⟨22564,15573,0,0⟩
private theorem pos181 : (0:ℤ) < 50713 := by decide +kernel
private theorem cp181 : (⟨(22564/50713),(15573/50713),0,0⟩ : CertField) = scaled n181 50713 := by decide +kernel
private def n182 : IntField := ⟨3990357,0,0,(-457387)⟩
private theorem pos182 : (0:ℤ) < 9620250 := by decide +kernel
private theorem cp182 : (⟨(1330119/3206750),0,0,(-457387/9620250)⟩ : CertField) = scaled n182 9620250 := by decide +kernel
private def n183 : IntField := ⟨7767,1,0,0⟩
private theorem pos183 : (0:ℤ) < 20022 := by decide +kernel
private theorem cp183 : (⟨(2589/6674),(1/20022),0,0⟩ : CertField) = scaled n183 20022 := by decide +kernel
private def n184 : IntField := ⟨30639607,24993995,0,0⟩
private theorem pos184 : (0:ℤ) < 86968894 := by decide +kernel
private theorem cp184 : (⟨(30639607/86968894),(24993995/86968894),0,0⟩ : CertField) = scaled n184 86968894 := by decide +kernel
private def n185 : IntField := ⟨574040,241790,0,0⟩
private theorem pos185 : (0:ℤ) < 1135849 := by decide +kernel
private theorem cp185 : (⟨(574040/1135849),(241790/1135849),0,0⟩ : CertField) = scaled n185 1135849 := by decide +kernel
private def n186 : IntField := ⟨922125,0,0,(-75625)⟩
private theorem pos186 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp186 : (⟨(922125/1160054),0,0,(-75625/1160054)⟩ : CertField) = scaled n186 1160054 := by decide +kernel
private def n187 : IntField := ⟨530634,(-271739),0,0⟩
private theorem pos187 : (0:ℤ) < 495541 := by decide +kernel
private theorem cp187 : (⟨(530634/495541),(-271739/495541),0,0⟩ : CertField) = scaled n187 495541 := by decide +kernel
private def n188 : IntField := ⟨177,(-1),0,0⟩
private theorem pos188 : (0:ℤ) < 454 := by decide +kernel
private theorem cp188 : (⟨(177/454),(-1/454),0,0⟩ : CertField) = scaled n188 454 := by decide +kernel
private def n189 : IntField := ⟨3143105,0,0,311040⟩
private theorem pos189 : (0:ℤ) < 7881307 := by decide +kernel
private theorem cp189 : (⟨(64145/160843),0,0,(311040/7881307)⟩ : CertField) = scaled n189 7881307 := by decide +kernel
private def n190 : IntField := ⟨8048625,(-3724019),0,0⟩
private theorem pos190 : (0:ℤ) < 12910852 := by decide +kernel
private theorem cp190 : (⟨(8048625/12910852),(-3724019/12910852),0,0⟩ : CertField) = scaled n190 12910852 := by decide +kernel
private def n191 : IntField := ⟨3035,0,0,(-1)⟩
private theorem pos191 : (0:ℤ) < 7846 := by decide +kernel
private theorem cp191 : (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) = scaled n191 7846 := by decide +kernel
private def n192 : IntField := ⟨628621,0,0,62208⟩
private theorem pos192 : (0:ℤ) < 804215 := by decide +kernel
private theorem cp192 : (⟨(628621/804215),0,0,(62208/804215)⟩ : CertField) = scaled n192 804215 := by decide +kernel
private def n193 : IntField := ⟨24871,0,0,108⟩
private theorem pos193 : (0:ℤ) < 28987 := by decide +kernel
private theorem cp193 : (⟨(3553/4141),0,0,(108/28987)⟩ : CertField) = scaled n193 28987 := by decide +kernel
private def n194 : IntField := ⟨11762541,(-5322545),0,0⟩
private theorem pos194 : (0:ℤ) < 18234599 := by decide +kernel
private theorem cp194 : (⟨(11762541/18234599),(-5322545/18234599),0,0⟩ : CertField) = scaled n194 18234599 := by decide +kernel
private def n195 : IntField := ⟨3230,(-1),0,0⟩
private theorem pos195 : (0:ℤ) < 8353 := by decide +kernel
private theorem cp195 : (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = scaled n195 8353 := by decide +kernel
private def n196 : IntField := ⟨566107,0,0,39413⟩
private theorem pos196 : (0:ℤ) < 1696450 := by decide +kernel
private theorem cp196 : (⟨(566107/1696450),0,0,(39413/1696450)⟩ : CertField) = scaled n196 1696450 := by decide +kernel
private def n197 : IntField := ⟨3863267,(-1767205),0,0⟩
private theorem pos197 : (0:ℤ) < 6455426 := by decide +kernel
private theorem cp197 : (⟨(3863267/6455426),(-1767205/6455426),0,0⟩ : CertField) = scaled n197 6455426 := by decide +kernel
private def n198 : IntField := ⟨117128745,(-48075646),0,0⟩
private theorem pos198 : (0:ℤ) < 266105517 := by decide +kernel
private theorem cp198 : (⟨(39042915/88701839),(-48075646/266105517),0,0⟩ : CertField) = scaled n198 266105517 := by decide +kernel
private def n199 : IntField := ⟨44781028,(-16029627),0,0⟩
private theorem pos199 : (0:ℤ) < 118771307 := by decide +kernel
private theorem cp199 : (⟨(44781028/118771307),(-16029627/118771307),0,0⟩ : CertField) = scaled n199 118771307 := by decide +kernel
private def n200 : IntField := ⟨3962749,0,0,275891⟩
private theorem pos200 : (0:ℤ) < 6058750 := by decide +kernel
private theorem cp200 : (⟨(3962749/6058750),0,0,(275891/6058750)⟩ : CertField) = scaled n200 6058750 := by decide +kernel
private def n201 : IntField := ⟨8727,0,0,(-143)⟩
private theorem pos201 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp201 : (⟨(8727/12314),0,0,(-143/12314)⟩ : CertField) = scaled n201 12314 := by decide +kernel
private def n202 : IntField := ⟨5839677,(-2780866),0,0⟩
private theorem pos202 : (0:ℤ) < 7449913 := by decide +kernel
private theorem cp202 : (⟨(5839677/7449913),(-2780866/7449913),0,0⟩ : CertField) = scaled n202 7449913 := by decide +kernel
private def n203 : IntField := ⟨90786309,(-36671293),0,0⟩
private theorem pos203 : (0:ℤ) < 194100436 := by decide +kernel
private theorem cp203 : (⟨(90786309/194100436),(-36671293/194100436),0,0⟩ : CertField) = scaled n203 194100436 := by decide +kernel
private def n204 : IntField := ⟨98170698,(-32019006),0,0⟩
private theorem pos204 : (0:ℤ) < 274137107 := by decide +kernel
private theorem cp204 : (⟨(98170698/274137107),(-32019006/274137107),0,0⟩ : CertField) = scaled n204 274137107 := by decide +kernel
private def n205 : IntField := ⟨14759,27704,0,0⟩
private theorem pos205 : (0:ℤ) < 63661 := by decide +kernel
private theorem cp205 : (⟨(14759/63661),(27704/63661),0,0⟩ : CertField) = scaled n205 63661 := by decide +kernel
private def n206 : IntField := ⟨1099455,0,0,(-119990)⟩
private theorem pos206 : (0:ℤ) < 580027 := by decide +kernel
private theorem cp206 : (⟨(157065/82861),0,0,(-119990/580027)⟩ : CertField) = scaled n206 580027 := by decide +kernel
private def n207 : IntField := ⟨1323,0,0,(-1)⟩
private theorem pos207 : (0:ℤ) < 4354 := by decide +kernel
private theorem cp207 : (⟨(189/622),0,0,(-1/4354)⟩ : CertField) = scaled n207 4354 := by decide +kernel
private def n208 : IntField := ⟨1539237,0,0,(-167986)⟩
private theorem pos208 : (0:ℤ) < 414305 := by decide +kernel
private theorem cp208 : (⟨(1539237/414305),0,0,(-167986/414305)⟩ : CertField) = scaled n208 414305 := by decide +kernel
private def n209 : IntField := ⟨5115,0,0,494⟩
private theorem pos209 : (0:ℤ) < 6157 := by decide +kernel
private theorem cp209 : (⟨(5115/6157),0,0,(494/6157)⟩ : CertField) = scaled n209 6157 := by decide +kernel
private def n210 : IntField := ⟨207759,1042741,0,0⟩
private theorem pos210 : (0:ℤ) < 2306487 := by decide +kernel
private theorem cp210 : (⟨(69253/768829),(1042741/2306487),0,0⟩ : CertField) = scaled n210 2306487 := by decide +kernel
private def n211 : IntField := ⟨262658,348954,0,0⟩
private theorem pos211 : (0:ℤ) < 957073 := by decide +kernel
private theorem cp211 : (⟨(262658/957073),(348954/957073),0,0⟩ : CertField) = scaled n211 957073 := by decide +kernel
private def n212 : IntField := ⟨(-24396960),17468351,0,0⟩
private theorem pos212 : (0:ℤ) < 32263737 := by decide +kernel
private theorem cp212 : (⟨(-8132320/10754579),(17468351/32263737),0,0⟩ : CertField) = scaled n212 32263737 := by decide +kernel
private def n213 : IntField := ⟨50354195,(-21235216),0,0⟩
private theorem pos213 : (0:ℤ) < 67768580 := by decide +kernel
private theorem cp213 : (⟨(10070839/13553716),(-5308804/16942145),0,0⟩ : CertField) = scaled n213 67768580 := by decide +kernel
private def n214 : IntField := ⟨(-448345431),402336023,0,0⟩
private theorem pos214 : (0:ℤ) < 1187220243 := by decide +kernel
private theorem cp214 : (⟨(-149448477/395740081),(402336023/1187220243),0,0⟩ : CertField) = scaled n214 1187220243 := by decide +kernel
private def n215 : IntField := ⟨1378579,1010248,0,0⟩
private theorem pos215 : (0:ℤ) < 1541891 := by decide +kernel
private theorem cp215 : (⟨(1378579/1541891),(1010248/1541891),0,0⟩ : CertField) = scaled n215 1541891 := by decide +kernel
private def n216 : IntField := ⟨341361,0,0,(-10376)⟩
private theorem pos216 : (0:ℤ) < 1346835 := by decide +kernel
private theorem cp216 : (⟨(113787/448945),0,0,(-10376/1346835)⟩ : CertField) = scaled n216 1346835 := by decide +kernel
private def n217 : IntField := ⟨11910457,11928891,0,0⟩
private theorem pos217 : (0:ℤ) < 18621299 := by decide +kernel
private theorem cp217 : (⟨(11910457/18621299),(11928891/18621299),0,0⟩ : CertField) = scaled n217 18621299 := by decide +kernel
private def n218 : IntField := ⟨1413,(-1),0,0⟩
private theorem pos218 : (0:ℤ) < 4654 := by decide +kernel
private theorem cp218 : (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = scaled n218 4654 := by decide +kernel
private def n219 : IntField := ⟨69347763,32526001,0,0⟩
private theorem pos219 : (0:ℤ) < 69069286 := by decide +kernel
private theorem cp219 : (⟨(69347763/69069286),(32526001/69069286),0,0⟩ : CertField) = scaled n219 69069286 := by decide +kernel
private def n220 : IntField := ⟨41275851,34140713,0,0⟩
private theorem pos220 : (0:ℤ) < 55863897 := by decide +kernel
private theorem cp220 : (⟨(13758617/18621299),(34140713/55863897),0,0⟩ : CertField) = scaled n220 55863897 := by decide +kernel
private def n221 : IntField := ⟨231,0,0,(-4)⟩
private theorem pos221 : (0:ℤ) < 707 := by decide +kernel
private theorem cp221 : (⟨(33/101),0,0,(-4/707)⟩ : CertField) = scaled n221 707 := by decide +kernel
private def n222 : IntField := ⟨12705500,27270561,0,0⟩
private theorem pos222 : (0:ℤ) < 38072847 := by decide +kernel
private theorem cp222 : (⟨(12705500/38072847),(9090187/12690949),0,0⟩ : CertField) = scaled n222 38072847 := by decide +kernel
private def n223 : IntField := ⟨388324822,163972491,0,0⟩
private theorem pos223 : (0:ℤ) < 417072227 := by decide +kernel
private theorem cp223 : (⟨(388324822/417072227),(163972491/417072227),0,0⟩ : CertField) = scaled n223 417072227 := by decide +kernel
private def n224 : IntField := ⟨6563101,4482897,0,0⟩
private theorem pos224 : (0:ℤ) < 7201246 := by decide +kernel
private theorem cp224 : (⟨(6563101/7201246),(4482897/7201246),0,0⟩ : CertField) = scaled n224 7201246 := by decide +kernel
private def n225 : IntField := ⟨2389527,0,0,(-72632)⟩
private theorem pos225 : (0:ℤ) < 4810125 := by decide +kernel
private theorem cp225 : (⟨(796509/1603375),0,0,(-72632/4810125)⟩ : CertField) = scaled n225 4810125 := by decide +kernel
private def n226 : IntField := ⟨30213209,25619932,0,0⟩
private theorem pos226 : (0:ℤ) < 43484447 := by decide +kernel
private theorem cp226 : (⟨(30213209/43484447),(25619932/43484447),0,0⟩ : CertField) = scaled n226 43484447 := by decide +kernel
private def n227 : IntField := ⟨82365655,35341555,0,0⟩
private theorem pos227 : (0:ℤ) < 80645279 := by decide +kernel
private theorem cp227 : (⟨(82365655/80645279),(35341555/80645279),0,0⟩ : CertField) = scaled n227 80645279 := by decide +kernel
private def n228 : IntField := ⟨2177375,0,0,83125⟩
private theorem pos228 : (0:ℤ) < 21903658 := by decide +kernel
private theorem cp228 : (⟨(2177375/21903658),0,0,(11875/3129094)⟩ : CertField) = scaled n228 21903658 := by decide +kernel
private def n229 : IntField := ⟨5409,0,0,(-1)⟩
private theorem pos229 : (0:ℤ) < 13866 := by decide +kernel
private theorem cp229 : (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) = scaled n229 13866 := by decide +kernel
private def n230 : IntField := ⟨6769,0,0,(-1121)⟩
private theorem pos230 : (0:ℤ) < 9478 := by decide +kernel
private theorem cp230 : (⟨(967/1354),0,0,(-1121/9478)⟩ : CertField) = scaled n230 9478 := by decide +kernel
private def n231 : IntField := ⟨(-784719),1774045,0,0⟩
private theorem pos231 : (0:ℤ) < 11144771 := by decide +kernel
private theorem cp231 : (⟨(-784719/11144771),(1774045/11144771),0,0⟩ : CertField) = scaled n231 11144771 := by decide +kernel
private def n232 : IntField := ⟨278,(-1),0,0⟩
private theorem pos232 : (0:ℤ) < 709 := by decide +kernel
private theorem cp232 : (⟨(278/709),(-1/709),0,0⟩ : CertField) = scaled n232 709 := by decide +kernel
private def n233 : IntField := ⟨(-3305591),5323257,0,0⟩
private theorem pos233 : (0:ℤ) < 26342186 := by decide +kernel
private theorem cp233 : (⟨(-3305591/26342186),(5323257/26342186),0,0⟩ : CertField) = scaled n233 26342186 := by decide +kernel
private def n234 : IntField := ⟨609665,0,0,23275⟩
private theorem pos234 : (0:ℤ) < 3129094 := by decide +kernel
private theorem cp234 : (⟨(609665/3129094),0,0,(23275/3129094)⟩ : CertField) = scaled n234 3129094 := by decide +kernel
private def n235 : IntField := ⟨(-6088),52493,0,0⟩
private theorem pos235 : (0:ℤ) < 366553 := by decide +kernel
private theorem cp235 : (⟨(-6088/366553),(52493/366553),0,0⟩ : CertField) = scaled n235 366553 := by decide +kernel
private def n236 : IntField := ⟨89059389,63877233,0,0⟩
private theorem pos236 : (0:ℤ) < 200296174 := by decide +kernel
private theorem cp236 : (⟨(89059389/200296174),(63877233/200296174),0,0⟩ : CertField) = scaled n236 200296174 := by decide +kernel
private def n237 : IntField := ⟨1007355,0,0,(-21065)⟩
private theorem pos237 : (0:ℤ) < 2251802 := by decide +kernel
private theorem cp237 : (⟨(1007355/2251802),0,0,(-21065/2251802)⟩ : CertField) = scaled n237 2251802 := by decide +kernel
private def n238 : IntField := ⟨13260,1,0,0⟩
private theorem pos238 : (0:ℤ) < 33937 := by decide +kernel
private theorem cp238 : (⟨(13260/33937),(1/33937),0,0⟩ : CertField) = scaled n238 33937 := by decide +kernel
private def n239 : IntField := ⟨392627001,373531548,0,0⟩
private theorem pos239 : (0:ℤ) < 1209480743 := by decide +kernel
private theorem cp239 : (⟨(392627001/1209480743),(373531548/1209480743),0,0⟩ : CertField) = scaled n239 1209480743 := by decide +kernel
private def n240 : IntField := ⟨22155,0,0,2123⟩
private theorem pos240 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp240 : (⟨(3165/8282),0,0,(2123/57974)⟩ : CertField) = scaled n240 57974 := by decide +kernel
private def n241 : IntField := ⟨1920033810,820805110,0,0⟩
private theorem pos241 : (0:ℤ) < 3685184893 := by decide +kernel
private theorem cp241 : (⟨(1920033810/3685184893),(820805110/3685184893),0,0⟩ : CertField) = scaled n241 3685184893 := by decide +kernel
private def n242 : IntField := ⟨(-94037445),66451517,0,0⟩
private theorem pos242 : (0:ℤ) < 221882259 := by decide +kernel
private theorem cp242 : (⟨(-31345815/73960753),(66451517/221882259),0,0⟩ : CertField) = scaled n242 221882259 := by decide +kernel
private def n243 : IntField := ⟨191109065,(-82168347),0,0⟩
private theorem pos243 : (0:ℤ) < 466054060 := by decide +kernel
private theorem cp243 : (⟨(38221813/93210812),(-82168347/466054060),0,0⟩ : CertField) = scaled n243 466054060 := by decide +kernel
private def n244 : IntField := ⟨(-138472771),129224168,0,0⟩
private theorem pos244 : (0:ℤ) < 773927823 := by decide +kernel
private theorem cp244 : (⟨(-138472771/773927823),(129224168/773927823),0,0⟩ : CertField) = scaled n244 773927823 := by decide +kernel
private def n245 : IntField := ⟨5787,(-1),0,0⟩
private theorem pos245 : (0:ℤ) < 14838 := by decide +kernel
private theorem cp245 : (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) = scaled n245 14838 := by decide +kernel
private def n246 : IntField := ⟨2569,0,0,(-176)⟩
private theorem pos246 : (0:ℤ) < 8911 := by decide +kernel
private theorem cp246 : (⟨(367/1273),0,0,(-176/8911)⟩ : CertField) = scaled n246 8911 := by decide +kernel
private def n247 : IntField := ⟨48811,0,0,(-3344)⟩
private theorem pos247 : (0:ℤ) < 11725 := by decide +kernel
private theorem cp247 : (⟨(6973/1675),0,0,(-3344/11725)⟩ : CertField) = scaled n247 11725 := by decide +kernel
private def n248 : IntField := ⟨14049,0,0,109⟩
private theorem pos248 : (0:ℤ) < 29526 := by decide +kernel
private theorem cp248 : (⟨(669/1406),0,0,(109/29526)⟩ : CertField) = scaled n248 29526 := by decide +kernel
private def n249 : IntField := ⟨(-576131),424264,0,0⟩
private theorem pos249 : (0:ℤ) < 539327 := by decide +kernel
private theorem cp249 : (⟨(-576131/539327),(424264/539327),0,0⟩ : CertField) = scaled n249 539327 := by decide +kernel
private def n250 : IntField := ⟨2569,0,0,(-176)⟩
private theorem pos250 : (0:ℤ) < 2345 := by decide +kernel
private theorem cp250 : (⟨(367/335),0,0,(-176/2345)⟩ : CertField) = scaled n250 2345 := by decide +kernel
private def n251 : IntField := ⟨443751,0,0,4831⟩
private theorem pos251 : (0:ℤ) < 349762 := by decide +kernel
private theorem cp251 : (⟨(63393/49966),0,0,(4831/349762)⟩ : CertField) = scaled n251 349762 := by decide +kernel
private def n252 : IntField := ⟨(-5445979),3737807,0,0⟩
private theorem pos252 : (0:ℤ) < 3423554 := by decide +kernel
private theorem cp252 : (⟨(-5445979/3423554),(3737807/3423554),0,0⟩ : CertField) = scaled n252 3423554 := by decide +kernel
private def n253 : IntField := ⟨3573,0,0,(-1)⟩
private theorem pos253 : (0:ℤ) < 13326 := by decide +kernel
private theorem cp253 : (⟨(1191/4442),0,0,(-1/13326)⟩ : CertField) = scaled n253 13326 := by decide +kernel
private def n254 : IntField := ⟨3753,(-1),0,0⟩
private theorem pos254 : (0:ℤ) < 14001 := by decide +kernel
private theorem cp254 : (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) = scaled n254 14001 := by decide +kernel
private def n255 : IntField := ⟨443751,0,0,4831⟩
private theorem pos255 : (0:ℤ) < 178450 := by decide +kernel
private theorem cp255 : (⟨(443751/178450),0,0,(4831/178450)⟩ : CertField) = scaled n255 178450 := by decide +kernel
private def n256 : IntField := ⟨8379,0,0,83⟩
private theorem pos256 : (0:ℤ) < 4690 := by decide +kernel
private theorem cp256 : (⟨(1197/670),0,0,(83/4690)⟩ : CertField) = scaled n256 4690 := by decide +kernel
private def n257 : IntField := ⟨(-17325864),14330533,0,0⟩
private theorem pos257 : (0:ℤ) < 22600513 := by decide +kernel
private theorem cp257 : (⟨(-17325864/22600513),(14330533/22600513),0,0⟩ : CertField) = scaled n257 22600513 := by decide +kernel
private def n258 : IntField := ⟨345,0,0,(-1)⟩
private theorem pos258 : (0:ℤ) < 1266 := by decide +kernel
private theorem cp258 : (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = scaled n258 1266 := by decide +kernel
private def n259 : IntField := ⟨30258120,(-14268851),0,0⟩
private theorem pos259 : (0:ℤ) < 16953627 := by decide +kernel
private theorem cp259 : (⟨(10086040/5651209),(-14268851/16953627),0,0⟩ : CertField) = scaled n259 16953627 := by decide +kernel
private def n260 : IntField := ⟨14271245,(-6156758),0,0⟩
private theorem pos260 : (0:ℤ) < 10786540 := by decide +kernel
private theorem cp260 : (⟨(2854249/2157308),(-3078379/5393270),0,0⟩ : CertField) = scaled n260 10786540 := by decide +kernel
private def n261 : IntField := ⟨338188789,(-144869352),0,0⟩
private theorem pos261 : (0:ℤ) < 236814071 := by decide +kernel
private theorem cp261 : (⟨(338188789/236814071),(-144869352/236814071),0,0⟩ : CertField) = scaled n261 236814071 := by decide +kernel
private def n262 : IntField := ⟨3078201,0,0,275471⟩
private theorem pos262 : (0:ℤ) < 6576450 := by decide +kernel
private theorem cp262 : (⟨(1026067/2192150),0,0,(275471/6576450)⟩ : CertField) = scaled n262 6576450 := by decide +kernel
private def n263 : IntField := ⟨1635,0,0,(-299)⟩
private theorem pos263 : (0:ℤ) < 510 := by decide +kernel
private theorem cp263 : (⟨(109/34),0,0,(-299/510)⟩ : CertField) = scaled n263 510 := by decide +kernel
private def n264 : IntField := ⟨(-9733651),10108657,0,0⟩
private theorem pos264 : (0:ℤ) < 22729957 := by decide +kernel
private theorem cp264 : (⟨(-9733651/22729957),(10108657/22729957),0,0⟩ : CertField) = scaled n264 22729957 := by decide +kernel
private def n265 : IntField := ⟨(-49334341),43021876,0,0⟩
private theorem pos265 : (0:ℤ) < 72142907 := by decide +kernel
private theorem cp265 : (⟨(-49334341/72142907),(43021876/72142907),0,0⟩ : CertField) = scaled n265 72142907 := by decide +kernel
private def n266 : IntField := ⟨(-120589494),278276430,0,0⟩
private theorem pos266 : (0:ℤ) < 952499483 := by decide +kernel
private theorem cp266 : (⟨(-120589494/952499483),(278276430/952499483),0,0⟩ : CertField) = scaled n266 952499483 := by decide +kernel
private def n267 : IntField := ⟨71202757,32270063,0,0⟩
private theorem pos267 : (0:ℤ) < 53963533 := by decide +kernel
private theorem cp267 : (⟨(71202757/53963533),(32270063/53963533),0,0⟩ : CertField) = scaled n267 53963533 := by decide +kernel
private def n268 : IntField := ⟨589435,0,0,(-43875)⟩
private theorem pos268 : (0:ℤ) < 1807526 := by decide +kernel
private theorem cp268 : (⟨(84205/258218),0,0,(-43875/1807526)⟩ : CertField) = scaled n268 1807526 := by decide +kernel
private def n269 : IntField := ⟨7081,0,0,1⟩
private theorem pos269 : (0:ℤ) < 19270 := by decide +kernel
private theorem cp269 : (⟨(7081/19270),0,0,(1/19270)⟩ : CertField) = scaled n269 19270 := by decide +kernel
private def n270 : IntField := ⟨483,1,0,0⟩
private theorem pos270 : (0:ℤ) < 1318 := by decide +kernel
private theorem cp270 : (⟨(483/1318),(1/1318),0,0⟩ : CertField) = scaled n270 1318 := by decide +kernel
private def n271 : IntField := ⟨831164429,287756229,0,0⟩
private theorem pos271 : (0:ℤ) < 651713437 := by decide +kernel
private theorem cp271 : (⟨(831164429/651713437),(287756229/651713437),0,0⟩ : CertField) = scaled n271 651713437 := by decide +kernel
private def n272 : IntField := ⟨20875,0,0,621⟩
private theorem pos272 : (0:ℤ) < 84286 := by decide +kernel
private theorem cp272 : (⟨(20875/84286),0,0,(621/84286)⟩ : CertField) = scaled n272 84286 := by decide +kernel
private def n273 : IntField := ⟨457,0,0,1⟩
private theorem pos273 : (0:ℤ) < 1258 := by decide +kernel
private theorem cp273 : (⟨(457/1258),0,0,(1/1258)⟩ : CertField) = scaled n273 1258 := by decide +kernel
private def n274 : IntField := ⟨2246128119,925182554,0,0⟩
private theorem pos274 : (0:ℤ) < 1666646111 := by decide +kernel
private theorem cp274 : (⟨(2246128119/1666646111),(925182554/1666646111),0,0⟩ : CertField) = scaled n274 1666646111 := by decide +kernel
private def n275 : IntField := ⟨825209,0,0,(-61425)⟩
private theorem pos275 : (0:ℤ) < 1291090 := by decide +kernel
private theorem cp275 : (⟨(825209/1291090),0,0,(-12285/258218)⟩ : CertField) = scaled n275 1291090 := by decide +kernel
private def n276 : IntField := ⟨7480,1,0,0⟩
private theorem pos276 : (0:ℤ) < 20353 := by decide +kernel
private theorem cp276 : (⟨(7480/20353),(1/20353),0,0⟩ : CertField) = scaled n276 20353 := by decide +kernel
private def n277 : IntField := ⟨643800,1183231,0,0⟩
private theorem pos277 : (0:ℤ) < 4600479 := by decide +kernel
private theorem cp277 : (⟨(214600/1533493),(1183231/4600479),0,0⟩ : CertField) = scaled n277 4600479 := by decide +kernel
private def n278 : IntField := ⟨(-1188771),16952696,0,0⟩
private theorem pos278 : (0:ℤ) < 55559631 := by decide +kernel
private theorem cp278 : (⟨(-396257/18519877),(16952696/55559631),0,0⟩ : CertField) = scaled n278 55559631 := by decide +kernel
private def n279 : IntField := ⟨23895000,30450956,0,0⟩
private theorem pos279 : (0:ℤ) < 142084293 := by decide +kernel
private theorem cp279 : (⟨(7965000/47361431),(30450956/142084293),0,0⟩ : CertField) = scaled n279 142084293 := by decide +kernel
private def n280 : IntField := ⟨266931,0,0,2071⟩
private theorem pos280 : (0:ℤ) < 38850 := by decide +kernel
private theorem cp280 : (⟨(12711/1850),0,0,(2071/38850)⟩ : CertField) = scaled n280 38850 := by decide +kernel
private def n281 : IntField := ⟨14049,0,0,109⟩
private theorem pos281 : (0:ℤ) < 7770 := by decide +kernel
private theorem cp281 : (⟨(669/370),0,0,(109/7770)⟩ : CertField) = scaled n281 7770 := by decide +kernel
private def n282 : IntField := ⟨1523676,1105007,0,0⟩
private theorem pos282 : (0:ℤ) < 1064531 := by decide +kernel
private theorem cp282 : (⟨(1523676/1064531),(1105007/1064531),0,0⟩ : CertField) = scaled n282 1064531 := by decide +kernel
private def n283 : IntField := ⟨178613577,166787020,0,0⟩
private theorem pos283 : (0:ℤ) < 167131367 := by decide +kernel
private theorem cp283 : (⟨(178613577/167131367),(166787020/167131367),0,0⟩ : CertField) = scaled n283 167131367 := by decide +kernel
private def n284 : IntField := ⟨218317480,92246870,0,0⟩
private theorem pos284 : (0:ℤ) < 128644477 := by decide +kernel
private theorem cp284 : (⟨(218317480/128644477),(92246870/128644477),0,0⟩ : CertField) = scaled n284 128644477 := by decide +kernel
private def n285 : IntField := ⟨22851,63275,0,0⟩
private theorem pos285 : (0:ℤ) < 90753 := by decide +kernel
private theorem cp285 : (⟨(7617/30251),(63275/90753),0,0⟩ : CertField) = scaled n285 90753 := by decide +kernel
private def n286 : IntField := ⟨(-291543),10761892,0,0⟩
private theorem pos286 : (0:ℤ) < 14248221 := by decide +kernel
private theorem cp286 : (⟨(-97181/4749407),(10761892/14248221),0,0⟩ : CertField) = scaled n286 14248221 := by decide +kernel
private def n287 : IntField := ⟨30400,57452,0,0⟩
private theorem pos287 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp287 : (⟨(30400/97513),(57452/97513),0,0⟩ : CertField) = scaled n287 97513 := by decide +kernel
private def n288 : IntField := ⟨124803,0,0,(-373)⟩
private theorem pos288 : (0:ℤ) < 91686 := by decide +kernel
private theorem cp288 : (⟨(5943/4366),0,0,(-373/91686)⟩ : CertField) = scaled n288 91686 := by decide +kernel
private def n289 : IntField := ⟨873621,0,0,(-2611)⟩
private theorem pos289 : (0:ℤ) < 327450 := by decide +kernel
private theorem cp289 : (⟨(291207/109150),0,0,(-2611/327450)⟩ : CertField) = scaled n289 327450 := by decide +kernel
private def n290 : IntField := ⟨74197,152797,0,0⟩
private theorem pos290 : (0:ℤ) < 700271 := by decide +kernel
private theorem cp290 : (⟨(74197/700271),(152797/700271),0,0⟩ : CertField) = scaled n290 700271 := by decide +kernel
private def n291 : IntField := ⟨344661,6029423,0,0⟩
private theorem pos291 : (0:ℤ) < 25371357 := by decide +kernel
private theorem cp291 : (⟨(114887/8457119),(6029423/25371357),0,0⟩ : CertField) = scaled n291 25371357 := by decide +kernel
private def n292 : IntField := ⟨(-24300),51497,0,0⟩
private theorem pos292 : (0:ℤ) < 147323 := by decide +kernel
private theorem cp292 : (⟨(-24300/147323),(51497/147323),0,0⟩ : CertField) = scaled n292 147323 := by decide +kernel
private def n293 : IntField := ⟨1361824,1917252,0,0⟩
private theorem pos293 : (0:ℤ) < 10527803 := by decide +kernel
private theorem cp293 : (⟨(1361824/10527803),(1917252/10527803),0,0⟩ : CertField) = scaled n293 10527803 := by decide +kernel
private def n294 : IntField := ⟨(-2406288),3511661,0,0⟩
private theorem pos294 : (0:ℤ) < 7660796 := by decide +kernel
private theorem cp294 : (⟨(-601572/1915199),(3511661/7660796),0,0⟩ : CertField) = scaled n294 7660796 := by decide +kernel
private def n295 : IntField := ⟨187203,1481141,0,0⟩
private theorem pos295 : (0:ℤ) < 5421097 := by decide +kernel
private theorem cp295 : (⟨(187203/5421097),(1481141/5421097),0,0⟩ : CertField) = scaled n295 5421097 := by decide +kernel
private def n296 : IntField := ⟨12775,0,0,(-1160)⟩
private theorem pos296 : (0:ℤ) < 90041 := by decide +kernel
private theorem cp296 : (⟨(1825/12863),0,0,(-1160/90041)⟩ : CertField) = scaled n296 90041 := by decide +kernel
private def n297 : IntField := ⟨48545,0,0,(-4408)⟩
private theorem pos297 : (0:ℤ) < 23695 := by decide +kernel
private theorem cp297 : (⟨(1387/677),0,0,(-4408/23695)⟩ : CertField) = scaled n297 23695 := by decide +kernel
private def n298 : IntField := ⟨4995615,15493577,0,0⟩
private theorem pos298 : (0:ℤ) < 51991484 := by decide +kernel
private theorem cp298 : (⟨(4995615/51991484),(15493577/51991484),0,0⟩ : CertField) = scaled n298 51991484 := by decide +kernel
private def n299 : IntField := ⟨5,0,0,0⟩
private theorem pos299 : (0:ℤ) < 7 := by decide +kernel
private theorem cp299 : (⟨(5/7),0,0,0⟩ : CertField) = scaled n299 7 := by decide +kernel
private def n300 : IntField := ⟨7,0,0,0⟩
private theorem pos300 : (0:ℤ) < 5 := by decide +kernel
private theorem cp300 : (⟨(7/5),0,0,0⟩ : CertField) = scaled n300 5 := by decide +kernel
private def n301 : IntField := ⟨1,0,0,0⟩
private theorem pos301 : (0:ℤ) < 1 := by decide +kernel
private theorem cp301 : (⟨1,0,0,0⟩ : CertField) = scaled n301 1 := by decide +kernel
private def n302 : IntField := ⟨30007,160632,0,0⟩
private theorem pos302 : (0:ℤ) < 547307 := by decide +kernel
private theorem cp302 : (⟨(30007/547307),(160632/547307),0,0⟩ : CertField) = scaled n302 547307 := by decide +kernel
private def n303 : IntField := ⟨2389135,0,0,11720⟩
private theorem pos303 : (0:ℤ) < 10951829 := by decide +kernel
private theorem cp303 : (⟨(341305/1564547),0,0,(11720/10951829)⟩ : CertField) = scaled n303 10951829 := by decide +kernel
private def n304 : IntField := ⟨2555,0,0,(-232)⟩
private theorem pos304 : (0:ℤ) < 4739 := by decide +kernel
private theorem cp304 : (⟨(365/677),0,0,(-232/4739)⟩ : CertField) = scaled n304 4739 := by decide +kernel
private def n305 : IntField := ⟨(-8563189),17479377,0,0⟩
private theorem pos305 : (0:ℤ) < 52684372 := by decide +kernel
private theorem cp305 : (⟨(-8563189/52684372),(17479377/52684372),0,0⟩ : CertField) = scaled n305 52684372 := by decide +kernel
private def n306 : IntField := ⟨3344789,0,0,16408⟩
private theorem pos306 : (0:ℤ) < 7822735 := by decide +kernel
private theorem cp306 : (⟨(3344789/7822735),0,0,(16408/7822735)⟩ : CertField) = scaled n306 7822735 := by decide +kernel
private def n307 : IntField := ⟨13014575,0,0,(-858600)⟩
private theorem pos307 : (0:ℤ) < 72486589 := by decide +kernel
private theorem cp307 : (⟨(1859225/10355227),0,0,(-858600/72486589)⟩ : CertField) = scaled n307 72486589 := by decide +kernel
private def n308 : IntField := ⟨11835,0,0,1⟩
private theorem pos308 : (0:ℤ) < 32926 := by decide +kernel
private theorem cp308 : (⟨(11835/32926),0,0,(1/32926)⟩ : CertField) = scaled n308 32926 := by decide +kernel
private def n309 : IntField := ⟨457,0,0,(-1)⟩
private theorem pos309 : (0:ℤ) < 1258 := by decide +kernel
private theorem cp309 : (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = scaled n309 1258 := by decide +kernel
private def n310 : IntField := ⟨3389547,0,0,533170⟩
private theorem pos310 : (0:ℤ) < 10028555 := by decide +kernel
private theorem cp310 : (⟨(3389547/10028555),0,0,(106634/2005711)⟩ : CertField) = scaled n310 10028555 := by decide +kernel
private def n311 : IntField := ⟨665,0,0,1⟩
private theorem pos311 : (0:ℤ) < 1858 := by decide +kernel
private theorem cp311 : (⟨(665/1858),0,0,(1/1858)⟩ : CertField) = scaled n311 1858 := by decide +kernel
private def n312 : IntField := ⟨10899,0,0,(-1)⟩
private theorem pos312 : (0:ℤ) < 30226 := by decide +kernel
private theorem cp312 : (⟨(1557/4318),0,0,(-1/30226)⟩ : CertField) = scaled n312 30226 := by decide +kernel
private def n313 : IntField := ⟨159387,0,0,16720⟩
private theorem pos313 : (0:ℤ) < 523027 := by decide +kernel
private theorem cp313 : (⟨(159387/523027),0,0,(16720/523027)⟩ : CertField) = scaled n313 523027 := by decide +kernel
private def n314 : IntField := ⟨411,0,0,(-1)⟩
private theorem pos314 : (0:ℤ) < 1126 := by decide +kernel
private theorem cp314 : (⟨(411/1126),0,0,(-1/1126)⟩ : CertField) = scaled n314 1126 := by decide +kernel
private def n315 : IntField := ⟨91003,0,0,3078⟩
private theorem pos315 : (0:ℤ) < 637177 := by decide +kernel
private theorem cp315 : (⟨(91003/637177),0,0,(3078/637177)⟩ : CertField) = scaled n315 637177 := by decide +kernel
private def n316 : IntField := ⟨723,0,0,1⟩
private theorem pos316 : (0:ℤ) < 2026 := by decide +kernel
private theorem cp316 : (⟨(723/2026),0,0,(1/2026)⟩ : CertField) = scaled n316 2026 := by decide +kernel
private def n317 : IntField := ⟨164831,0,0,5481⟩
private theorem pos317 : (0:ℤ) < 1046054 := by decide +kernel
private theorem cp317 : (⟨(164831/1046054),0,0,(5481/1046054)⟩ : CertField) = scaled n317 1046054 := by decide +kernel
private def n318 : IntField := ⟨(-1325497),3996240,0,0⟩
private theorem pos318 : (0:ℤ) < 22549813 := by decide +kernel
private theorem cp318 : (⟨(-1325497/22549813),(3996240/22549813),0,0⟩ : CertField) = scaled n318 22549813 := by decide +kernel
private def n319 : IntField := ⟨797,1,0,0⟩
private theorem pos319 : (0:ℤ) < 2221 := by decide +kernel
private theorem cp319 : (⟨(797/2221),(1/2221),0,0⟩ : CertField) = scaled n319 2221 := by decide +kernel
private def n320 : IntField := ⟨667,(-1),0,0⟩
private theorem pos320 : (0:ℤ) < 1846 := by decide +kernel
private theorem cp320 : (⟨(667/1846),(-1/1846),0,0⟩ : CertField) = scaled n320 1846 := by decide +kernel
private def n321 : IntField := ⟨(-11689311),23486732,0,0⟩
private theorem pos321 : (0:ℤ) < 106599116 := by decide +kernel
private theorem cp321 : (⟨(-11689311/106599116),(5871683/26649779),0,0⟩ : CertField) = scaled n321 106599116 := by decide +kernel
private def n322 : IntField := ⟨24985871,114593233,0,0⟩
private theorem pos322 : (0:ℤ) < 784259531 := by decide +kernel
private theorem cp322 : (⟨(24985871/784259531),(114593233/784259531),0,0⟩ : CertField) = scaled n322 784259531 := by decide +kernel
private def n323 : IntField := ⟨11574,(-1),0,0⟩
private theorem pos323 : (0:ℤ) < 32101 := by decide +kernel
private theorem cp323 : (⟨(11574/32101),(-1/32101),0,0⟩ : CertField) = scaled n323 32101 := by decide +kernel
private def n324 : IntField := ⟨3644081,0,0,(-240408)⟩
private theorem pos324 : (0:ℤ) < 10355227 := by decide +kernel
private theorem cp324 : (⟨(3644081/10355227),0,0,(-240408/10355227)⟩ : CertField) = scaled n324 10355227 := by decide +kernel
private def n325 : IntField := ⟨5981,0,0,(-1183)⟩
private theorem pos325 : (0:ℤ) < 1258 := by decide +kernel
private theorem cp325 : (⟨(5981/1258),0,0,(-1183/1258)⟩ : CertField) = scaled n325 1258 := by decide +kernel
private def n326 : IntField := ⟨8564475,21645893,0,0⟩
private theorem pos326 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp326 : (⟨(8564475/10727197),(21645893/10727197),0,0⟩ : CertField) = scaled n326 10727197 := by decide +kernel
private def n327 : IntField := ⟨660,1,0,0⟩
private theorem pos327 : (0:ℤ) < 2461 := by decide +kernel
private theorem cp327 : (⟨(660/2461),(1/2461),0,0⟩ : CertField) = scaled n327 2461 := by decide +kernel
private def n328 : IntField := ⟨525,(-1),0,0⟩
private theorem pos328 : (0:ℤ) < 1941 := by decide +kernel
private theorem cp328 : (⟨(175/647),(-1/1941),0,0⟩ : CertField) = scaled n328 1941 := by decide +kernel
private def n329 : IntField := ⟨19599,0,0,(-3569)⟩
private theorem pos329 : (0:ℤ) < 510 := by decide +kernel
private theorem cp329 : (⟨(6533/170),0,0,(-3569/510)⟩ : CertField) = scaled n329 510 := by decide +kernel
private def n330 : IntField := ⟨561,0,0,1⟩
private theorem pos330 : (0:ℤ) < 2098 := by decide +kernel
private theorem cp330 : (⟨(561/2098),0,0,(1/2098)⟩ : CertField) = scaled n330 2098 := by decide +kernel
private def n331 : IntField := ⟨299,0,0,(-1)⟩
private theorem pos331 : (0:ℤ) < 1090 := by decide +kernel
private theorem cp331 : (⟨(299/1090),0,0,(-1/1090)⟩ : CertField) = scaled n331 1090 := by decide +kernel
private def n332 : IntField := ⟨2012539,0,0,184759⟩
private theorem pos332 : (0:ℤ) < 613802 := by decide +kernel
private theorem cp332 : (⟨(2012539/613802),0,0,(184759/613802)⟩ : CertField) = scaled n332 613802 := by decide +kernel
private def n333 : IntField := ⟨9683,0,0,1⟩
private theorem pos333 : (0:ℤ) < 36034 := by decide +kernel
private theorem cp333 : (⟨(9683/36034),0,0,(1/36034)⟩ : CertField) = scaled n333 36034 := by decide +kernel
private def n334 : IntField := ⟨14087773,0,0,1293313⟩
private theorem pos334 : (0:ℤ) < 2192150 := by decide +kernel
private theorem cp334 : (⟨(14087773/2192150),0,0,(1293313/2192150)⟩ : CertField) = scaled n334 2192150 := by decide +kernel
private def n335 : IntField := ⟨7469,0,0,(-1363)⟩
private theorem pos335 : (0:ℤ) < 170 := by decide +kernel
private theorem cp335 : (⟨(7469/170),0,0,(-1363/170)⟩ : CertField) = scaled n335 170 := by decide +kernel
private def n336 : IntField := ⟨623,0,0,1⟩
private theorem pos336 : (0:ℤ) < 2338 := by decide +kernel
private theorem cp336 : (⟨(89/334),0,0,(1/2338)⟩ : CertField) = scaled n336 2338 := by decide +kernel
private def n337 : IntField := ⟨3979975,0,0,22280⟩
private theorem pos337 : (0:ℤ) < 72486589 := by decide +kernel
private theorem cp337 : (⟨(3979975/72486589),0,0,(22280/72486589)⟩ : CertField) = scaled n337 72486589 := by decide +kernel
private def n338 : IntField := ⟨49859,0,0,118⟩
private theorem pos338 : (0:ℤ) < 637177 := by decide +kernel
private theorem cp338 : (⟨(49859/637177),0,0,(118/637177)⟩ : CertField) = scaled n338 637177 := by decide +kernel
private def n339 : IntField := ⟨90343,0,0,161⟩
private theorem pos339 : (0:ℤ) < 1046054 := by decide +kernel
private theorem cp339 : (⟨(90343/1046054),0,0,(161/1046054)⟩ : CertField) = scaled n339 1046054 := by decide +kernel
private def n340 : IntField := ⟨(-967545),2108488,0,0⟩
private theorem pos340 : (0:ℤ) < 22549813 := by decide +kernel
private theorem cp340 : (⟨(-967545/22549813),(2108488/22549813),0,0⟩ : CertField) = scaled n340 22549813 := by decide +kernel
private def n341 : IntField := ⟨(-8792967),13057964,0,0⟩
private theorem pos341 : (0:ℤ) < 106599116 := by decide +kernel
private theorem cp341 : (⟨(-8792967/106599116),(3264491/26649779),0,0⟩ : CertField) = scaled n341 106599116 := by decide +kernel
private def n342 : IntField := ⟨5007399,58998601,0,0⟩
private theorem pos342 : (0:ℤ) < 784259531 := by decide +kernel
private theorem cp342 : (⟨(5007399/784259531),(58998601/784259531),0,0⟩ : CertField) = scaled n342 784259531 := by decide +kernel
private def n343 : IntField := ⟨5571965,0,0,31192⟩
private theorem pos343 : (0:ℤ) < 51776135 := by decide +kernel
private theorem cp343 : (⟨(1114393/10355227),0,0,(31192/51776135)⟩ : CertField) = scaled n343 51776135 := by decide +kernel
private def n344 : IntField := ⟨4177235,10328301,0,0⟩
private theorem pos344 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp344 : (⟨(4177235/10727197),(10328301/10727197),0,0⟩ : CertField) = scaled n344 10727197 := by decide +kernel
private def n345 : IntField := ⟨341,1,0,0⟩
private theorem pos345 : (0:ℤ) < 1237 := by decide +kernel
private theorem cp345 : (⟨(341/1237),(1/1237),0,0⟩ : CertField) = scaled n345 1237 := by decide +kernel
private def n346 : IntField := ⟨246,(-1),0,0⟩
private theorem pos346 : (0:ℤ) < 877 := by decide +kernel
private theorem cp346 : (⟨(246/877),(-1/877),0,0⟩ : CertField) = scaled n346 877 := by decide +kernel
private def n347 : IntField := ⟨2717,0,0,(-483)⟩
private theorem pos347 : (0:ℤ) < 170 := by decide +kernel
private theorem cp347 : (⟨(2717/170),0,0,(-483/170)⟩ : CertField) = scaled n347 170 := by decide +kernel
private def n348 : IntField := ⟨299,0,0,1⟩
private theorem pos348 : (0:ℤ) < 1090 := by decide +kernel
private theorem cp348 : (⟨(299/1090),0,0,(1/1090)⟩ : CertField) = scaled n348 1090 := by decide +kernel
private def n349 : IntField := ⟨117,0,0,(-1)⟩
private theorem pos349 : (0:ℤ) < 402 := by decide +kernel
private theorem cp349 : (⟨(39/134),0,0,(-1/402)⟩ : CertField) = scaled n349 402 := by decide +kernel
private def n350 : IntField := ⟨935011,0,0,100031⟩
private theorem pos350 : (0:ℤ) < 613802 := by decide +kernel
private theorem cp350 : (⟨(133573/87686),0,0,(100031/613802)⟩ : CertField) = scaled n350 613802 := by decide +kernel
private def n351 : IntField := ⟨4893,0,0,1⟩
private theorem pos351 : (0:ℤ) < 17682 := by decide +kernel
private theorem cp351 : (⟨(233/842),0,0,(1/17682)⟩ : CertField) = scaled n351 17682 := by decide +kernel
private def n352 : IntField := ⟨6545077,0,0,700217⟩
private theorem pos352 : (0:ℤ) < 2192150 := by decide +kernel
private theorem cp352 : (⟨(6545077/2192150),0,0,(700217/2192150)⟩ : CertField) = scaled n352 2192150 := by decide +kernel
private def n353 : IntField := ⟨3365,0,0,(-603)⟩
private theorem pos353 : (0:ℤ) < 170 := by decide +kernel
private theorem cp353 : (⟨(673/34),0,0,(-603/170)⟩ : CertField) = scaled n353 170 := by decide +kernel
private def n354 : IntField := ⟨345,0,0,1⟩
private theorem pos354 : (0:ℤ) < 1266 := by decide +kernel
private theorem cp354 : (⟨(115/422),0,0,(1/1266)⟩ : CertField) = scaled n354 1266 := by decide +kernel
private def n355 : IntField := ⟨177731,0,0,(-683)⟩
private theorem pos355 : (0:ℤ) < 1807526 := by decide +kernel
private theorem cp355 : (⟨(177731/1807526),0,0,(-683/1807526)⟩ : CertField) = scaled n355 1807526 := by decide +kernel
private def n356 : IntField := ⟨17885273,0,0,1618785⟩
private theorem pos356 : (0:ℤ) < 48468670 := by decide +kernel
private theorem cp356 : (⟨(17885273/48468670),0,0,(323757/9693734)⟩ : CertField) = scaled n356 48468670 := by decide +kernel
private def n357 : IntField := ⟨411,0,0,1⟩
private theorem pos357 : (0:ℤ) < 1126 := by decide +kernel
private theorem cp357 : (⟨(411/1126),0,0,(1/1126)⟩ : CertField) = scaled n357 1126 := by decide +kernel
private def n358 : IntField := ⟨6361,0,0,(-1)⟩
private theorem pos358 : (0:ℤ) < 17218 := by decide +kernel
private theorem cp358 : (⟨(6361/17218),0,0,(-1/17218)⟩ : CertField) = scaled n358 17218 := by decide +kernel
private def n359 : IntField := ⟨57343,0,0,(-103)⟩
private theorem pos359 : (0:ℤ) < 421430 := by decide +kernel
private theorem cp359 : (⟨(57343/421430),0,0,(-103/421430)⟩ : CertField) = scaled n359 421430 := by decide +kernel
private def n360 : IntField := ⟨25109,0,0,(-80)⟩
private theorem pos360 : (0:ℤ) < 161581 := by decide +kernel
private theorem cp360 : (⟨(3587/23083),0,0,(-80/161581)⟩ : CertField) = scaled n360 161581 := by decide +kernel
private def n361 : IntField := ⟨217,0,0,(-1)⟩
private theorem pos361 : (0:ℤ) < 574 := by decide +kernel
private theorem cp361 : (⟨(31/82),0,0,(-1/574)⟩ : CertField) = scaled n361 574 := by decide +kernel
private def n362 : IntField := ⟨(-562140),1215739,0,0⟩
private theorem pos362 : (0:ℤ) < 7488217 := by decide +kernel
private theorem cp362 : (⟨(-562140/7488217),(1215739/7488217),0,0⟩ : CertField) = scaled n362 7488217 := by decide +kernel
private def n363 : IntField := ⟨383,(-1),0,0⟩
private theorem pos363 : (0:ℤ) < 1033 := by decide +kernel
private theorem cp363 : (⟨(383/1033),(-1/1033),0,0⟩ : CertField) = scaled n363 1033 := by decide +kernel
private def n364 : IntField := ⟨(-5095416),7531157,0,0⟩
private theorem pos364 : (0:ℤ) < 35398844 := by decide +kernel
private theorem cp364 : (⟨(-1273854/8849711),(7531157/35398844),0,0⟩ : CertField) = scaled n364 35398844 := by decide +kernel
private def n365 : IntField := ⟨1707987,17165996,0,0⟩
private theorem pos365 : (0:ℤ) < 132663949 := by decide +kernel
private theorem cp365 : (⟨(1707987/132663949),(17165996/132663949),0,0⟩ : CertField) = scaled n365 132663949 := by decide +kernel
private def n366 : IntField := ⟨6760,(-1),0,0⟩
private theorem pos366 : (0:ℤ) < 18301 := by decide +kernel
private theorem cp366 : (⟨(6760/18301),(-1/18301),0,0⟩ : CertField) = scaled n366 18301 := by decide +kernel
private def n367 : IntField := ⟨1244117,0,0,(-4781)⟩
private theorem pos367 : (0:ℤ) < 6455450 := by decide +kernel
private theorem cp367 : (⟨(1244117/6455450),0,0,(-4781/6455450)⟩ : CertField) = scaled n367 6455450 := by decide +kernel
private def n368 : IntField := ⟨59979,170200,0,0⟩
private theorem pos368 : (0:ℤ) < 90753 := by decide +kernel
private theorem cp368 : (⟨(19993/30251),(170200/90753),0,0⟩ : CertField) = scaled n368 90753 := by decide +kernel
private def n369 : IntField := ⟨(-2681441),10850397,0,0⟩
private theorem pos369 : (0:ℤ) < 4749407 := by decide +kernel
private theorem cp369 : (⟨(-2681441/4749407),(10850397/4749407),0,0⟩ : CertField) = scaled n369 4749407 := by decide +kernel
private def n370 : IntField := ⟨4479,(-1),0,0⟩
private theorem pos370 : (0:ℤ) < 16062 := by decide +kernel
private theorem cp370 : (⟨(1493/5354),(-1/16062),0,0⟩ : CertField) = scaled n370 16062 := by decide +kernel
private def n371 : IntField := ⟨80450,154458,0,0⟩
private theorem pos371 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp371 : (⟨(80450/97513),(154458/97513),0,0⟩ : CertField) = scaled n371 97513 := by decide +kernel
private def n372 : IntField := ⟨6881,0,0,(-54)⟩
private theorem pos372 : (0:ℤ) < 1295 := by decide +kernel
private theorem cp372 : (⟨(983/185),0,0,(-54/1295)⟩ : CertField) = scaled n372 1295 := by decide +kernel
private def n373 : IntField := ⟨221921,0,0,19414⟩
private theorem pos373 : (0:ℤ) < 76405 := by decide +kernel
private theorem cp373 : (⟨(31703/10915),0,0,(19414/76405)⟩ : CertField) = scaled n373 76405 := by decide +kernel
private def n374 : IntField := ⟨1553447,0,0,135898⟩
private theorem pos374 : (0:ℤ) < 272875 := by decide +kernel
private theorem cp374 : (⟨(1553447/272875),0,0,(135898/272875)⟩ : CertField) = scaled n374 272875 := by decide +kernel
private def n375 : IntField := ⟨8393,0,0,(-102)⟩
private theorem pos375 : (0:ℤ) < 1295 := by decide +kernel
private theorem cp375 : (⟨(1199/185),0,0,(-102/1295)⟩ : CertField) = scaled n375 1295 := by decide +kernel
private def n376 : IntField := ⟨5562375,0,0,(-19750)⟩
private theorem pos376 : (0:ℤ) < 98279839 := by decide +kernel
private theorem cp376 : (⟨(794625/14039977),0,0,(-19750/98279839)⟩ : CertField) = scaled n376 98279839 := by decide +kernel
private def n377 : IntField := ⟨40107,0,0,112⟩
private theorem pos377 : (0:ℤ) < 523027 := by decide +kernel
private theorem cp377 : (⟨(40107/523027),0,0,(112/523027)⟩ : CertField) = scaled n377 523027 := by decide +kernel
private def n378 : IntField := ⟨(-51396),135985,0,0⟩
private theorem pos378 : (0:ℤ) < 1734601 := by decide +kernel
private theorem cp378 : (⟨(-51396/1734601),(135985/1734601),0,0⟩ : CertField) = scaled n378 1734601 := by decide +kernel
private def n379 : IntField := ⟨222495,0,0,(-790)⟩
private theorem pos379 : (0:ℤ) < 2005711 := by decide +kernel
private theorem cp379 : (⟨(222495/2005711),0,0,(-790/2005711)⟩ : CertField) = scaled n379 2005711 := by decide +kernel
private def n380 : IntField := ⟨(-2962082),5282779,0,0⟩
private theorem pos380 : (0:ℤ) < 53299558 := by decide +kernel
private theorem cp380 : (⟨(-1481041/26649779),(5282779/53299558),0,0⟩ : CertField) = scaled n380 53299558 := by decide +kernel
private def n381 : IntField := ⟨121599,1826912,0,0⟩
private theorem pos381 : (0:ℤ) < 27179581 := by decide +kernel
private theorem cp381 : (⟨(121599/27179581),(1826912/27179581),0,0⟩ : CertField) = scaled n381 27179581 := by decide +kernel
private def n382 : IntField := ⟨12510,1,0,0⟩
private theorem pos382 : (0:ℤ) < 34801 := by decide +kernel
private theorem cp382 : (⟨(12510/34801),(1/34801),0,0⟩ : CertField) = scaled n382 34801 := by decide +kernel
private def n383 : IntField := ⟨3680200,9241922,0,0⟩
private theorem pos383 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp383 : (⟨(3680200/10727197),(9241922/10727197),0,0⟩ : CertField) = scaled n383 10727197 := by decide +kernel
private def n384 : IntField := ⟨237,1,0,0⟩
private theorem pos384 : (0:ℤ) < 814 := by decide +kernel
private theorem cp384 : (⟨(237/814),(1/814),0,0⟩ : CertField) = scaled n384 814 := by decide +kernel
private def n385 : IntField := ⟨317,(-1),0,0⟩
private theorem pos385 : (0:ℤ) < 1069 := by decide +kernel
private theorem cp385 : (⟨(317/1069),(-1/1069),0,0⟩ : CertField) = scaled n385 1069 := by decide +kernel
private def n386 : IntField := ⟨1458747,0,0,50102⟩
private theorem pos386 : (0:ℤ) < 920703 := by decide +kernel
private theorem cp386 : (⟨(486249/306901),0,0,(50102/920703)⟩ : CertField) = scaled n386 920703 := by decide +kernel
private def n387 : IntField := ⟨4009,0,0,1⟩
private theorem pos387 : (0:ℤ) < 13690 := by decide +kernel
private theorem cp387 : (⟨(4009/13690),0,0,(1/13690)⟩ : CertField) = scaled n387 13690 := by decide +kernel
private def n388 : IntField := ⟨275,0,0,(-1)⟩
private theorem pos388 : (0:ℤ) < 922 := by decide +kernel
private theorem cp388 : (⟨(275/922),0,0,(-1/922)⟩ : CertField) = scaled n388 922 := by decide +kernel
private def n389 : IntField := ⟨10211229,0,0,350714⟩
private theorem pos389 : (0:ℤ) < 3288225 := by decide +kernel
private theorem cp389 : (⟨(3403743/1096075),0,0,(350714/3288225)⟩ : CertField) = scaled n389 3288225 := by decide +kernel
private def n390 : IntField := ⟨4023,0,0,(-728)⟩
private theorem pos390 : (0:ℤ) < 255 := by decide +kernel
private theorem cp390 : (⟨(1341/85),0,0,(-728/255)⟩ : CertField) = scaled n390 255 := by decide +kernel
private def n391 : IntField := ⟨121,0,0,1⟩
private theorem pos391 : (0:ℤ) < 430 := by decide +kernel
private theorem cp391 : (⟨(121/430),0,0,(1/430)⟩ : CertField) = scaled n391 430 := by decide +kernel
private def n392 : IntField := ⟨3592515,0,0,(-132425)⟩
private theorem pos392 : (0:ℤ) < 28079954 := by decide +kernel
private theorem cp392 : (⟨(3592515/28079954),0,0,(-132425/28079954)⟩ : CertField) = scaled n392 28079954 := by decide +kernel
private def n393 : IntField := ⟨98331,0,0,10955⟩
private theorem pos393 : (0:ℤ) < 1046054 := by decide +kernel
private theorem cp393 : (⟨(98331/1046054),0,0,(10955/1046054)⟩ : CertField) = scaled n393 1046054 := by decide +kernel
private def n394 : IntField := ⟨(-7420123),17398874,0,0⟩
private theorem pos394 : (0:ℤ) < 106599116 := by decide +kernel
private theorem cp394 : (⟨(-7420123/106599116),(8699437/53299558),0,0⟩ : CertField) = scaled n394 106599116 := by decide +kernel
private def n395 : IntField := ⟨5029521,0,0,(-185395)⟩
private theorem pos395 : (0:ℤ) < 20057110 := by decide +kernel
private theorem cp395 : (⟨(5029521/20057110),0,0,(-37079/4011422)⟩ : CertField) = scaled n395 20057110 := by decide +kernel
private def n396 : IntField := ⟨6671500,16958462,0,0⟩
private theorem pos396 : (0:ℤ) < 10727197 := by decide +kernel
private theorem cp396 : (⟨(6671500/10727197),(16958462/10727197),0,0⟩ : CertField) = scaled n396 10727197 := by decide +kernel
private def n397 : IntField := ⟨469,1,0,0⟩
private theorem pos397 : (0:ℤ) < 1549 := by decide +kernel
private theorem cp397 : (⟨(469/1549),(1/1549),0,0⟩ : CertField) = scaled n397 1549 := by decide +kernel
private def n398 : IntField := ⟨579,(-1),0,0⟩
private theorem pos398 : (0:ℤ) < 1894 := by decide +kernel
private theorem cp398 : (⟨(579/1894),(-1/1894),0,0⟩ : CertField) = scaled n398 1894 := by decide +kernel
private def n399 : IntField := ⟨5262903,0,0,216193⟩
private theorem pos399 : (0:ℤ) < 1841406 := by decide +kernel
private theorem cp399 : (⟨(1754301/613802),0,0,(216193/1841406)⟩ : CertField) = scaled n399 1841406 := by decide +kernel
private def n400 : IntField := ⟨7739,0,0,1⟩
private theorem pos400 : (0:ℤ) < 25486 := by decide +kernel
private theorem cp400 : (⟨(7739/25486),0,0,(1/25486)⟩ : CertField) = scaled n400 25486 := by decide +kernel
private def n401 : IntField := ⟨489,0,0,(-1)⟩
private theorem pos401 : (0:ℤ) < 1594 := by decide +kernel
private theorem cp401 : (⟨(489/1594),0,0,(-1/1594)⟩ : CertField) = scaled n401 1594 := by decide +kernel
private def n402 : IntField := ⟨36840321,0,0,1513351⟩
private theorem pos402 : (0:ℤ) < 6576450 := by decide +kernel
private theorem cp402 : (⟨(12280107/2192150),0,0,(1513351/6576450)⟩ : CertField) = scaled n402 6576450 := by decide +kernel
private def n403 : IntField := ⟨15903,0,0,(-2911)⟩
private theorem pos403 : (0:ℤ) < 510 := by decide +kernel
private theorem cp403 : (⟨(5301/170),0,0,(-2911/510)⟩ : CertField) = scaled n403 510 := by decide +kernel
private def n404 : IntField := ⟨275,0,0,1⟩
private theorem pos404 : (0:ℤ) < 922 := by decide +kernel
private theorem cp404 : (⟨(275/922),0,0,(1/922)⟩ : CertField) = scaled n404 922 := by decide +kernel
private def n405 : IntField := ⟨6535875,0,0,14875⟩
private theorem pos405 : (0:ℤ) < 67856138 := by decide +kernel
private theorem cp405 : (⟨(6535875/67856138),0,0,(2125/9693734)⟩ : CertField) = scaled n405 67856138 := by decide +kernel
private def n406 : IntField := ⟨44583,0,0,(-97)⟩
private theorem pos406 : (0:ℤ) < 323162 := by decide +kernel
private theorem cp406 : (⟨(6369/46166),0,0,(-97/323162)⟩ : CertField) = scaled n406 323162 := by decide +kernel
private def n407 : IntField := ⟨(-388869),1019200,0,0⟩
private theorem pos407 : (0:ℤ) < 7488217 := by decide +kernel
private theorem cp407 : (⟨(-388869/7488217),(1019200/7488217),0,0⟩ : CertField) = scaled n407 7488217 := by decide +kernel
private def n408 : IntField := ⟨1830045,0,0,4165⟩
private theorem pos408 : (0:ℤ) < 9693734 := by decide +kernel
private theorem cp408 : (⟨(1830045/9693734),0,0,(4165/9693734)⟩ : CertField) = scaled n408 9693734 := by decide +kernel
private def n409 : IntField := ⟨(-1718411),3046402,0,0⟩
private theorem pos409 : (0:ℤ) < 17699422 := by decide +kernel
private theorem cp409 : (⟨(-1718411/17699422),(1523201/8849711),0,0⟩ : CertField) = scaled n409 17699422 := by decide +kernel
private def n410 : IntField := ⟨1893227,0,0,165991⟩
private theorem pos410 : (0:ℤ) < 6455450 := by decide +kernel
private theorem cp410 : (⟨(1893227/6455450),0,0,(165991/6455450)⟩ : CertField) = scaled n410 6455450 := by decide +kernel
private def n411 : IntField := ⟨1305027,27163759,0,0⟩
private theorem pos411 : (0:ℤ) < 231271139 := by decide +kernel
private theorem cp411 : (⟨(1305027/231271139),(27163759/231271139),0,0⟩ : CertField) = scaled n411 231271139 := by decide +kernel
private def n412 : IntField := ⟨52713,152315,0,0⟩
private theorem pos412 : (0:ℤ) < 90753 := by decide +kernel
private theorem cp412 : (⟨(17571/30251),(152315/90753),0,0⟩ : CertField) = scaled n412 90753 := by decide +kernel
private def n413 : IntField := ⟨(-12201),156391,0,0⟩
private theorem pos413 : (0:ℤ) < 84309 := by decide +kernel
private theorem cp413 : (⟨(-4067/28103),(156391/84309),0,0⟩ : CertField) = scaled n413 84309 := by decide +kernel
private def n414 : IntField := ⟨4840,(-1),0,0⟩
private theorem pos414 : (0:ℤ) < 16393 := by decide +kernel
private theorem cp414 : (⟨(4840/16393),(-1/16393),0,0⟩ : CertField) = scaled n414 16393 := by decide +kernel
private def n415 : IntField := ⟨71140,138176,0,0⟩
private theorem pos415 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp415 : (⟨(71140/97513),(138176/97513),0,0⟩ : CertField) = scaled n415 97513 := by decide +kernel
private def n416 : IntField := ⟨287829,0,0,2951⟩
private theorem pos416 : (0:ℤ) < 91686 := by decide +kernel
private theorem cp416 : (⟨(95943/30562),0,0,(2951/91686)⟩ : CertField) = scaled n416 91686 := by decide +kernel
private def n417 : IntField := ⟨2014803,0,0,20657⟩
private theorem pos417 : (0:ℤ) < 327450 := by decide +kernel
private theorem cp417 : (⟨(671601/109150),0,0,(20657/327450)⟩ : CertField) = scaled n417 327450 := by decide +kernel
private def n418 : IntField := ⟨7875,0,0,(-139)⟩
private theorem pos418 : (0:ℤ) < 1554 := by decide +kernel
private theorem cp418 : (⟨(375/74),0,0,(-139/1554)⟩ : CertField) = scaled n418 1554 := by decide +kernel
private def n419 : IntField := ⟨721239,0,0,48244⟩
private theorem pos419 : (0:ℤ) < 10790913 := by decide +kernel
private theorem cp419 : (⟨(240413/3596971),0,0,(6892/1541559)⟩ : CertField) = scaled n419 10790913 := by decide +kernel
private def n420 : IntField := ⟨7761,0,0,1⟩
private theorem pos420 : (0:ℤ) < 20418 := by decide +kernel
private theorem cp420 : (⟨(2587/6806),0,0,(1/20418)⟩ : CertField) = scaled n420 20418 := by decide +kernel
private def n421 : IntField := ⟨579,0,0,(-1)⟩
private theorem pos421 : (0:ℤ) < 1510 := by decide +kernel
private theorem cp421 : (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) = scaled n421 1510 := by decide +kernel
private def n422 : IntField := ⟨5505,0,0,(-112)⟩
private theorem pos422 : (0:ℤ) < 38505 := by decide +kernel
private theorem cp422 : (⟨(367/2567),0,0,(-112/38505)⟩ : CertField) = scaled n422 38505 := by decide +kernel
private def n423 : IntField := ⟨189,0,0,1⟩
private theorem pos423 : (0:ℤ) < 510 := by decide +kernel
private theorem cp423 : (⟨(63/170),0,0,(1/510)⟩ : CertField) = scaled n423 510 := by decide +kernel
private def n424 : IntField := ⟨(-698820),1477331,0,0⟩
private theorem pos424 : (0:ℤ) < 11017897 := by decide +kernel
private theorem cp424 : (⟨(-698820/11017897),(1477331/11017897),0,0⟩ : CertField) = scaled n424 11017897 := by decide +kernel
private def n425 : IntField := ⟨446,1,0,0⟩
private theorem pos425 : (0:ℤ) < 1177 := by decide +kernel
private theorem cp425 : (⟨(446/1177),(1/1177),0,0⟩ : CertField) = scaled n425 1177 := by decide +kernel
private def n426 : IntField := ⟨651,(-1),0,0⟩
private theorem pos426 : (0:ℤ) < 1702 := by decide +kernel
private theorem cp426 : (⟨(651/1702),(-1/1702),0,0⟩ : CertField) = scaled n426 1702 := by decide +kernel
private def n427 : IntField := ⟨(-6285744),9159133,0,0⟩
private theorem pos427 : (0:ℤ) < 52084604 := by decide +kernel
private theorem cp427 : (⟨(-1571436/13021151),(9159133/52084604),0,0⟩ : CertField) = scaled n427 52084604 := by decide +kernel
private def n428 : IntField := ⟨(-1011781),12763133,0,0⟩
private theorem pos428 : (0:ℤ) < 110140129 := by decide +kernel
private theorem cp428 : (⟨(-1011781/110140129),(12763133/110140129),0,0⟩ : CertField) = scaled n428 110140129 := by decide +kernel
private def n429 : IntField := ⟨9741,(-1),0,0⟩
private theorem pos429 : (0:ℤ) < 25521 := by decide +kernel
private theorem cp429 : (⟨(3247/8507),(-1/25521),0,0⟩ : CertField) = scaled n429 25521 := by decide +kernel
private def n430 : IntField := ⟨5048673,0,0,337708⟩
private theorem pos430 : (0:ℤ) < 38538975 := by decide +kernel
private theorem cp430 : (⟨(1682891/12846325),0,0,(337708/38538975)⟩ : CertField) = scaled n430 38538975 := by decide +kernel
private def n431 : IntField := ⟨1493871,3016696,0,0⟩
private theorem pos431 : (0:ℤ) < 2100813 := by decide +kernel
private theorem cp431 : (⟨(497957/700271),(3016696/2100813),0,0⟩ : CertField) = scaled n431 2100813 := by decide +kernel
private def n432 : IntField := ⟨3216375,0,0,(-294950)⟩
private theorem pos432 : (0:ℤ) < 580027 := by decide +kernel
private theorem cp432 : (⟨(3216375/580027),0,0,(-294950/580027)⟩ : CertField) = scaled n432 580027 := by decide +kernel
private def n433 : IntField := ⟨4209,0,0,(-1)⟩
private theorem pos433 : (0:ℤ) < 15090 := by decide +kernel
private theorem cp433 : (⟨(1403/5030),0,0,(-1/15090)⟩ : CertField) = scaled n433 15090 := by decide +kernel
private def n434 : IntField := ⟨900585,0,0,(-82586)⟩
private theorem pos434 : (0:ℤ) < 82861 := by decide +kernel
private theorem cp434 : (⟨(900585/82861),0,0,(-82586/82861)⟩ : CertField) = scaled n434 82861 := by decide +kernel
private def n435 : IntField := ⟨25971,0,0,(-34)⟩
private theorem pos435 : (0:ℤ) < 6157 := by decide +kernel
private theorem cp435 : (⟨(25971/6157),0,0,(-34/6157)⟩ : CertField) = scaled n435 6157 := by decide +kernel
private def n436 : IntField := ⟨1269727,13024501,0,0⟩
private theorem pos436 : (0:ℤ) < 8457119 := by decide +kernel
private theorem cp436 : (⟨(1269727/8457119),(13024501/8457119),0,0⟩ : CertField) = scaled n436 8457119 := by decide +kernel
private def n437 : IntField := ⟨5163,1,0,0⟩
private theorem pos437 : (0:ℤ) < 18654 := by decide +kernel
private theorem cp437 : (⟨(1721/6218),(1/18654),0,0⟩ : CertField) = scaled n437 18654 := by decide +kernel
private def n438 : IntField := ⟨27236082,37882186,0,0⟩
private theorem pos438 : (0:ℤ) < 31583409 := by decide +kernel
private theorem cp438 : (⟨(9078694/10527803),(37882186/31583409),0,0⟩ : CertField) = scaled n438 31583409 := by decide +kernel
private def n439 : IntField := ⟨3006563,0,0,170973⟩
private theorem pos439 : (0:ℤ) < 96454246 := by decide +kernel
private theorem cp439 : (⟨(429509/13779178),0,0,(170973/96454246)⟩ : CertField) = scaled n439 96454246 := by decide +kernel
private def n440 : IntField := ⟨17703,0,0,1⟩
private theorem pos440 : (0:ℤ) < 45778 := by decide +kernel
private theorem cp440 : (⟨(17703/45778),0,0,(1/45778)⟩ : CertField) = scaled n440 45778 := by decide +kernel
private def n441 : IntField := ⟨1169,0,0,(-1)⟩
private theorem pos441 : (0:ℤ) < 3010 := by decide +kernel
private theorem cp441 : (⟨(167/430),0,0,(-1/3010)⟩ : CertField) = scaled n441 3010 := by decide +kernel
private def n442 : IntField := ⟨26635,0,0,(-99)⟩
private theorem pos442 : (0:ℤ) < 454510 := by decide +kernel
private theorem cp442 : (⟨(761/12986),0,0,(-99/454510)⟩ : CertField) = scaled n442 454510 := by decide +kernel
private def n443 : IntField := ⟨579,0,0,1⟩
private theorem pos443 : (0:ℤ) < 1510 := by decide +kernel
private theorem cp443 : (⟨(579/1510),0,0,(1/1510)⟩ : CertField) = scaled n443 1510 := by decide +kernel
private def n444 : IntField := ⟨(-499115),1078592,0,0⟩
private theorem pos444 : (0:ℤ) < 17679959 := by decide +kernel
private theorem cp444 : (⟨(-499115/17679959),(1078592/17679959),0,0⟩ : CertField) = scaled n444 17679959 := by decide +kernel
private def n445 : IntField := ⟨1059,1,0,0⟩
private theorem pos445 : (0:ℤ) < 2742 := by decide +kernel
private theorem cp445 : (⟨(353/914),(1/2742),0,0⟩ : CertField) = scaled n445 2742 := by decide +kernel
private def n446 : IntField := ⟨1364,(-1),0,0⟩
private theorem pos446 : (0:ℤ) < 3517 := by decide +kernel
private theorem cp446 : (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) = scaled n446 3517 := by decide +kernel
private def n447 : IntField := ⟨(-4522933),6681756,0,0⟩
private theorem pos447 : (0:ℤ) < 83577988 := by decide +kernel
private theorem cp447 : (⟨(-4522933/83577988),(1670439/20894497),0,0⟩ : CertField) = scaled n447 83577988 := by decide +kernel
private def n448 : IntField := ⟨(-561788),14188809,0,0⟩
private theorem pos448 : (0:ℤ) < 272669507 := by decide +kernel
private theorem cp448 : (⟨(-561788/272669507),(14188809/272669507),0,0⟩ : CertField) = scaled n448 272669507 := by decide +kernel
private def n449 : IntField := ⟨21015,(-1),0,0⟩
private theorem pos449 : (0:ℤ) < 54241 := by decide +kernel
private theorem cp449 : (⟨(21015/54241),(-1/54241),0,0⟩ : CertField) = scaled n449 54241 := by decide +kernel
private def n450 : IntField := ⟨3006563,0,0,170973⟩
private theorem pos450 : (0:ℤ) < 49211350 := by decide +kernel
private theorem cp450 : (⟨(3006563/49211350),0,0,(170973/49211350)⟩ : CertField) = scaled n450 49211350 := by decide +kernel
private def n451 : IntField := ⟨2128591,5921041,0,0⟩
private theorem pos451 : (0:ℤ) < 8433958 := by decide +kernel
private theorem cp451 : (⟨(2128591/8433958),(5921041/8433958),0,0⟩ : CertField) = scaled n451 8433958 := by decide +kernel
private def n452 : IntField := ⟨21517125,0,0,25225⟩
private theorem pos452 : (0:ℤ) < 15762614 := by decide +kernel
private theorem cp452 : (⟨(439125/321686),0,0,(25225/15762614)⟩ : CertField) = scaled n452 15762614 := by decide +kernel
private def n453 : IntField := ⟨860685,0,0,1009⟩
private theorem pos453 : (0:ℤ) < 321686 := by decide +kernel
private theorem cp453 : (⟨(860685/321686),0,0,(1009/321686)⟩ : CertField) = scaled n453 321686 := by decide +kernel
private def n454 : IntField := ⟨112707,0,0,(-253)⟩
private theorem pos454 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp454 : (⟨(16101/8282),0,0,(-253/57974)⟩ : CertField) = scaled n454 57974 := by decide +kernel
private def n455 : IntField := ⟨(-1837512),39097169,0,0⟩
private theorem pos455 : (0:ℤ) < 50928131 := by decide +kernel
private theorem cp455 : (⟨(-1837512/50928131),(39097169/50928131),0,0⟩ : CertField) = scaled n455 50928131 := by decide +kernel
private def n456 : IntField := ⟨9287043,17507389,0,0⟩
private theorem pos456 : (0:ℤ) < 29542461 := by decide +kernel
private theorem cp456 : (⟨(3095681/9847487),(17507389/29542461),0,0⟩ : CertField) = scaled n456 29542461 := by decide +kernel
private def n457 : IntField := ⟨213575,0,0,(-16800)⟩
private theorem pos457 : (0:ℤ) < 1891477 := by decide +kernel
private theorem cp457 : (⟨(213575/1891477),0,0,(-2400/270211)⟩ : CertField) = scaled n457 1891477 := by decide +kernel
private def n458 : IntField := ⟨9237,0,0,(-1)⟩
private theorem pos458 : (0:ℤ) < 24198 := by decide +kernel
private theorem cp458 : (⟨(3079/8066),0,0,(-1/24198)⟩ : CertField) = scaled n458 24198 := by decide +kernel
private def n459 : IntField := ⟨2017,0,0,(-28)⟩
private theorem pos459 : (0:ℤ) < 19765 := by decide +kernel
private theorem cp459 : (⟨(2017/19765),0,0,(-28/19765)⟩ : CertField) = scaled n459 19765 := by decide +kernel
private def n460 : IntField := ⟨681,0,0,(-1)⟩
private theorem pos460 : (0:ℤ) < 1770 := by decide +kernel
private theorem cp460 : (⟨(227/590),0,0,(-1/1770)⟩ : CertField) = scaled n460 1770 := by decide +kernel
private def n461 : IntField := ⟨3257,0,0,(-63)⟩
private theorem pos461 : (0:ℤ) < 25670 := by decide +kernel
private theorem cp461 : (⟨(3257/25670),0,0,(-63/25670)⟩ : CertField) = scaled n461 25670 := by decide +kernel
private def n462 : IntField := ⟨(-485901),1238120,0,0⟩
private theorem pos462 : (0:ℤ) < 11017897 := by decide +kernel
private theorem cp462 : (⟨(-485901/11017897),(1238120/11017897),0,0⟩ : CertField) = scaled n462 11017897 := by decide +kernel
private def n463 : IntField := ⟨59801,0,0,(-4704)⟩
private theorem pos463 : (0:ℤ) < 270211 := by decide +kernel
private theorem cp463 : (⟨(59801/270211),0,0,(-4704/270211)⟩ : CertField) = scaled n463 270211 := by decide +kernel
private def n464 : IntField := ⟨(-2126899),3703338,0,0⟩
private theorem pos464 : (0:ℤ) < 26042302 := by decide +kernel
private theorem cp464 : (⟨(-2126899/26042302),(1851669/13021151),0,0⟩ : CertField) = scaled n464 26042302 := by decide +kernel
private def n465 : IntField := ⟨1295416,6050211,0,0⟩
private theorem pos465 : (0:ℤ) < 67839167 := by decide +kernel
private theorem cp465 : (⟨(1295416/67839167),(6050211/67839167),0,0⟩ : CertField) = scaled n465 67839167 := by decide +kernel
private def n466 : IntField := ⟨8265,1,0,0⟩
private theorem pos466 : (0:ℤ) < 21741 := by decide +kernel
private theorem cp466 : (⟨(2755/7247),(1/21741),0,0⟩ : CertField) = scaled n466 21741 := by decide +kernel
private def n467 : IntField := ⟨1320117,2698847,0,0⟩
private theorem pos467 : (0:ℤ) < 2100813 := by decide +kernel
private theorem cp467 : (⟨(440039/700271),(2698847/2100813),0,0⟩ : CertField) = scaled n467 2100813 := by decide +kernel
private def n468 : IntField := ⟨4086635,0,0,(-89725)⟩
private theorem pos468 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp468 : (⟨(583805/165722),0,0,(-89725/1160054)⟩ : CertField) = scaled n468 1160054 := by decide +kernel
private def n469 : IntField := ⟨4585,0,0,(-1)⟩
private theorem pos469 : (0:ℤ) < 15526 := by decide +kernel
private theorem cp469 : (⟨(655/2218),0,0,(-1/15526)⟩ : CertField) = scaled n469 15526 := by decide +kernel
private def n470 : IntField := ⟨5721289,0,0,(-125615)⟩
private theorem pos470 : (0:ℤ) < 828610 := by decide +kernel
private theorem cp470 : (⟨(5721289/828610),0,0,(-25123/165722)⟩ : CertField) = scaled n470 828610 := by decide +kernel
private def n471 : IntField := ⟨57529,0,0,(-755)⟩
private theorem pos471 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp471 : (⟨(57529/12314),0,0,(-755/12314)⟩ : CertField) = scaled n471 12314 := by decide +kernel
private def n472 : IntField := ⟨313,0,0,(-1)⟩
private theorem pos472 : (0:ℤ) < 1042 := by decide +kernel
private theorem cp472 : (⟨(313/1042),0,0,(-1/1042)⟩ : CertField) = scaled n472 1042 := by decide +kernel
private def n473 : IntField := ⟨(-3042309),38088568,0,0⟩
private theorem pos473 : (0:ℤ) < 25371357 := by decide +kernel
private theorem cp473 : (⟨(-1014103/8457119),(38088568/25371357),0,0⟩ : CertField) = scaled n473 25371357 := by decide +kernel
private def n474 : IntField := ⟨4264,1,0,0⟩
private theorem pos474 : (0:ℤ) < 14557 := by decide +kernel
private theorem cp474 : (⟨(4264/14557),(1/14557),0,0⟩ : CertField) = scaled n474 14557 := by decide +kernel
private def n475 : IntField := ⟨24169284,33874112,0,0⟩
private theorem pos475 : (0:ℤ) < 31583409 := by decide +kernel
private theorem cp475 : (⟨(8056428/10527803),(33874112/31583409),0,0⟩ : CertField) = scaled n475 31583409 := by decide +kernel
private def n476 : IntField := ⟨49471,0,0,(-551)⟩
private theorem pos476 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp476 : (⟨(49471/12314),0,0,(-551/12314)⟩ : CertField) = scaled n476 12314 := by decide +kernel
private def n477 : IntField := ⟨15169,0,0,(-1611)⟩
private theorem pos477 : (0:ℤ) < 56462 := by decide +kernel
private theorem cp477 : (⟨(2167/8066),0,0,(-1611/56462)⟩ : CertField) = scaled n477 56462 := by decide +kernel
private def n478 : IntField := ⟨71,0,0,7⟩
private theorem pos478 : (0:ℤ) < 590 := by decide +kernel
private theorem cp478 : (⟨(71/590),0,0,(7/590)⟩ : CertField) = scaled n478 590 := by decide +kernel
private def n479 : IntField := ⟨223,0,0,21⟩
private theorem pos479 : (0:ℤ) < 1510 := by decide +kernel
private theorem cp479 : (⟨(223/1510),0,0,(21/1510)⟩ : CertField) = scaled n479 1510 := by decide +kernel
private def n480 : IntField := ⟨411,0,0,41⟩
private theorem pos480 : (0:ℤ) < 1310 := by decide +kernel
private theorem cp480 : (⟨(411/1310),0,0,(41/1310)⟩ : CertField) = scaled n480 1310 := by decide +kernel
private def n481 : IntField := ⟨(-5372366),12188673,0,0⟩
private theorem pos481 : (0:ℤ) < 52084604 := by decide +kernel
private theorem cp481 : (⟨(-2686183/26042302),(12188673/52084604),0,0⟩ : CertField) = scaled n481 52084604 := by decide +kernel
private def n482 : IntField := ⟨106183,0,0,(-11277)⟩
private theorem pos482 : (0:ℤ) < 201650 := by decide +kernel
private theorem cp482 : (⟨(106183/201650),0,0,(-11277/201650)⟩ : CertField) = scaled n482 201650 := by decide +kernel
private def n483 : IntField := ⟨2398857,4951487,0,0⟩
private theorem pos483 : (0:ℤ) < 2100813 := by decide +kernel
private theorem cp483 : (⟨(799619/700271),(4951487/2100813),0,0⟩ : CertField) = scaled n483 2100813 := by decide +kernel
private def n484 : IntField := ⟨7863965,0,0,(-264385)⟩
private theorem pos484 : (0:ℤ) < 1160054 := by decide +kernel
private theorem cp484 : (⟨(7863965/1160054),0,0,(-264385/1160054)⟩ : CertField) = scaled n484 1160054 := by decide +kernel
private def n485 : IntField := ⟨313,0,0,1⟩
private theorem pos485 : (0:ℤ) < 1042 := by decide +kernel
private theorem cp485 : (⟨(313/1042),0,0,(1/1042)⟩ : CertField) = scaled n485 1042 := by decide +kernel
private def n486 : IntField := ⟨8531,0,0,(-1)⟩
private theorem pos486 : (0:ℤ) < 27970 := by decide +kernel
private theorem cp486 : (⟨(8531/27970),0,0,(-1/27970)⟩ : CertField) = scaled n486 27970 := by decide +kernel
private def n487 : IntField := ⟨11009551,0,0,(-370139)⟩
private theorem pos487 : (0:ℤ) < 828610 := by decide +kernel
private theorem cp487 : (⟨(11009551/828610),0,0,(-370139/828610)⟩ : CertField) = scaled n487 828610 := by decide +kernel
private def n488 : IntField := ⟨106351,0,0,(-1991)⟩
private theorem pos488 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp488 : (⟨(106351/12314),0,0,(-1991/12314)⟩ : CertField) = scaled n488 12314 := by decide +kernel
private def n489 : IntField := ⟨539,0,0,(-1)⟩
private theorem pos489 : (0:ℤ) < 1750 := by decide +kernel
private theorem cp489 : (⟨(77/250),0,0,(-1/1750)⟩ : CertField) = scaled n489 1750 := by decide +kernel
private def n490 : IntField := ⟨(-4304901),69110935,0,0⟩
private theorem pos490 : (0:ℤ) < 25371357 := by decide +kernel
private theorem cp490 : (⟨(-1434967/8457119),(69110935/25371357),0,0⟩ : CertField) = scaled n490 25371357 := by decide +kernel
private def n491 : IntField := ⟨8222,1,0,0⟩
private theorem pos491 : (0:ℤ) < 27073 := by decide +kernel
private theorem cp491 : (⟨(8222/27073),(1/27073),0,0⟩ : CertField) = scaled n491 27073 := by decide +kernel
private def n492 : IntField := ⟨44063964,62124152,0,0⟩
private theorem pos492 : (0:ℤ) < 31583409 := by decide +kernel
private theorem cp492 : (⟨(14687988/10527803),(62124152/31583409),0,0⟩ : CertField) = scaled n492 31583409 := by decide +kernel
private def n493 : IntField := ⟨95449,0,0,(-1715)⟩
private theorem pos493 : (0:ℤ) < 12314 := by decide +kernel
private theorem cp493 : (⟨(95449/12314),0,0,(-1715/12314)⟩ : CertField) = scaled n493 12314 := by decide +kernel
private def n494 : IntField := ⟨979525,0,0,(-57475)⟩
private theorem pos494 : (0:ℤ) < 21210854 := by decide +kernel
private theorem cp494 : (⟨(979525/21210854),0,0,(-57475/21210854)⟩ : CertField) = scaled n494 21210854 := by decide +kernel
private def n495 : IntField := ⟨19899,0,0,(-1)⟩
private theorem pos495 : (0:ℤ) < 51358 := by decide +kernel
private theorem cp495 : (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) = scaled n495 51358 := by decide +kernel
private def n496 : IntField := ⟨9029,0,0,(-11)⟩
private theorem pos496 : (0:ℤ) < 198830 := by decide +kernel
private theorem cp496 : (⟨(9029/198830),0,0,(-11/198830)⟩ : CertField) = scaled n496 198830 := by decide +kernel
private def n497 : IntField := ⟨1311,0,0,(-1)⟩
private theorem pos497 : (0:ℤ) < 3370 := by decide +kernel
private theorem cp497 : (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) = scaled n497 3370 := by decide +kernel
private def n498 : IntField := ⟨11823,0,0,(-32)⟩
private theorem pos498 : (0:ℤ) < 227255 := by decide +kernel
private theorem cp498 : (⟨(1689/32465),0,0,(-32/227255)⟩ : CertField) = scaled n498 227255 := by decide +kernel
private def n499 : IntField := ⟨(-345332),904215,0,0⟩
private theorem pos499 : (0:ℤ) < 17679959 := by decide +kernel
private theorem cp499 : (⟨(-345332/17679959),(904215/17679959),0,0⟩ : CertField) = scaled n499 17679959 := by decide +kernel
private def n500 : IntField := ⟨274267,0,0,(-16093)⟩
private theorem pos500 : (0:ℤ) < 3030122 := by decide +kernel
private theorem cp500 : (⟨(274267/3030122),0,0,(-16093/3030122)⟩ : CertField) = scaled n500 3030122 := by decide +kernel
private def n501 : IntField := ⟨(-4576554),8108323,0,0⟩
private theorem pos501 : (0:ℤ) < 125366982 := by decide +kernel
private theorem cp501 : (⟨(-762759/20894497),(8108323/125366982),0,0⟩ : CertField) = scaled n501 125366982 := by decide +kernel
private def n502 : IntField := ⟨14504541,77921561,0,0⟩
private theorem pos502 : (0:ℤ) < 1882548107 := by decide +kernel
private theorem cp502 : (⟨(14504541/1882548107),(77921561/1882548107),0,0⟩ : CertField) = scaled n502 1882548107 := by decide +kernel
private def n503 : IntField := ⟨18819,1,0,0⟩
private theorem pos503 : (0:ℤ) < 48661 := by decide +kernel
private theorem cp503 : (⟨(18819/48661),(1/48661),0,0⟩ : CertField) = scaled n503 48661 := by decide +kernel
private def n504 : IntField := ⟨935716,2649381,0,0⟩
private theorem pos504 : (0:ℤ) < 4216979 := by decide +kernel
private theorem cp504 : (⟨(935716/4216979),(2649381/4216979),0,0⟩ : CertField) = scaled n504 4216979 := by decide +kernel
private def n505 : IntField := ⟨971349,0,0,(-147649)⟩
private theorem pos505 : (0:ℤ) < 538734 := by decide +kernel
private theorem cp505 : (⟨(323783/179578),0,0,(-147649/538734)⟩ : CertField) = scaled n505 538734 := by decide +kernel
private def n506 : IntField := ⟨2275405,0,0,168075⟩
private theorem pos506 : (0:ℤ) < 2251802 := by decide +kernel
private theorem cp506 : (⟨(2275405/2251802),0,0,(168075/2251802)⟩ : CertField) = scaled n506 2251802 := by decide +kernel
private def n507 : IntField := ⟨3185567,0,0,235305⟩
private theorem pos507 : (0:ℤ) < 1608430 := by decide +kernel
private theorem cp507 : (⟨(3185567/1608430),0,0,(47061/321686)⟩ : CertField) = scaled n507 1608430 := by decide +kernel
private def n508 : IntField := ⟨124859,0,0,(-1755)⟩
private theorem pos508 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp508 : (⟨(17837/8282),0,0,(-1755/57974)⟩ : CertField) = scaled n508 57974 := by decide +kernel
private def n509 : IntField := ⟨(-17165189),76876453,0,0⟩
private theorem pos509 : (0:ℤ) < 101856262 := by decide +kernel
private theorem cp509 : (⟨(-17165189/101856262),(76876453/101856262),0,0⟩ : CertField) = scaled n509 101856262 := by decide +kernel
private def n510 : IntField := ⟨8214216,15661538,0,0⟩
private theorem pos510 : (0:ℤ) < 29542461 := by decide +kernel
private theorem cp510 : (⟨(2738072/9847487),(15661538/29542461),0,0⟩ : CertField) = scaled n510 29542461 := by decide +kernel
private def n511 : IntField := ⟨53683,0,0,(-648)⟩
private theorem pos511 : (0:ℤ) < 28987 := by decide +kernel
private theorem cp511 : (⟨(7669/4141),0,0,(-648/28987)⟩ : CertField) = scaled n511 28987 := by decide +kernel
private def n512 : IntField := ⟨2633475,0,0,(-130150)⟩
private theorem pos512 : (0:ℤ) < 104524931 := by decide +kernel
private theorem cp512 : (⟨(2633475/104524931),0,0,(-130150/104524931)⟩ : CertField) = scaled n512 104524931 := by decide +kernel
private def n513 : IntField := ⟨1311,0,0,1⟩
private theorem pos513 : (0:ℤ) < 3370 := by decide +kernel
private theorem cp513 : (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) = scaled n513 3370 := by decide +kernel
private def n514 : IntField := ⟨34601,0,0,(-1)⟩
private theorem pos514 : (0:ℤ) < 88618 := by decide +kernel
private theorem cp514 : (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) = scaled n514 88618 := by decide +kernel
private def n515 : IntField := ⟨23811,0,0,76⟩
private theorem pos515 : (0:ℤ) < 921695 := by decide +kernel
private theorem cp515 : (⟨(23811/921695),0,0,(76/921695)⟩ : CertField) = scaled n515 921695 := by decide +kernel
private def n516 : IntField := ⟨2141,0,0,(-1)⟩
private theorem pos516 : (0:ℤ) < 5470 := by decide +kernel
private theorem cp516 : (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) = scaled n516 5470 := by decide +kernel
private def n517 : IntField := ⟨14357,0,0,37⟩
private theorem pos517 : (0:ℤ) < 502670 := by decide +kernel
private theorem cp517 : (⟨(2051/71810),0,0,(37/502670)⟩ : CertField) = scaled n517 502670 := by decide +kernel
private def n518 : IntField := ⟨1169,0,0,1⟩
private theorem pos518 : (0:ℤ) < 3010 := by decide +kernel
private theorem cp518 : (⟨(167/430),0,0,(1/3010)⟩ : CertField) = scaled n518 3010 := by decide +kernel
private def n519 : IntField := ⟨1959,0,0,(-1)⟩
private theorem pos519 : (0:ℤ) < 5010 := by decide +kernel
private theorem cp519 : (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) = scaled n519 5010 := by decide +kernel
private def n520 : IntField := ⟨(-599222),1584765,0,0⟩
private theorem pos520 : (0:ℤ) < 54363419 := by decide +kernel
private theorem cp520 : (⟨(-599222/54363419),(1584765/54363419),0,0⟩ : CertField) = scaled n520 54363419 := by decide +kernel
private def n521 : IntField := ⟨1932,1,0,0⟩
private theorem pos521 : (0:ℤ) < 4957 := by decide +kernel
private theorem cp521 : (⟨(1932/4957),(1/4957),0,0⟩ : CertField) = scaled n521 4957 := by decide +kernel
private def n522 : IntField := ⟨2337,(-1),0,0⟩
private theorem pos522 : (0:ℤ) < 5982 := by decide +kernel
private theorem cp522 : (⟨(779/1994),(-1/5982),0,0⟩ : CertField) = scaled n522 5982 := by decide +kernel
private def n523 : IntField := ⟨737373,0,0,(-36442)⟩
private theorem pos523 : (0:ℤ) < 14932133 := by decide +kernel
private theorem cp523 : (⟨(737373/14932133),0,0,(-36442/14932133)⟩ : CertField) = scaled n523 14932133 := by decide +kernel
private def n524 : IntField := ⟨(-7968384),14207533,0,0⟩
private theorem pos524 : (0:ℤ) < 385486062 := by decide +kernel
private theorem cp524 : (⟨(-1328064/64247677),(14207533/385486062),0,0⟩ : CertField) = scaled n524 385486062 := by decide +kernel
private def n525 : IntField := ⟨296587,1733302,0,0⟩
private theorem pos525 : (0:ℤ) < 72787979 := by decide +kernel
private theorem cp525 : (⟨(296587/72787979),(1733302/72787979),0,0⟩ : CertField) = scaled n525 72787979 := by decide +kernel
private def n526 : IntField := ⟨33653,1,0,0⟩
private theorem pos526 : (0:ℤ) < 86281 := by decide +kernel
private theorem cp526 : (⟨(33653/86281),(1/86281),0,0⟩ : CertField) = scaled n526 86281 := by decide +kernel
private def n527 : IntField := ⟨40426244,99902592,0,0⟩
private theorem pos527 : (0:ℤ) < 312797329 := by decide +kernel
private theorem cp527 : (⟨(40426244/312797329),(99902592/312797329),0,0⟩ : CertField) = scaled n527 312797329 := by decide +kernel
private def n528 : IntField := ⟨15225,0,0,(-1976)⟩
private theorem pos528 : (0:ℤ) < 14217 := by decide +kernel
private theorem cp528 : (⟨(725/677),0,0,(-1976/14217)⟩ : CertField) = scaled n528 14217 := by decide +kernel
private def n529 : IntField := ⟨34058535,0,0,3262775⟩
private theorem pos529 : (0:ℤ) < 65710974 := by decide +kernel
private theorem cp529 : (⟨(1621835/3129094),0,0,(3262775/65710974)⟩ : CertField) = scaled n529 65710974 := by decide +kernel
private def n530 : IntField := ⟨47681949,0,0,4567885⟩
private theorem pos530 : (0:ℤ) < 46936410 := by decide +kernel
private theorem cp530 : (⟨(15893983/15645470),0,0,(913577/9387282)⟩ : CertField) = scaled n530 46936410 := by decide +kernel
private def n531 : IntField := ⟨132489,0,0,(-21755)⟩
private theorem pos531 : (0:ℤ) < 28434 := by decide +kernel
private theorem cp531 : (⟨(6309/1354),0,0,(-21755/28434)⟩ : CertField) = scaled n531 28434 := by decide +kernel
private def n532 : IntField := ⟨113211,0,0,(-18491)⟩
private theorem pos532 : (0:ℤ) < 28434 := by decide +kernel
private theorem cp532 : (⟨(5391/1354),0,0,(-18491/28434)⟩ : CertField) = scaled n532 28434 := by decide +kernel
private def n533 : IntField := ⟨2299633,0,0,(-203377)⟩
private theorem pos533 : (0:ℤ) < 21210854 := by decide +kernel
private theorem cp533 : (⟨(328519/3030122),0,0,(-203377/21210854)⟩ : CertField) = scaled n533 21210854 := by decide +kernel
private def n534 : IntField := ⟨10967,0,0,1189⟩
private theorem pos534 : (0:ℤ) < 198830 := by decide +kernel
private theorem cp534 : (⟨(10967/198830),0,0,(1189/198830)⟩ : CertField) = scaled n534 198830 := by decide +kernel
private def n535 : IntField := ⟨28623,0,0,3071⟩
private theorem pos535 : (0:ℤ) < 454510 := by decide +kernel
private theorem cp535 : (⟨(4089/64930),0,0,(3071/454510)⟩ : CertField) = scaled n535 454510 := by decide +kernel
private def n536 : IntField := ⟨(-11491011),26699858,0,0⟩
private theorem pos536 : (0:ℤ) < 250733964 := by decide +kernel
private theorem cp536 : (⟨(-3830337/83577988),(13349929/125366982),0,0⟩ : CertField) = scaled n536 250733964 := by decide +kernel
private def n537 : IntField := ⟨16097431,0,0,(-1423639)⟩
private theorem pos537 : (0:ℤ) < 75753050 := by decide +kernel
private theorem cp537 : (⟨(16097431/75753050),0,0,(-1423639/75753050)⟩ : CertField) = scaled n537 75753050 := by decide +kernel
private def n538 : IntField := ⟨1693486,4861851,0,0⟩
private theorem pos538 : (0:ℤ) < 4216979 := by decide +kernel
private theorem cp538 : (⟨(1693486/4216979),(4861851/4216979),0,0⟩ : CertField) = scaled n538 4216979 := by decide +kernel
private def n539 : IntField := ⟨14961695,0,0,945270⟩
private theorem pos539 : (0:ℤ) < 7881307 := by decide +kernel
private theorem cp539 : (⟨(2137385/1125901),0,0,(945270/7881307)⟩ : CertField) = scaled n539 7881307 := by decide +kernel
private def n540 : IntField := ⟨2992339,0,0,189054⟩
private theorem pos540 : (0:ℤ) < 804215 := by decide +kernel
private theorem cp540 : (⟨(2992339/804215),0,0,(189054/804215)⟩ : CertField) = scaled n540 804215 := by decide +kernel
private def n541 : IntField := ⟨16489,0,0,(-324)⟩
private theorem pos541 : (0:ℤ) < 4141 := by decide +kernel
private theorem cp541 : (⟨(16489/4141),0,0,(-324/4141)⟩ : CertField) = scaled n541 4141 := by decide +kernel
private def n542 : IntField := ⟨(-14351173),69686630,0,0⟩
private theorem pos542 : (0:ℤ) < 50928131 := by decide +kernel
private theorem cp542 : (⟨(-14351173/50928131),(69686630/50928131),0,0⟩ : CertField) = scaled n542 50928131 := by decide +kernel
private def n543 : IntField := ⟨14937036,28731998,0,0⟩
private theorem pos543 : (0:ℤ) < 29542461 := by decide +kernel
private theorem cp543 : (⟨(4979012/9847487),(28731998/29542461),0,0⟩ : CertField) = scaled n543 29542461 := by decide +kernel
private def n544 : IntField := ⟨207179,0,0,(-3915)⟩
private theorem pos544 : (0:ℤ) < 57974 := by decide +kernel
private theorem cp544 : (⟨(29597/8282),0,0,(-3915/57974)⟩ : CertField) = scaled n544 57974 := by decide +kernel
private def n545 : IntField := ⟨12288129,0,0,(-983651)⟩
private theorem pos545 : (0:ℤ) < 209049862 := by decide +kernel
private theorem cp545 : (⟨(1755447/29864266),0,0,(-983651/209049862)⟩ : CertField) = scaled n545 209049862 := by decide +kernel
private def n546 : IntField := ⟨58431,0,0,6527⟩
private theorem pos546 : (0:ℤ) < 1843390 := by decide +kernel
private theorem cp546 : (⟨(58431/1843390),0,0,(6527/1843390)⟩ : CertField) = scaled n546 1843390 := by decide +kernel
private def n547 : IntField := ⟨17591,0,0,1957⟩
private theorem pos547 : (0:ℤ) < 502670 := by decide +kernel
private theorem cp547 : (⟨(2513/71810),0,0,(1957/502670)⟩ : CertField) = scaled n547 502670 := by decide +kernel
private def n548 : IntField := ⟨(-19962981),46792268,0,0⟩
private theorem pos548 : (0:ℤ) < 770972124 := by decide +kernel
private theorem cp548 : (⟨(-6654327/256990708),(11698067/192743031),0,0⟩ : CertField) = scaled n548 770972124 := by decide +kernel
private def n549 : IntField := ⟨86016903,0,0,(-6885557)⟩
private theorem pos549 : (0:ℤ) < 746606650 := by decide +kernel
private theorem cp549 : (⟨(86016903/746606650),0,0,(-6885557/746606650)⟩ : CertField) = scaled n549 746606650 := by decide +kernel
private def n550 : IntField := ⟨73300124,183314232,0,0⟩
private theorem pos550 : (0:ℤ) < 312797329 := by decide +kernel
private theorem cp550 : (⟨(73300124/312797329),(183314232/312797329),0,0⟩ : CertField) = scaled n550 312797329 := by decide +kernel
private def n551 : IntField := ⟨63629565,0,0,5472215⟩
private theorem pos551 : (0:ℤ) < 65710974 := by decide +kernel
private theorem cp551 : (⟨(21209855/21903658),0,0,(781745/9387282)⟩ : CertField) = scaled n551 65710974 := by decide +kernel
private def n552 : IntField := ⟨89081391,0,0,7661101⟩
private theorem pos552 : (0:ℤ) < 46936410 := by decide +kernel
private theorem cp552 : (⟨(29693797/15645470),0,0,(7661101/46936410)⟩ : CertField) = scaled n552 46936410 := by decide +kernel
private def n553 : IntField := ⟨35613,0,0,(-5933)⟩
private theorem pos553 : (0:ℤ) < 4062 := by decide +kernel
private theorem cp553 : (⟨(11871/1354),0,0,(-5933/4062)⟩ : CertField) = scaled n553 4062 := by decide +kernel
private def n554 : IntField := ⟨223209,0,0,(-37115)⟩
private theorem pos554 : (0:ℤ) < 28434 := by decide +kernel
private theorem cp554 : (⟨(10629/1354),0,0,(-37115/28434)⟩ : CertField) = scaled n554 28434 := by decide +kernel
private def n555 : IntField := ⟨20305875,0,0,3249835⟩
private theorem pos555 : (0:ℤ) < 67856138 := by decide +kernel
private theorem cp555 : (⟨(20305875/67856138),0,0,(3249835/67856138)⟩ : CertField) = scaled n555 67856138 := by decide +kernel
private def n556 : IntField := ⟨28428225,0,0,4549769⟩
private theorem pos556 : (0:ℤ) < 48468670 := by decide +kernel
private theorem cp556 : (⟨(5685645/9693734),0,0,(4549769/48468670)⟩ : CertField) = scaled n556 48468670 := by decide +kernel
private def n557 : IntField := ⟨175287,0,0,17711⟩
private theorem pos557 : (0:ℤ) < 323162 := by decide +kernel
private theorem cp557 : (⟨(25041/46166),0,0,(17711/323162)⟩ : CertField) = scaled n557 323162 := by decide +kernel
private def n558 : IntField := ⟨45661,0,0,1296⟩
private theorem pos558 : (0:ℤ) < 161581 := by decide +kernel
private theorem cp558 : (⟨(6523/23083),0,0,(1296/161581)⟩ : CertField) = scaled n558 161581 := by decide +kernel
private def n559 : IntField := ⟨(-772516),2303835,0,0⟩
private theorem pos559 : (0:ℤ) < 7488217 := by decide +kernel
private theorem cp559 : (⟨(-772516/7488217),(2303835/7488217),0,0⟩ : CertField) = scaled n559 7488217 := by decide +kernel
private def n560 : IntField := ⟨(-6787128),13542941,0,0⟩
private theorem pos560 : (0:ℤ) < 35398844 := by decide +kernel
private theorem cp560 : (⟨(-1696782/8849711),(13542941/35398844),0,0⟩ : CertField) = scaled n560 35398844 := by decide +kernel
private def n561 : IntField := ⟨7755571,33363284,0,0⟩
private theorem pos561 : (0:ℤ) < 132663949 := by decide +kernel
private theorem cp561 : (⟨(7755571/132663949),(33363284/132663949),0,0⟩ : CertField) = scaled n561 132663949 := by decide +kernel
private def n562 : IntField := ⟨40849,118920,0,0⟩
private theorem pos562 : (0:ℤ) < 30251 := by decide +kernel
private theorem cp562 : (⟨(40849/30251),(118920/30251),0,0⟩ : CertField) = scaled n562 30251 := by decide +kernel
private def n563 : IntField := ⟨(-14877963),66978287,0,0⟩
private theorem pos563 : (0:ℤ) < 14248221 := by decide +kernel
private theorem cp563 : (⟨(-4959321/4749407),(66978287/14248221),0,0⟩ : CertField) = scaled n563 14248221 := by decide +kernel
private def n564 : IntField := ⟨9257,(-1),0,0⟩
private theorem pos564 : (0:ℤ) < 34318 := by decide +kernel
private theorem cp564 : (⟨(9257/34318),(-1/34318),0,0⟩ : CertField) = scaled n564 34318 := by decide +kernel
private def n565 : IntField := ⟨165810,323594,0,0⟩
private theorem pos565 : (0:ℤ) < 97513 := by decide +kernel
private theorem cp565 : (⟨(165810/97513),(323594/97513),0,0⟩ : CertField) = scaled n565 97513 := by decide +kernel
private def n566 : IntField := ⟨9471,0,0,(-202)⟩
private theorem pos566 : (0:ℤ) < 777 := by decide +kernel
private theorem cp566 : (⟨(451/37),0,0,(-202/777)⟩ : CertField) = scaled n566 777 := by decide +kernel
private def n567 : IntField := ⟨481577,0,0,34118⟩
private theorem pos567 : (0:ℤ) < 76405 := by decide +kernel
private theorem cp567 : (⟨(481577/76405),0,0,(4874/10915)⟩ : CertField) = scaled n567 76405 := by decide +kernel
private def n568 : IntField := ⟨3371039,0,0,238826⟩
private theorem pos568 : (0:ℤ) < 272875 := by decide +kernel
private theorem cp568 : (⟨(3371039/272875),0,0,(238826/272875)⟩ : CertField) = scaled n568 272875 := by decide +kernel
private def n569 : IntField := ⟨2567,0,0,(-58)⟩
private theorem pos569 : (0:ℤ) < 185 := by decide +kernel
private theorem cp569 : (⟨(2567/185),0,0,(-58/185)⟩ : CertField) = scaled n569 185 := by decide +kernel
private def n570 : IntField := ⟨6303825,0,0,(-4975)⟩
private theorem pos570 : (0:ℤ) < 65508114 := by decide +kernel
private theorem cp570 : (⟨(2101275/21836038),0,0,(-4975/65508114)⟩ : CertField) = scaled n570 65508114 := by decide +kernel
private def n571 : IntField := ⟨15099,0,0,1⟩
private theorem pos571 : (0:ℤ) < 41226 := by decide +kernel
private theorem cp571 : (⟨(5033/13742),0,0,(1/41226)⟩ : CertField) = scaled n571 41226 := by decide +kernel
private def n572 : IntField := ⟨1169,0,0,(-1)⟩
private theorem pos572 : (0:ℤ) < 3178 := by decide +kernel
private theorem cp572 : (⟨(167/454),0,0,(-1/3178)⟩ : CertField) = scaled n572 3178 := by decide +kernel
private def n573 : IntField := ⟨191121,0,0,421⟩
private theorem pos573 : (0:ℤ) < 1439634 := by decide +kernel
private theorem cp573 : (⟨(9101/68554),0,0,(421/1439634)⟩ : CertField) = scaled n573 1439634 := by decide +kernel
private def n574 : IntField := ⟨327,0,0,1⟩
private theorem pos574 : (0:ℤ) < 906 := by decide +kernel
private theorem cp574 : (⟨(109/302),0,0,(1/906)⟩ : CertField) = scaled n574 906 := by decide +kernel
private def n575 : IntField := ⟨(-4002949),11391205,0,0⟩
private theorem pos575 : (0:ℤ) < 91184291 := by decide +kernel
private theorem cp575 : (⟨(-4002949/91184291),(11391205/91184291),0,0⟩ : CertField) = scaled n575 91184291 := by decide +kernel
private def n576 : IntField := ⟨856,1,0,0⟩
private theorem pos576 : (0:ℤ) < 2341 := by decide +kernel
private theorem cp576 : (⟨(856/2341),(1/2341),0,0⟩ : CertField) = scaled n576 2341 := by decide +kernel
private def n577 : IntField := ⟨1301,(-1),0,0⟩
private theorem pos577 : (0:ℤ) < 3541 := by decide +kernel
private theorem cp577 : (⟨(1301/3541),(-1/3541),0,0⟩ : CertField) = scaled n577 3541 := by decide +kernel
private def n578 : IntField := ⟨(-34615287),67024319,0,0⟩
private theorem pos578 : (0:ℤ) < 431053012 := by decide +kernel
private theorem cp578 : (⟨(-34615287/431053012),(67024319/431053012),0,0⟩ : CertField) = scaled n578 431053012 := by decide +kernel
private def n579 : IntField := ⟨2942763,74695124,0,0⟩
private theorem pos579 : (0:ℤ) < 676813533 := by decide +kernel
private theorem cp579 : (⟨(980921/225604511),(74695124/676813533),0,0⟩ : CertField) = scaled n579 676813533 := by decide +kernel
private def n580 : IntField := ⟨19293,(-1),0,0⟩
private theorem pos580 : (0:ℤ) < 52566 := by decide +kernel
private theorem cp580 : (⟨(6431/17522),(-1/52566),0,0⟩ : CertField) = scaled n580 52566 := by decide +kernel
private def n581 : IntField := ⟨9352415,0,0,950325⟩
private theorem pos581 : (0:ℤ) < 73186666 := by decide +kernel
private theorem cp581 : (⟨(9352415/73186666),0,0,(950325/73186666)⟩ : CertField) = scaled n581 73186666 := by decide +kernel
private def n582 : IntField := ⟨18303,0,0,(-1)⟩
private theorem pos582 : (0:ℤ) < 49866 := by decide +kernel
private theorem cp582 : (⟨(6101/16622),0,0,(-1/49866)⟩ : CertField) = scaled n582 49866 := by decide +kernel
private def n583 : IntField := ⟨1765071,0,0,(-1393)⟩
private theorem pos583 : (0:ℤ) < 9358302 := by decide +kernel
private theorem cp583 : (⟨(588357/3119434),0,0,(-1393/9358302)⟩ : CertField) = scaled n583 9358302 := by decide +kernel
private def n584 : IntField := ⟨2343295,4442563,0,0⟩
private theorem pos584 : (0:ℤ) < 3066986 := by decide +kernel
private theorem cp584 : (⟨(2343295/3066986),(4442563/3066986),0,0⟩ : CertField) = scaled n584 3066986 := by decide +kernel
private def n585 : IntField := ⟨4119731,0,0,(-636579)⟩
private theorem pos585 : (0:ℤ) < 349762 := by decide +kernel
private theorem cp585 : (⟨(588533/49966),0,0,(-636579/349762)⟩ : CertField) = scaled n585 349762 := by decide +kernel
private def n586 : IntField := ⟨8711,0,0,(-1)⟩
private theorem pos586 : (0:ℤ) < 32290 := by decide +kernel
private theorem cp586 : (⟨(8711/32290),0,0,(-1/32290)⟩ : CertField) = scaled n586 32290 := by decide +kernel
private def n587 : IntField := ⟨4119731,0,0,(-636579)⟩
private theorem pos587 : (0:ℤ) < 178450 := by decide +kernel
private theorem cp587 : (⟨(4119731/178450),0,0,(-636579/178450)⟩ : CertField) = scaled n587 178450 := by decide +kernel
private def n588 : IntField := ⟨36253,0,0,(-3393)⟩
private theorem pos588 : (0:ℤ) < 4690 := by decide +kernel
private theorem cp588 : (⟨(5179/670),0,0,(-3393/4690)⟩ : CertField) = scaled n588 4690 := by decide +kernel
private def n589 : IntField := ⟨3102587,28971396,0,0⟩
private theorem pos589 : (0:ℤ) < 18519877 := by decide +kernel
private theorem cp589 : (⟨(3102587/18519877),(28971396/18519877),0,0⟩ : CertField) = scaled n589 18519877 := by decide +kernel
private def n590 : IntField := ⟨10229,1,0,0⟩
private theorem pos590 : (0:ℤ) < 38062 := by decide +kernel
private theorem cp590 : (⟨(10229/38062),(1/38062),0,0⟩ : CertField) = scaled n590 38062 := by decide +kernel
private def n591 : IntField := ⟨43953010,57080994,0,0⟩
private theorem pos591 : (0:ℤ) < 47361431 := by decide +kernel
private theorem cp591 : (⟨(43953010/47361431),(57080994/47361431),0,0⟩ : CertField) = scaled n591 47361431 := by decide +kernel
private def ivec1 : Fin 3 → IntField := fun j => blendN 144 rE rF n3 n4 10 510 j
private def dvec1 : Fin 3 → ℤ := fun _ => 144*10*510
private def vec1 : Fin 3 → CertField := fun j => scaled (ivec1 j) (dvec1 j)
private theorem dpos1 : ∀ j, (0:ℤ) < dvec1 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos4
private theorem vp1 : productBlend (1/4) (1/3) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(63/170),0,0,(-1/510)⟩ : CertField) = vec1 := by
  rw [cp3, cp4]
  exact r_blend_scaled n3 n4 10 510 pos3 pos4
private def ivec2 : Fin 3 → IntField := fun j => blendN 400 sE sF n5 n6 13 13 j
private def dvec2 : Fin 3 → ℤ := fun _ => 400*13*13
private def vec2 : Fin 3 → CertField := fun j => scaled (ivec2 j) (dvec2 j)
private theorem dpos2 : ∀ j, (0:ℤ) < dvec2 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos5) pos6
private theorem vp2 : productBlend (3/4) (4/5) (⟨(4/13),(1/13),0,0⟩ : CertField) (⟨(9/13),(-1/13),0,0⟩ : CertField) = vec2 := by
  rw [cp5, cp6]
  exact s_blend_scaled n5 n6 13 13 pos5 pos6
private def ivec3 : Fin 3 → IntField := fun j => blendN 144 rE rF n7 n8 22 1 j
private def dvec3 : Fin 3 → ℤ := fun _ => 144*22*1
private def vec3 : Fin 3 → CertField := fun j => scaled (ivec3 j) (dvec3 j)
private theorem dpos3 : ∀ j, (0:ℤ) < dvec3 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos7) pos8
private theorem vp3 : productBlend (1/4) (1/3) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨2,-1,0,0⟩ : CertField) = vec3 := by
  rw [cp7, cp8]
  exact r_blend_scaled n7 n8 22 1 pos7 pos8
private def ivec4 : Fin 3 → IntField := fun j => blendN 400 sE sF n9 n10 118 430 j
private def dvec4 : Fin 3 → ℤ := fun _ => 400*118*430
private def vec4 : Fin 3 → CertField := fun j => scaled (ivec4 j) (dvec4 j)
private theorem dpos4 : ∀ j, (0:ℤ) < dvec4 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos9) pos10
private theorem vp4 : productBlend (3/4) (4/5) (⟨(27/118),0,0,(1/118)⟩ : CertField) (⟨(121/430),0,0,(-1/430)⟩ : CertField) = vec4 := by
  rw [cp9, cp10]
  exact s_blend_scaled n9 n10 118 430 pos9 pos10
private def ivec5 : Fin 3 → IntField := fun j => blendN 144 rE rF n3 n13 10 94 j
private def dvec5 : Fin 3 → ℤ := fun _ => 144*10*94
private def vec5 : Fin 3 → CertField := fun j => scaled (ivec5 j) (dvec5 j)
private theorem dpos5 : ∀ j, (0:ℤ) < dvec5 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos13
private theorem vp5 : productBlend (1/4) (1/3) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(35/94),(1/94),0,0⟩ : CertField) = vec5 := by
  rw [cp3, cp13]
  exact r_blend_scaled n3 n13 10 94 pos3 pos13
private def ivec6 : Fin 3 → IntField := fun j => blendN 400 sE sF n3 n7 10 22 j
private def dvec6 : Fin 3 → ℤ := fun _ => 400*10*22
private def vec6 : Fin 3 → CertField := fun j => scaled (ivec6 j) (dvec6 j)
private theorem dpos6 : ∀ j, (0:ℤ) < dvec6 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos7
private theorem vp6 : productBlend (3/4) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(5/22),(1/22),0,0⟩ : CertField) = vec6 := by
  rw [cp3, cp7]
  exact s_blend_scaled n3 n7 10 22 pos3 pos7
private def ivec7 : Fin 3 → IntField := fun j => blendN 400 sE sF n15 n16 166 94 j
private def dvec7 : Fin 3 → ℤ := fun _ => 400*166*94
private def vec7 : Fin 3 → CertField := fun j => scaled (ivec7 j) (dvec7 j)
private theorem dpos7 : ∀ j, (0:ℤ) < dvec7 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos15) pos16
private theorem vp7 : productBlend (3/4) (4/5) (⟨(41/166),0,0,(1/166)⟩ : CertField) (⟨(31/94),0,0,(-1/94)⟩ : CertField) = vec7 := by
  rw [cp15, cp16]
  exact s_blend_scaled n15 n16 166 94 pos15 pos16
private def ivec8 : Fin 3 → IntField := fun j => blendN 144 rE rF n19 n20 70 222 j
private def dvec8 : Fin 3 → ℤ := fun _ => 144*70*222
private def vec8 : Fin 3 → CertField := fun j => scaled (ivec8 j) (dvec8 j)
private theorem dpos8 : ∀ j, (0:ℤ) < dvec8 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos19) pos20
private theorem vp8 : productBlend (1/4) (1/3) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(29/74),0,0,(-1/222)⟩ : CertField) = vec8 := by
  rw [cp19, cp20]
  exact r_blend_scaled n19 n20 70 222 pos19 pos20
private def ivec9 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n24 150 82 j
private def dvec9 : Fin 3 → ℤ := fun _ => 400*150*82
private def vec9 : Fin 3 → CertField := fun j => scaled (ivec9 j) (dvec9 j)
private theorem dpos9 : ∀ j, (0:ℤ) < dvec9 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos24
private theorem vp9 : productBlend (3/4) (4/5) (⟨(13/50),0,0,(1/150)⟩ : CertField) (⟨(29/82),0,0,(-1/82)⟩ : CertField) = vec9 := by
  rw [cp23, cp24]
  exact s_blend_scaled n23 n24 150 82 pos23 pos24
private def ivec10 : Fin 3 → IntField := fun j => blendN 400 sE sF n27 n28 402 34 j
private def dvec10 : Fin 3 → ℤ := fun _ => 400*402*34
private def vec10 : Fin 3 → CertField := fun j => scaled (ivec10 j) (dvec10 j)
private theorem dpos10 : ∀ j, (0:ℤ) < dvec10 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos27) pos28
private theorem vp10 : productBlend (3/4) (4/5) (⟨(39/134),0,0,(1/402)⟩ : CertField) (⟨(15/34),0,0,(-1/34)⟩ : CertField) = vec10 := by
  rw [cp27, cp28]
  exact s_blend_scaled n27 n28 402 34 pos27 pos28
private def ivec11 : Fin 3 → IntField := fun j => blendN 144 rE rF n33 n34 94 262 j
private def dvec11 : Fin 3 → ℤ := fun _ => 144*94*262
private def vec11 : Fin 3 → CertField := fun j => scaled (ivec11 j) (dvec11 j)
private theorem dpos11 : ∀ j, (0:ℤ) < dvec11 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos33) pos34
private theorem vp11 : productBlend (1/4) (1/3) (⟨(31/94),0,0,(1/94)⟩ : CertField) (⟨(105/262),0,0,(-1/262)⟩ : CertField) = vec11 := by
  rw [cp33, cp34]
  exact r_blend_scaled n33 n34 94 262 pos33 pos34
private def ivec12 : Fin 3 → IntField := fun j => blendN 144 rE rF n37 n38 574 202 j
private def dvec12 : Fin 3 → ℤ := fun _ => 144*574*202
private def vec12 : Fin 3 → CertField := fun j => scaled (ivec12 j) (dvec12 j)
private theorem dpos12 : ∀ j, (0:ℤ) < dvec12 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos37) pos38
private theorem vp12 : productBlend (1/4) (1/3) (⟨(31/82),0,0,(1/574)⟩ : CertField) (⟨(83/202),0,0,(-1/202)⟩ : CertField) = vec12 := by
  rw [cp37, cp38]
  exact r_blend_scaled n37 n38 574 202 pos37 pos38
private def ivec13 : Fin 3 → IntField := fun j => blendN 144 rE rF n47 n48 1354 42 j
private def dvec13 : Fin 3 → ℤ := fun _ => 144*1354*42
private def vec13 : Fin 3 → CertField := fun j => scaled (ivec13 j) (dvec13 j)
private theorem dpos13 : ∀ j, (0:ℤ) < dvec13 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos47) pos48
private theorem vp13 : productBlend (1/4) (1/3) (⟨(523/1354),0,0,(1/1354)⟩ : CertField) (⟨(1/2),0,0,(-1/42)⟩ : CertField) = vec13 := by
  rw [cp47, cp48]
  exact r_blend_scaled n47 n48 1354 42 pos47 pos48
private def ivec14 : Fin 3 → IntField := fun j => blendN 144 rE rF n7 n53 22 12598 j
private def dvec14 : Fin 3 → ℤ := fun _ => 144*22*12598
private def vec14 : Fin 3 → CertField := fun j => scaled (ivec14 j) (dvec14 j)
private theorem dpos14 : ∀ j, (0:ℤ) < dvec14 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos7) pos53
private theorem vp14 : productBlend (1/4) (1/3) (⟨(5/22),(1/22),0,0⟩ : CertField) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = vec14 := by
  rw [cp7, cp53]
  exact r_blend_scaled n7 n53 22 12598 pos7 pos53
private def ivec15 : Fin 3 → IntField := fun j => blendN 400 sE sF n54 n5 1006 13 j
private def dvec15 : Fin 3 → ℤ := fun _ => 400*1006*13
private def vec15 : Fin 3 → CertField := fun j => scaled (ivec15 j) (dvec15 j)
private theorem dpos15 : ∀ j, (0:ℤ) < dvec15 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos54) pos5
private theorem vp15 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(4/13),(1/13),0,0⟩ : CertField) = vec15 := by
  rw [cp54, cp5]
  exact s_blend_scaled n54 n5 1006 13 pos54 pos5
private def ivec16 : Fin 3 → IntField := fun j => blendN 400 sE sF n57 n58 202 10 j
private def dvec16 : Fin 3 → ℤ := fun _ => 400*202*10
private def vec16 : Fin 3 → CertField := fun j => scaled (ivec16 j) (dvec16 j)
private theorem dpos16 : ∀ j, (0:ℤ) < dvec16 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos57) pos58
private theorem vp16 : productBlend (3/4) (4/5) (⟨(83/202),0,0,(1/202)⟩ : CertField) (⟨(9/10),0,0,(-1/10)⟩ : CertField) = vec16 := by
  rw [cp57, cp58]
  exact s_blend_scaled n57 n58 202 10 pos57 pos58
private def ivec17 : Fin 3 → IntField := fun j => blendN 144 rE rF n27 n28 402 34 j
private def dvec17 : Fin 3 → ℤ := fun _ => 144*402*34
private def vec17 : Fin 3 → CertField := fun j => scaled (ivec17 j) (dvec17 j)
private theorem dpos17 : ∀ j, (0:ℤ) < dvec17 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos27) pos28
private theorem vp17 : productBlend (1/4) (1/3) (⟨(39/134),0,0,(1/402)⟩ : CertField) (⟨(15/34),0,0,(-1/34)⟩ : CertField) = vec17 := by
  rw [cp27, cp28]
  exact r_blend_scaled n27 n28 402 34 pos27 pos28
private def ivec18 : Fin 3 → IntField := fun j => blendN 400 sE sF n54 n59 1006 214 j
private def dvec18 : Fin 3 → ℤ := fun _ => 400*1006*214
private def vec18 : Fin 3 → CertField := fun j => scaled (ivec18 j) (dvec18 j)
private theorem dpos18 : ∀ j, (0:ℤ) < dvec18 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos54) pos59
private theorem vp18 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(89/214),(1/214),0,0⟩ : CertField) = vec18 := by
  rw [cp54, cp59]
  exact s_blend_scaled n54 n59 1006 214 pos54 pos59
private def ivec19 : Fin 3 → IntField := fun j => blendN 144 rE rF n63 n53 429 12598 j
private def dvec19 : Fin 3 → ℤ := fun _ => 144*429*12598
private def vec19 : Fin 3 → CertField := fun j => scaled (ivec19 j) (dvec19 j)
private theorem dpos19 : ∀ j, (0:ℤ) < dvec19 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos63) pos53
private theorem vp19 : productBlend (1/4) (1/3) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = vec19 := by
  rw [cp63, cp53]
  exact r_blend_scaled n63 n53 429 12598 pos63 pos53
private def ivec20 : Fin 3 → IntField := fun j => blendN 400 sE sF n3 n58 10 10 j
private def dvec20 : Fin 3 → ℤ := fun _ => 400*10*10
private def vec20 : Fin 3 → CertField := fun j => scaled (ivec20 j) (dvec20 j)
private theorem dpos20 : ∀ j, (0:ℤ) < dvec20 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos58
private theorem vp20 : productBlend (3/4) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(9/10),0,0,(-1/10)⟩ : CertField) = vec20 := by
  rw [cp3, cp58]
  exact s_blend_scaled n3 n58 10 10 pos3 pos58
private def ivec21 : Fin 3 → IntField := fun j => blendN 144 rE rF n64 n28 6 34 j
private def dvec21 : Fin 3 → ℤ := fun _ => 144*6*34
private def vec21 : Fin 3 → CertField := fun j => scaled (ivec21 j) (dvec21 j)
private theorem dpos21 : ∀ j, (0:ℤ) < dvec21 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos64) pos28
private theorem vp21 : productBlend (1/4) (1/3) (⟨(-1/2),0,0,(1/6)⟩ : CertField) (⟨(15/34),0,0,(-1/34)⟩ : CertField) = vec21 := by
  rw [cp64, cp28]
  exact r_blend_scaled n64 n28 6 34 pos64 pos28
private def ivec22 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n67 313 37 j
private def dvec22 : Fin 3 → ℤ := fun _ => 400*313*37
private def vec22 : Fin 3 → CertField := fun j => scaled (ivec22 j) (dvec22 j)
private theorem dpos22 : ∀ j, (0:ℤ) < dvec22 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos67
private theorem vp22 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec22 := by
  rw [cp66, cp67]
  exact s_blend_scaled n66 n67 313 37 pos66 pos67
private def ivec23 : Fin 3 → IntField := fun j => blendN 144 rE rF n54 n68 1006 262 j
private def dvec23 : Fin 3 → ℤ := fun _ => 144*1006*262
private def vec23 : Fin 3 → CertField := fun j => scaled (ivec23 j) (dvec23 j)
private theorem dpos23 : ∀ j, (0:ℤ) < dvec23 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos54) pos68
private theorem vp23 : productBlend (1/4) (1/3) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(93/262),(1/262),0,0⟩ : CertField) = vec23 := by
  rw [cp54, cp68]
  exact r_blend_scaled n54 n68 1006 262 pos54 pos68
private def ivec24 : Fin 3 → IntField := fun j => blendN 400 sE sF n70 n67 5893 37 j
private def dvec24 : Fin 3 → ℤ := fun _ => 400*5893*37
private def vec24 : Fin 3 → CertField := fun j => scaled (ivec24 j) (dvec24 j)
private theorem dpos24 : ∀ j, (0:ℤ) < dvec24 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos70) pos67
private theorem vp24 : productBlend (3/4) (4/5) (⟨(1590/5893),(1/5893),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec24 := by
  rw [cp70, cp67]
  exact s_blend_scaled n70 n67 5893 37 pos70 pos67
private def ivec25 : Fin 3 → IntField := fun j => blendN 400 sE sF n72 n10 5530 430 j
private def dvec25 : Fin 3 → ℤ := fun _ => 400*5530*430
private def vec25 : Fin 3 → CertField := fun j => scaled (ivec25 j) (dvec25 j)
private theorem dpos25 : ∀ j, (0:ℤ) < dvec25 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos72) pos10
private theorem vp25 : productBlend (3/4) (4/5) (⟨(213/790),0,0,(1/5530)⟩ : CertField) (⟨(121/430),0,0,(-1/430)⟩ : CertField) = vec25 := by
  rw [cp72, cp10]
  exact s_blend_scaled n72 n10 5530 430 pos72 pos10
private def ivec26 : Fin 3 → IntField := fun j => blendN 144 rE rF n73 n4 5158 510 j
private def dvec26 : Fin 3 → ℤ := fun _ => 144*5158*510
private def vec26 : Fin 3 → CertField := fun j => scaled (ivec26 j) (dvec26 j)
private theorem dpos26 : ∀ j, (0:ℤ) < dvec26 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos73) pos4
private theorem vp26 : productBlend (1/4) (1/3) (⟨(1859/5158),0,0,(1/5158)⟩ : CertField) (⟨(63/170),0,0,(-1/510)⟩ : CertField) = vec26 := by
  rw [cp73, cp4]
  exact r_blend_scaled n73 n4 5158 510 pos73 pos4
private def ivec27 : Fin 3 → IntField := fun j => blendN 144 rE rF n54 n75 1006 5521 j
private def dvec27 : Fin 3 → ℤ := fun _ => 144*1006*5521
private def vec27 : Fin 3 → CertField := fun j => scaled (ivec27 j) (dvec27 j)
private theorem dpos27 : ∀ j, (0:ℤ) < dvec27 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos54) pos75
private theorem vp27 : productBlend (1/4) (1/3) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(1991/5521),(1/5521),0,0⟩ : CertField) = vec27 := by
  rw [cp54, cp75]
  exact r_blend_scaled n54 n75 1006 5521 pos54 pos75
private def ivec28 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n77 313 478 j
private def dvec28 : Fin 3 → ℤ := fun _ => 400*313*478
private def vec28 : Fin 3 → CertField := fun j => scaled (ivec28 j) (dvec28 j)
private theorem dpos28 : ∀ j, (0:ℤ) < dvec28 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos77
private theorem vp28 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(133/478),(-1/478),0,0⟩ : CertField) = vec28 := by
  rw [cp66, cp77]
  exact s_blend_scaled n66 n77 313 478 pos66 pos77
private def ivec29 : Fin 3 → IntField := fun j => blendN 144 rE rF n68 n53 262 12598 j
private def dvec29 : Fin 3 → ℤ := fun _ => 144*262*12598
private def vec29 : Fin 3 → CertField := fun j => scaled (ivec29 j) (dvec29 j)
private theorem dpos29 : ∀ j, (0:ℤ) < dvec29 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos68) pos53
private theorem vp29 : productBlend (1/4) (1/3) (⟨(93/262),(1/262),0,0⟩ : CertField) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) = vec29 := by
  rw [cp68, cp53]
  exact r_blend_scaled n68 n53 262 12598 pos68 pos53
private def ivec30 : Fin 3 → IntField := fun j => blendN 400 sE sF n82 n83 177 142 j
private def dvec30 : Fin 3 → ℤ := fun _ => 400*177*142
private def vec30 : Fin 3 → CertField := fun j => scaled (ivec30 j) (dvec30 j)
private theorem dpos30 : ∀ j, (0:ℤ) < dvec30 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos82) pos83
private theorem vp30 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec30 := by
  rw [cp82, cp83]
  exact s_blend_scaled n82 n83 177 142 pos82 pos83
private def ivec31 : Fin 3 → IntField := fun j => blendN 144 rE rF n53 n84 12598 169 j
private def dvec31 : Fin 3 → ℤ := fun _ => 144*12598*169
private def vec31 : Fin 3 → CertField := fun j => scaled (ivec31 j) (dvec31 j)
private theorem dpos31 : ∀ j, (0:ℤ) < dvec31 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos53) pos84
private theorem vp31 : productBlend (1/4) (1/3) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(61/169),(1/169),0,0⟩ : CertField) = vec31 := by
  rw [cp53, cp84]
  exact r_blend_scaled n53 n84 12598 169 pos53 pos84
private def ivec32 : Fin 3 → IntField := fun j => blendN 144 rE rF n86 n20 2950 222 j
private def dvec32 : Fin 3 → ℤ := fun _ => 144*2950*222
private def vec32 : Fin 3 → CertField := fun j => scaled (ivec32 j) (dvec32 j)
private theorem dpos32 : ∀ j, (0:ℤ) < dvec32 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos86) pos20
private theorem vp32 : productBlend (1/4) (1/3) (⟨(1089/2950),0,0,(1/2950)⟩ : CertField) (⟨(29/74),0,0,(-1/222)⟩ : CertField) = vec32 := by
  rw [cp86, cp20]
  exact r_blend_scaled n86 n20 2950 222 pos86 pos20
private def ivec33 : Fin 3 → IntField := fun j => blendN 400 sE sF n87 n16 2602 94 j
private def dvec33 : Fin 3 → ℤ := fun _ => 400*2602*94
private def vec33 : Fin 3 → CertField := fun j => scaled (ivec33 j) (dvec33 j)
private theorem dpos33 : ∀ j, (0:ℤ) < dvec33 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos87) pos16
private theorem vp33 : productBlend (3/4) (4/5) (⟨(725/2602),0,0,(1/2602)⟩ : CertField) (⟨(31/94),0,0,(-1/94)⟩ : CertField) = vec33 := by
  rw [cp87, cp16]
  exact s_blend_scaled n87 n16 2602 94 pos87 pos16
private def ivec34 : Fin 3 → IntField := fun j => blendN 400 sE sF n89 n83 2749 142 j
private def dvec34 : Fin 3 → ℤ := fun _ => 400*2749*142
private def vec34 : Fin 3 → CertField := fun j => scaled (ivec34 j) (dvec34 j)
private theorem dpos34 : ∀ j, (0:ℤ) < dvec34 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos89) pos83
private theorem vp34 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec34 := by
  rw [cp89, cp83]
  exact s_blend_scaled n89 n83 2749 142 pos89 pos83
private def ivec35 : Fin 3 → IntField := fun j => blendN 144 rE rF n53 n91 12598 3142 j
private def dvec35 : Fin 3 → ℤ := fun _ => 144*12598*3142
private def vec35 : Fin 3 → CertField := fun j => scaled (ivec35 j) (dvec35 j)
private theorem dpos35 : ∀ j, (0:ℤ) < dvec35 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos53) pos91
private theorem vp35 : productBlend (1/4) (1/3) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(1161/3142),(1/3142),0,0⟩ : CertField) = vec35 := by
  rw [cp53, cp91]
  exact r_blend_scaled n53 n91 12598 3142 pos53 pos91
private def ivec36 : Fin 3 → IntField := fun j => blendN 144 rE rF n68 n93 262 537 j
private def dvec36 : Fin 3 → ℤ := fun _ => 144*262*537
private def vec36 : Fin 3 → CertField := fun j => scaled (ivec36 j) (dvec36 j)
private theorem dpos36 : ∀ j, (0:ℤ) < dvec36 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos68) pos93
private theorem vp36 : productBlend (1/4) (1/3) (⟨(93/262),(1/262),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec36 := by
  rw [cp68, cp93]
  exact r_blend_scaled n68 n93 262 537 pos68 pos93
private def ivec37 : Fin 3 → IntField := fun j => blendN 400 sE sF n77 n63 478 429 j
private def dvec37 : Fin 3 → ℤ := fun _ => 400*478*429
private def vec37 : Fin 3 → CertField := fun j => scaled (ivec37 j) (dvec37 j)
private theorem dpos37 : ∀ j, (0:ℤ) < dvec37 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos77) pos63
private theorem vp37 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(42/143),(1/429),0,0⟩ : CertField) = vec37 := by
  rw [cp77, cp63]
  exact s_blend_scaled n77 n63 478 429 pos77 pos63
private def ivec38 : Fin 3 → IntField := fun j => blendN 400 sE sF n15 n96 166 6718 j
private def dvec38 : Fin 3 → ℤ := fun _ => 400*166*6718
private def vec38 : Fin 3 → CertField := fun j => scaled (ivec38 j) (dvec38 j)
private theorem dpos38 : ∀ j, (0:ℤ) < dvec38 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos15) pos96
private theorem vp38 : productBlend (3/4) (4/5) (⟨(41/166),0,0,(1/166)⟩ : CertField) (⟨(1851/6718),0,0,(-1/6718)⟩ : CertField) = vec38 := by
  rw [cp15, cp96]
  exact s_blend_scaled n15 n96 166 6718 pos15 pos96
private def ivec39 : Fin 3 → IntField := fun j => blendN 144 rE rF n19 n97 70 7138 j
private def dvec39 : Fin 3 → ℤ := fun _ => 144*70*7138
private def vec39 : Fin 3 → CertField := fun j => scaled (ivec39 j) (dvec39 j)
private theorem dpos39 : ∀ j, (0:ℤ) < dvec39 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos19) pos97
private theorem vp39 : productBlend (1/4) (1/3) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(2615/7138),0,0,(-1/7138)⟩ : CertField) = vec39 := by
  rw [cp19, cp97]
  exact r_blend_scaled n19 n97 70 7138 pos19 pos97
private def ivec40 : Fin 3 → IntField := fun j => blendN 400 sE sF n98 n63 7081 429 j
private def dvec40 : Fin 3 → ℤ := fun _ => 400*7081*429
private def vec40 : Fin 3 → CertField := fun j => scaled (ivec40 j) (dvec40 j)
private theorem dpos40 : ∀ j, (0:ℤ) < dvec40 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos63
private theorem vp40 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(42/143),(1/429),0,0⟩ : CertField) = vec40 := by
  rw [cp98, cp63]
  exact s_blend_scaled n98 n63 7081 429 pos98 pos63
private def ivec41 : Fin 3 → IntField := fun j => blendN 144 rE rF n68 n102 262 7501 j
private def dvec41 : Fin 3 → ℤ := fun _ => 144*262*7501
private def vec41 : Fin 3 → CertField := fun j => scaled (ivec41 j) (dvec41 j)
private theorem dpos41 : ∀ j, (0:ℤ) < dvec41 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos68) pos102
private theorem vp41 : productBlend (1/4) (1/3) (⟨(93/262),(1/262),0,0⟩ : CertField) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = vec41 := by
  rw [cp68, cp102]
  exact r_blend_scaled n68 n102 262 7501 pos68 pos102
private def ivec42 : Fin 3 → IntField := fun j => blendN 400 sE sF n105 n24 5794 82 j
private def dvec42 : Fin 3 → ℤ := fun _ => 400*5794*82
private def vec42 : Fin 3 → CertField := fun j => scaled (ivec42 j) (dvec42 j)
private theorem dpos42 : ∀ j, (0:ℤ) < dvec42 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos105) pos24
private theorem vp42 : productBlend (3/4) (4/5) (⟨(1719/5794),0,0,(1/5794)⟩ : CertField) (⟨(29/82),0,0,(-1/82)⟩ : CertField) = vec42 := by
  rw [cp105, cp24]
  exact s_blend_scaled n105 n24 5794 82 pos105 pos24
private def ivec43 : Fin 3 → IntField := fun j => blendN 400 sE sF n77 n106 478 6094 j
private def dvec43 : Fin 3 → ℤ := fun _ => 400*478*6094
private def vec43 : Fin 3 → CertField := fun j => scaled (ivec43 j) (dvec43 j)
private theorem dpos43 : ∀ j, (0:ℤ) < dvec43 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos77) pos106
private theorem vp43 : productBlend (3/4) (4/5) (⟨(133/478),(-1/478),0,0⟩ : CertField) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) = vec43 := by
  rw [cp77, cp106]
  exact s_blend_scaled n77 n106 478 6094 pos77 pos106
private def ivec44 : Fin 3 → IntField := fun j => blendN 400 sE sF n98 n106 7081 6094 j
private def dvec44 : Fin 3 → ℤ := fun _ => 400*7081*6094
private def vec44 : Fin 3 → CertField := fun j => scaled (ivec44 j) (dvec44 j)
private theorem dpos44 : ∀ j, (0:ℤ) < dvec44 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos98) pos106
private theorem vp44 : productBlend (3/4) (4/5) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) = vec44 := by
  rw [cp98, cp106]
  exact s_blend_scaled n98 n106 7081 6094 pos98 pos106
private def ivec45 : Fin 3 → IntField := fun j => blendN 144 rE rF n75 n93 5521 537 j
private def dvec45 : Fin 3 → ℤ := fun _ => 144*5521*537
private def vec45 : Fin 3 → CertField := fun j => scaled (ivec45 j) (dvec45 j)
private theorem dpos45 : ∀ j, (0:ℤ) < dvec45 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos75) pos93
private theorem vp45 : productBlend (1/4) (1/3) (⟨(1991/5521),(1/5521),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec45 := by
  rw [cp75, cp93]
  exact r_blend_scaled n75 n93 5521 537 pos75 pos93
private def ivec46 : Fin 3 → IntField := fun j => blendN 400 sE sF n112 n24 514 82 j
private def dvec46 : Fin 3 → ℤ := fun _ => 400*514*82
private def vec46 : Fin 3 → CertField := fun j => scaled (ivec46 j) (dvec46 j)
private theorem dpos46 : ∀ j, (0:ℤ) < dvec46 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos112) pos24
private theorem vp46 : productBlend (3/4) (4/5) (⟨(147/514),0,0,(1/514)⟩ : CertField) (⟨(29/82),0,0,(-1/82)⟩ : CertField) = vec46 := by
  rw [cp112, cp24]
  exact s_blend_scaled n112 n24 514 82 pos112 pos24
private def ivec47 : Fin 3 → IntField := fun j => blendN 144 rE rF n75 n102 5521 7501 j
private def dvec47 : Fin 3 → ℤ := fun _ => 144*5521*7501
private def vec47 : Fin 3 → CertField := fun j => scaled (ivec47 j) (dvec47 j)
private theorem dpos47 : ∀ j, (0:ℤ) < dvec47 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos75) pos102
private theorem vp47 : productBlend (1/4) (1/3) (⟨(1991/5521),(1/5521),0,0⟩ : CertField) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = vec47 := by
  rw [cp75, cp102]
  exact r_blend_scaled n75 n102 5521 7501 pos75 pos102
private def ivec48 : Fin 3 → IntField := fun j => blendN 400 sE sF n63 n116 429 229 j
private def dvec48 : Fin 3 → ℤ := fun _ => 400*429*229
private def vec48 : Fin 3 → CertField := fun j => scaled (ivec48 j) (dvec48 j)
private theorem dpos48 : ∀ j, (0:ℤ) < dvec48 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos63) pos116
private theorem vp48 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec48 := by
  rw [cp63, cp116]
  exact s_blend_scaled n63 n116 429 229 pos63 pos116
private def ivec49 : Fin 3 → IntField := fun j => blendN 400 sE sF n23 n119 150 2350 j
private def dvec49 : Fin 3 → ℤ := fun _ => 400*150*2350
private def vec49 : Fin 3 → CertField := fun j => scaled (ivec49 j) (dvec49 j)
private theorem dpos49 : ∀ j, (0:ℤ) < dvec49 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos23) pos119
private theorem vp49 : productBlend (3/4) (4/5) (⟨(13/50),0,0,(1/150)⟩ : CertField) (⟨(689/2350),0,0,(-1/2350)⟩ : CertField) = vec49 := by
  rw [cp23, cp119]
  exact s_blend_scaled n23 n119 150 2350 pos23 pos119
private def ivec50 : Fin 3 → IntField := fun j => blendN 400 sE sF n121 n122 2497 10753 j
private def dvec50 : Fin 3 → ℤ := fun _ => 400*2497*10753
private def vec50 : Fin 3 → CertField := fun j => scaled (ivec50 j) (dvec50 j)
private theorem dpos50 : ∀ j, (0:ℤ) < dvec50 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos121) pos122
private theorem vp50 : productBlend (3/4) (4/5) (⟨(731/2497),(-1/2497),0,0⟩ : CertField) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = vec50 := by
  rw [cp121, cp122]
  exact s_blend_scaled n121 n122 2497 10753 pos121 pos122
private def ivec51 : Fin 3 → IntField := fun j => blendN 400 sE sF n83 n122 142 10753 j
private def dvec51 : Fin 3 → ℤ := fun _ => 400*142*10753
private def vec51 : Fin 3 → CertField := fun j => scaled (ivec51 j) (dvec51 j)
private theorem dpos51 : ∀ j, (0:ℤ) < dvec51 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos83) pos122
private theorem vp51 : productBlend (3/4) (4/5) (⟨(43/142),(-1/142),0,0⟩ : CertField) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) = vec51 := by
  rw [cp83, cp122]
  exact s_blend_scaled n83 n122 142 10753 pos83 pos122
private def ivec52 : Fin 3 → IntField := fun j => blendN 400 sE sF n106 n116 6094 229 j
private def dvec52 : Fin 3 → ℤ := fun _ => 400*6094*229
private def vec52 : Fin 3 → CertField := fun j => scaled (ivec52 j) (dvec52 j)
private theorem dpos52 : ∀ j, (0:ℤ) < dvec52 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos106) pos116
private theorem vp52 : productBlend (3/4) (4/5) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec52 := by
  rw [cp106, cp116]
  exact s_blend_scaled n106 n116 6094 229 pos106 pos116
private def ivec53 : Fin 3 → IntField := fun j => blendN 144 rE rF n84 n131 169 249 j
private def dvec53 : Fin 3 → ℤ := fun _ => 144*169*249
private def vec53 : Fin 3 → CertField := fun j => scaled (ivec53 j) (dvec53 j)
private theorem dpos53 : ∀ j, (0:ℤ) < dvec53 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos131
private theorem vp53 : productBlend (1/4) (1/3) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec53 := by
  rw [cp84, cp131]
  exact r_blend_scaled n84 n131 169 249 pos84 pos131
private def ivec54 : Fin 3 → IntField := fun j => blendN 144 rE rF n33 n135 94 3526 j
private def dvec54 : Fin 3 → ℤ := fun _ => 144*94*3526
private def vec54 : Fin 3 → CertField := fun j => scaled (ivec54 j) (dvec54 j)
private theorem dpos54 : ∀ j, (0:ℤ) < dvec54 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos33) pos135
private theorem vp54 : productBlend (1/4) (1/3) (⟨(31/94),0,0,(1/94)⟩ : CertField) (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) = vec54 := by
  rw [cp33, cp135]
  exact r_blend_scaled n33 n135 94 3526 pos33 pos135
private def ivec55 : Fin 3 → IntField := fun j => blendN 144 rE rF n84 n139 169 3718 j
private def dvec55 : Fin 3 → ℤ := fun _ => 144*169*3718
private def vec55 : Fin 3 → CertField := fun j => scaled (ivec55 j) (dvec55 j)
private theorem dpos55 : ∀ j, (0:ℤ) < dvec55 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos139
private theorem vp55 : productBlend (1/4) (1/3) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec55 := by
  rw [cp84, cp139]
  exact r_blend_scaled n84 n139 169 3718 pos84 pos139
private def ivec56 : Fin 3 → IntField := fun j => blendN 400 sE sF n15 n140 166 514 j
private def dvec56 : Fin 3 → ℤ := fun _ => 400*166*514
private def vec56 : Fin 3 → CertField := fun j => scaled (ivec56 j) (dvec56 j)
private theorem dpos56 : ∀ j, (0:ℤ) < dvec56 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos15) pos140
private theorem vp56 : productBlend (3/4) (4/5) (⟨(41/166),0,0,(1/166)⟩ : CertField) (⟨(147/514),0,0,(-1/514)⟩ : CertField) = vec56 := by
  rw [cp15, cp140]
  exact s_blend_scaled n15 n140 166 514 pos15 pos140
private def ivec57 : Fin 3 → IntField := fun j => blendN 144 rE rF n91 n131 3142 249 j
private def dvec57 : Fin 3 → ℤ := fun _ => 144*3142*249
private def vec57 : Fin 3 → CertField := fun j => scaled (ivec57 j) (dvec57 j)
private theorem dpos57 : ∀ j, (0:ℤ) < dvec57 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos91) pos131
private theorem vp57 : productBlend (1/4) (1/3) (⟨(1161/3142),(1/3142),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec57 := by
  rw [cp91, cp131]
  exact r_blend_scaled n91 n131 3142 249 pos91 pos131
private def ivec58 : Fin 3 → IntField := fun j => blendN 144 rE rF n91 n139 3142 3718 j
private def dvec58 : Fin 3 → ℤ := fun _ => 144*3142*3718
private def vec58 : Fin 3 → CertField := fun j => scaled (ivec58 j) (dvec58 j)
private theorem dpos58 : ∀ j, (0:ℤ) < dvec58 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos91) pos139
private theorem vp58 : productBlend (1/4) (1/3) (⟨(1161/3142),(1/3142),0,0⟩ : CertField) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) = vec58 := by
  rw [cp91, cp139]
  exact r_blend_scaled n91 n139 3142 3718 pos91 pos139
private def ivec59 : Fin 3 → IntField := fun j => blendN 144 rE rF n152 n34 9250 262 j
private def dvec59 : Fin 3 → ℤ := fun _ => 144*9250*262
private def vec59 : Fin 3 → CertField := fun j => scaled (ivec59 j) (dvec59 j)
private theorem dpos59 : ∀ j, (0:ℤ) < dvec59 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos152) pos34
private theorem vp59 : productBlend (1/4) (1/3) (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) (⟨(105/262),0,0,(-1/262)⟩ : CertField) = vec59 := by
  rw [cp152, cp34]
  exact r_blend_scaled n152 n34 9250 262 pos152 pos34
private def ivec60 : Fin 3 → IntField := fun j => blendN 144 rE rF n93 n153 537 649 j
private def dvec60 : Fin 3 → ℤ := fun _ => 144*537*649
private def vec60 : Fin 3 → CertField := fun j => scaled (ivec60 j) (dvec60 j)
private theorem dpos60 : ∀ j, (0:ℤ) < dvec60 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos93) pos153
private theorem vp60 : productBlend (1/4) (1/3) (⟨(66/179),(-1/537),0,0⟩ : CertField) (⟨(247/649),(1/649),0,0⟩ : CertField) = vec60 := by
  rw [cp93, cp153]
  exact r_blend_scaled n93 n153 537 649 pos93 pos153
private def ivec61 : Fin 3 → IntField := fun j => blendN 400 sE sF n82 n121 177 2497 j
private def dvec61 : Fin 3 → ℤ := fun _ => 400*177*2497
private def vec61 : Fin 3 → CertField := fun j => scaled (ivec61 j) (dvec61 j)
private theorem dpos61 : ∀ j, (0:ℤ) < dvec61 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos82) pos121
private theorem vp61 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(731/2497),(-1/2497),0,0⟩ : CertField) = vec61 := by
  rw [cp82, cp121]
  exact s_blend_scaled n82 n121 177 2497 pos82 pos121
private def ivec62 : Fin 3 → IntField := fun j => blendN 144 rE rF n102 n153 7501 649 j
private def dvec62 : Fin 3 → ℤ := fun _ => 144*7501*649
private def vec62 : Fin 3 → CertField := fun j => scaled (ivec62 j) (dvec62 j)
private theorem dpos62 : ∀ j, (0:ℤ) < dvec62 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos102) pos153
private theorem vp62 : productBlend (1/4) (1/3) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) (⟨(247/649),(1/649),0,0⟩ : CertField) = vec62 := by
  rw [cp102, cp153]
  exact r_blend_scaled n102 n153 7501 649 pos102 pos153
private def ivec63 : Fin 3 → IntField := fun j => blendN 144 rE rF n159 n34 670 262 j
private def dvec63 : Fin 3 → ℤ := fun _ => 144*670*262
private def vec63 : Fin 3 → CertField := fun j => scaled (ivec63 j) (dvec63 j)
private theorem dpos63 : ∀ j, (0:ℤ) < dvec63 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos159) pos34
private theorem vp63 : productBlend (1/4) (1/3) (⟨(251/670),0,0,(1/670)⟩ : CertField) (⟨(105/262),0,0,(-1/262)⟩ : CertField) = vec63 := by
  rw [cp159, cp34]
  exact r_blend_scaled n159 n34 670 262 pos159 pos34
private def ivec64 : Fin 3 → IntField := fun j => blendN 400 sE sF n89 n121 2749 2497 j
private def dvec64 : Fin 3 → ℤ := fun _ => 400*2749*2497
private def vec64 : Fin 3 → CertField := fun j => scaled (ivec64 j) (dvec64 j)
private theorem dpos64 : ∀ j, (0:ℤ) < dvec64 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos89) pos121
private theorem vp64 : productBlend (3/4) (4/5) (⟨(767/2749),(1/2749),0,0⟩ : CertField) (⟨(731/2497),(-1/2497),0,0⟩ : CertField) = vec64 := by
  rw [cp89, cp121]
  exact s_blend_scaled n89 n121 2749 2497 pos89 pos121
private def ivec65 : Fin 3 → IntField := fun j => blendN 144 rE rF n19 n162 70 670 j
private def dvec65 : Fin 3 → ℤ := fun _ => 144*70*670
private def vec65 : Fin 3 → CertField := fun j => scaled (ivec65 j) (dvec65 j)
private theorem dpos65 : ∀ j, (0:ℤ) < dvec65 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos19) pos162
private theorem vp65 : productBlend (1/4) (1/3) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(251/670),0,0,(-1/670)⟩ : CertField) = vec65 := by
  rw [cp19, cp162]
  exact r_blend_scaled n19 n162 70 670 pos19 pos162
private def ivec66 : Fin 3 → IntField := fun j => blendN 144 rE rF n93 n164 537 9757 j
private def dvec66 : Fin 3 → ℤ := fun _ => 144*537*9757
private def vec66 : Fin 3 → CertField := fun j => scaled (ivec66 j) (dvec66 j)
private theorem dpos66 : ∀ j, (0:ℤ) < dvec66 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos93) pos164
private theorem vp66 : productBlend (1/4) (1/3) (⟨(66/179),(-1/537),0,0⟩ : CertField) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) = vec66 := by
  rw [cp93, cp164]
  exact r_blend_scaled n93 n164 537 9757 pos93 pos164
private def ivec67 : Fin 3 → IntField := fun j => blendN 144 rE rF n102 n164 7501 9757 j
private def dvec67 : Fin 3 → ℤ := fun _ => 144*7501*9757
private def vec67 : Fin 3 → CertField := fun j => scaled (ivec67 j) (dvec67 j)
private theorem dpos67 : ∀ j, (0:ℤ) < dvec67 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos102) pos164
private theorem vp67 : productBlend (1/4) (1/3) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) = vec67 := by
  rw [cp102, cp164]
  exact r_blend_scaled n102 n164 7501 9757 pos102 pos164
private def ivec68 : Fin 3 → IntField := fun j => blendN 144 rE rF n170 n38 19050 202 j
private def dvec68 : Fin 3 → ℤ := fun _ => 144*19050*202
private def vec68 : Fin 3 → CertField := fun j => scaled (ivec68 j) (dvec68 j)
private theorem dpos68 : ∀ j, (0:ℤ) < dvec68 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos170) pos38
private theorem vp68 : productBlend (1/4) (1/3) (⟨(2463/6350),0,0,(1/19050)⟩ : CertField) (⟨(83/202),0,0,(-1/202)⟩ : CertField) = vec68 := by
  rw [cp170, cp38]
  exact r_blend_scaled n170 n38 19050 202 pos170 pos38
private def ivec69 : Fin 3 → IntField := fun j => blendN 144 rE rF n131 n171 249 1429 j
private def dvec69 : Fin 3 → ℤ := fun _ => 144*249*1429
private def vec69 : Fin 3 → CertField := fun j => scaled (ivec69 j) (dvec69 j)
private theorem dpos69 : ∀ j, (0:ℤ) < dvec69 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos131) pos171
private theorem vp69 : productBlend (1/4) (1/3) (⟨(32/83),(-1/249),0,0⟩ : CertField) (⟨(553/1429),(1/1429),0,0⟩ : CertField) = vec69 := by
  rw [cp131, cp171]
  exact r_blend_scaled n131 n171 249 1429 pos131 pos171
private def ivec70 : Fin 3 → IntField := fun j => blendN 144 rE rF n139 n171 3718 1429 j
private def dvec70 : Fin 3 → ℤ := fun _ => 144*3718*1429
private def vec70 : Fin 3 → CertField := fun j => scaled (ivec70 j) (dvec70 j)
private theorem dpos70 : ∀ j, (0:ℤ) < dvec70 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos139) pos171
private theorem vp70 : productBlend (1/4) (1/3) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) (⟨(553/1429),(1/1429),0,0⟩ : CertField) = vec70 := by
  rw [cp139, cp171]
  exact r_blend_scaled n139 n171 3718 1429 pos139 pos171
private def ivec71 : Fin 3 → IntField := fun j => blendN 144 rE rF n176 n38 1770 202 j
private def dvec71 : Fin 3 → ℤ := fun _ => 144*1770*202
private def vec71 : Fin 3 → CertField := fun j => scaled (ivec71 j) (dvec71 j)
private theorem dpos71 : ∀ j, (0:ℤ) < dvec71 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos176) pos38
private theorem vp71 : productBlend (1/4) (1/3) (⟨(227/590),0,0,(1/1770)⟩ : CertField) (⟨(83/202),0,0,(-1/202)⟩ : CertField) = vec71 := by
  rw [cp176, cp38]
  exact r_blend_scaled n176 n38 1770 202 pos176 pos38
private def ivec72 : Fin 3 → IntField := fun j => blendN 144 rE rF n131 n183 249 20022 j
private def dvec72 : Fin 3 → ℤ := fun _ => 144*249*20022
private def vec72 : Fin 3 → CertField := fun j => scaled (ivec72 j) (dvec72 j)
private theorem dpos72 : ∀ j, (0:ℤ) < dvec72 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos131) pos183
private theorem vp72 : productBlend (1/4) (1/3) (⟨(32/83),(-1/249),0,0⟩ : CertField) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) = vec72 := by
  rw [cp131, cp183]
  exact r_blend_scaled n131 n183 249 20022 pos131 pos183
private def ivec73 : Fin 3 → IntField := fun j => blendN 144 rE rF n139 n183 3718 20022 j
private def dvec73 : Fin 3 → ℤ := fun _ => 144*3718*20022
private def vec73 : Fin 3 → CertField := fun j => scaled (ivec73 j) (dvec73 j)
private theorem dpos73 : ∀ j, (0:ℤ) < dvec73 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos139) pos183
private theorem vp73 : productBlend (1/4) (1/3) (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) = vec73 := by
  rw [cp139, cp183]
  exact r_blend_scaled n139 n183 3718 20022 pos139 pos183
private def ivec74 : Fin 3 → IntField := fun j => blendN 144 rE rF n153 n188 649 454 j
private def dvec74 : Fin 3 → ℤ := fun _ => 144*649*454
private def vec74 : Fin 3 → CertField := fun j => scaled (ivec74 j) (dvec74 j)
private theorem dpos74 : ∀ j, (0:ℤ) < dvec74 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos153) pos188
private theorem vp74 : productBlend (1/4) (1/3) (⟨(247/649),(1/649),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec74 := by
  rw [cp153, cp188]
  exact r_blend_scaled n153 n188 649 454 pos153 pos188
private def ivec75 : Fin 3 → IntField := fun j => blendN 144 rE rF n37 n191 574 7846 j
private def dvec75 : Fin 3 → ℤ := fun _ => 144*574*7846
private def vec75 : Fin 3 → CertField := fun j => scaled (ivec75 j) (dvec75 j)
private theorem dpos75 : ∀ j, (0:ℤ) < dvec75 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos37) pos191
private theorem vp75 : productBlend (1/4) (1/3) (⟨(31/82),0,0,(1/574)⟩ : CertField) (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) = vec75 := by
  rw [cp37, cp191]
  exact r_blend_scaled n37 n191 574 7846 pos37 pos191
private def ivec76 : Fin 3 → IntField := fun j => blendN 144 rE rF n153 n195 649 8353 j
private def dvec76 : Fin 3 → ℤ := fun _ => 144*649*8353
private def vec76 : Fin 3 → CertField := fun j => scaled (ivec76 j) (dvec76 j)
private theorem dpos76 : ∀ j, (0:ℤ) < dvec76 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos153) pos195
private theorem vp76 : productBlend (1/4) (1/3) (⟨(247/649),(1/649),0,0⟩ : CertField) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = vec76 := by
  rw [cp153, cp195]
  exact r_blend_scaled n153 n195 649 8353 pos153 pos195
private def ivec77 : Fin 3 → IntField := fun j => blendN 144 rE rF n164 n188 9757 454 j
private def dvec77 : Fin 3 → ℤ := fun _ => 144*9757*454
private def vec77 : Fin 3 → CertField := fun j => scaled (ivec77 j) (dvec77 j)
private theorem dpos77 : ∀ j, (0:ℤ) < dvec77 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos164) pos188
private theorem vp77 : productBlend (1/4) (1/3) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec77 := by
  rw [cp164, cp188]
  exact r_blend_scaled n164 n188 9757 454 pos164 pos188
private def ivec78 : Fin 3 → IntField := fun j => blendN 144 rE rF n164 n195 9757 8353 j
private def dvec78 : Fin 3 → ℤ := fun _ => 144*9757*8353
private def vec78 : Fin 3 → CertField := fun j => scaled (ivec78 j) (dvec78 j)
private theorem dpos78 : ∀ j, (0:ℤ) < dvec78 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos164) pos195
private theorem vp78 : productBlend (1/4) (1/3) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) = vec78 := by
  rw [cp164, cp195]
  exact r_blend_scaled n164 n195 9757 8353 pos164 pos195
private def ivec79 : Fin 3 → IntField := fun j => blendN 144 rE rF n153 n131 649 249 j
private def dvec79 : Fin 3 → ℤ := fun _ => 144*649*249
private def vec79 : Fin 3 → CertField := fun j => scaled (ivec79 j) (dvec79 j)
private theorem dpos79 : ∀ j, (0:ℤ) < dvec79 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos153) pos131
private theorem vp79 : productBlend (1/4) (1/3) (⟨(247/649),(1/649),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec79 := by
  rw [cp153, cp131]
  exact r_blend_scaled n153 n131 649 249 pos153 pos131
private def ivec80 : Fin 3 → IntField := fun j => blendN 400 sE sF n27 n207 402 4354 j
private def dvec80 : Fin 3 → ℤ := fun _ => 400*402*4354
private def vec80 : Fin 3 → CertField := fun j => scaled (ivec80 j) (dvec80 j)
private theorem dpos80 : ∀ j, (0:ℤ) < dvec80 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos27) pos207
private theorem vp80 : productBlend (3/4) (4/5) (⟨(39/134),0,0,(1/402)⟩ : CertField) (⟨(189/622),0,0,(-1/4354)⟩ : CertField) = vec80 := by
  rw [cp27, cp207]
  exact s_blend_scaled n27 n207 402 4354 pos27 pos207
private def ivec81 : Fin 3 → IntField := fun j => blendN 144 rE rF n164 n131 9757 249 j
private def dvec81 : Fin 3 → ℤ := fun _ => 144*9757*249
private def vec81 : Fin 3 → CertField := fun j => scaled (ivec81 j) (dvec81 j)
private theorem dpos81 : ∀ j, (0:ℤ) < dvec81 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos164) pos131
private theorem vp81 : productBlend (1/4) (1/3) (⟨(3734/9757),(1/9757),0,0⟩ : CertField) (⟨(32/83),(-1/249),0,0⟩ : CertField) = vec81 := by
  rw [cp164, cp131]
  exact r_blend_scaled n164 n131 9757 249 pos164 pos131
private def ivec82 : Fin 3 → IntField := fun j => blendN 400 sE sF n63 n218 429 4654 j
private def dvec82 : Fin 3 → ℤ := fun _ => 400*429*4654
private def vec82 : Fin 3 → CertField := fun j => scaled (ivec82 j) (dvec82 j)
private theorem dpos82 : ∀ j, (0:ℤ) < dvec82 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos63) pos218
private theorem vp82 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = vec82 := by
  rw [cp63, cp218]
  exact s_blend_scaled n63 n218 429 4654 pos63 pos218
private def ivec83 : Fin 3 → IntField := fun j => blendN 400 sE sF n106 n218 6094 4654 j
private def dvec83 : Fin 3 → ℤ := fun _ => 400*6094*4654
private def vec83 : Fin 3 → CertField := fun j => scaled (ivec83 j) (dvec83 j)
private theorem dpos83 : ∀ j, (0:ℤ) < dvec83 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos106) pos218
private theorem vp83 : productBlend (3/4) (4/5) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) (⟨(1413/4654),(-1/4654),0,0⟩ : CertField) = vec83 := by
  rw [cp106, cp218]
  exact s_blend_scaled n106 n218 6094 4654 pos106 pos218
private def ivec84 : Fin 3 → IntField := fun j => blendN 144 rE rF n47 n229 1354 13866 j
private def dvec84 : Fin 3 → ℤ := fun _ => 144*1354*13866
private def vec84 : Fin 3 → CertField := fun j => scaled (ivec84 j) (dvec84 j)
private theorem dpos84 : ∀ j, (0:ℤ) < dvec84 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos47) pos229
private theorem vp84 : productBlend (1/4) (1/3) (⟨(523/1354),0,0,(1/1354)⟩ : CertField) (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) = vec84 := by
  rw [cp47, cp229]
  exact r_blend_scaled n47 n229 1354 13866 pos47 pos229
private def ivec85 : Fin 3 → IntField := fun j => blendN 144 rE rF n171 n232 1429 709 j
private def dvec85 : Fin 3 → ℤ := fun _ => 144*1429*709
private def vec85 : Fin 3 → CertField := fun j => scaled (ivec85 j) (dvec85 j)
private theorem dpos85 : ∀ j, (0:ℤ) < dvec85 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos232
private theorem vp85 : productBlend (1/4) (1/3) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(278/709),(-1/709),0,0⟩ : CertField) = vec85 := by
  rw [cp171, cp232]
  exact r_blend_scaled n171 n232 1429 709 pos171 pos232
private def ivec86 : Fin 3 → IntField := fun j => blendN 400 sE sF n63 n83 429 142 j
private def dvec86 : Fin 3 → ℤ := fun _ => 400*429*142
private def vec86 : Fin 3 → CertField := fun j => scaled (ivec86 j) (dvec86 j)
private theorem dpos86 : ∀ j, (0:ℤ) < dvec86 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos63) pos83
private theorem vp86 : productBlend (3/4) (4/5) (⟨(42/143),(1/429),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec86 := by
  rw [cp63, cp83]
  exact s_blend_scaled n63 n83 429 142 pos63 pos83
private def ivec87 : Fin 3 → IntField := fun j => blendN 400 sE sF n106 n83 6094 142 j
private def dvec87 : Fin 3 → ℤ := fun _ => 400*6094*142
private def vec87 : Fin 3 → CertField := fun j => scaled (ivec87 j) (dvec87 j)
private theorem dpos87 : ∀ j, (0:ℤ) < dvec87 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos106) pos83
private theorem vp87 : productBlend (3/4) (4/5) (⟨(1809/6094),(1/6094),0,0⟩ : CertField) (⟨(43/142),(-1/142),0,0⟩ : CertField) = vec87 := by
  rw [cp106, cp83]
  exact s_blend_scaled n106 n83 6094 142 pos106 pos83
private def ivec88 : Fin 3 → IntField := fun j => blendN 144 rE rF n183 n232 20022 709 j
private def dvec88 : Fin 3 → ℤ := fun _ => 144*20022*709
private def vec88 : Fin 3 → CertField := fun j => scaled (ivec88 j) (dvec88 j)
private theorem dpos88 : ∀ j, (0:ℤ) < dvec88 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos183) pos232
private theorem vp88 : productBlend (1/4) (1/3) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) (⟨(278/709),(-1/709),0,0⟩ : CertField) = vec88 := by
  rw [cp183, cp232]
  exact r_blend_scaled n183 n232 20022 709 pos183 pos232
private def ivec89 : Fin 3 → IntField := fun j => blendN 144 rE rF n188 n238 454 33937 j
private def dvec89 : Fin 3 → ℤ := fun _ => 144*454*33937
private def vec89 : Fin 3 → CertField := fun j => scaled (ivec89 j) (dvec89 j)
private theorem dpos89 : ∀ j, (0:ℤ) < dvec89 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos188) pos238
private theorem vp89 : productBlend (1/4) (1/3) (⟨(177/454),(-1/454),0,0⟩ : CertField) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) = vec89 := by
  rw [cp188, cp238]
  exact r_blend_scaled n188 n238 454 33937 pos188 pos238
private def ivec90 : Fin 3 → IntField := fun j => blendN 144 rE rF n195 n238 8353 33937 j
private def dvec90 : Fin 3 → ℤ := fun _ => 144*8353*33937
private def vec90 : Fin 3 → CertField := fun j => scaled (ivec90 j) (dvec90 j)
private theorem dpos90 : ∀ j, (0:ℤ) < dvec90 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos195) pos238
private theorem vp90 : productBlend (1/4) (1/3) (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) = vec90 := by
  rw [cp195, cp238]
  exact r_blend_scaled n195 n238 8353 33937 pos195 pos238
private def ivec91 : Fin 3 → IntField := fun j => blendN 144 rE rF n171 n245 1429 14838 j
private def dvec91 : Fin 3 → ℤ := fun _ => 144*1429*14838
private def vec91 : Fin 3 → CertField := fun j => scaled (ivec91 j) (dvec91 j)
private theorem dpos91 : ∀ j, (0:ℤ) < dvec91 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos245
private theorem vp91 : productBlend (1/4) (1/3) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) = vec91 := by
  rw [cp171, cp245]
  exact r_blend_scaled n171 n245 1429 14838 pos171 pos245
private def ivec92 : Fin 3 → IntField := fun j => blendN 144 rE rF n19 n19 70 70 j
private def dvec92 : Fin 3 → ℤ := fun _ => 144*70*70
private def vec92 : Fin 3 → CertField := fun j => scaled (ivec92 j) (dvec92 j)
private theorem dpos92 : ∀ j, (0:ℤ) < dvec92 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos19) pos19
private theorem vp92 : productBlend (1/4) (1/3) (⟨(3/10),0,0,(1/70)⟩ : CertField) (⟨(3/10),0,0,(1/70)⟩ : CertField) = vec92 := by
  rw [cp19]
  exact r_blend_scaled n19 n19 70 70 pos19 pos19
private def ivec93 : Fin 3 → IntField := fun j => blendN 400 sE sF n10 n10 430 430 j
private def dvec93 : Fin 3 → ℤ := fun _ => 400*430*430
private def vec93 : Fin 3 → CertField := fun j => scaled (ivec93 j) (dvec93 j)
private theorem dpos93 : ∀ j, (0:ℤ) < dvec93 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos10) pos10
private theorem vp93 : productBlend (3/4) (4/5) (⟨(121/430),0,0,(-1/430)⟩ : CertField) (⟨(121/430),0,0,(-1/430)⟩ : CertField) = vec93 := by
  rw [cp10]
  exact s_blend_scaled n10 n10 430 430 pos10 pos10
private def ivec94 : Fin 3 → IntField := fun j => blendN 400 sE sF n54 n82 1006 177 j
private def dvec94 : Fin 3 → ℤ := fun _ => 400*1006*177
private def vec94 : Fin 3 → CertField := fun j => scaled (ivec94 j) (dvec94 j)
private theorem dpos94 : ∀ j, (0:ℤ) < dvec94 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos54) pos82
private theorem vp94 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(16/59),(1/177),0,0⟩ : CertField) = vec94 := by
  rw [cp54, cp82]
  exact s_blend_scaled n54 n82 1006 177 pos54 pos82
private def ivec95 : Fin 3 → IntField := fun j => blendN 400 sE sF n9 n253 118 13326 j
private def dvec95 : Fin 3 → ℤ := fun _ => 400*118*13326
private def vec95 : Fin 3 → CertField := fun j => scaled (ivec95 j) (dvec95 j)
private theorem dpos95 : ∀ j, (0:ℤ) < dvec95 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos9) pos253
private theorem vp95 : productBlend (3/4) (4/5) (⟨(27/118),0,0,(1/118)⟩ : CertField) (⟨(1191/4442),0,0,(-1/13326)⟩ : CertField) = vec95 := by
  rw [cp9, cp253]
  exact s_blend_scaled n9 n253 118 13326 pos9 pos253
private def ivec96 : Fin 3 → IntField := fun j => blendN 400 sE sF n254 n82 14001 177 j
private def dvec96 : Fin 3 → ℤ := fun _ => 400*14001*177
private def vec96 : Fin 3 → CertField := fun j => scaled (ivec96 j) (dvec96 j)
private theorem dpos96 : ∀ j, (0:ℤ) < dvec96 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos254) pos82
private theorem vp96 : productBlend (3/4) (4/5) (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) (⟨(16/59),(1/177),0,0⟩ : CertField) = vec96 := by
  rw [cp254, cp82]
  exact s_blend_scaled n254 n82 14001 177 pos254 pos82
private def ivec97 : Fin 3 → IntField := fun j => blendN 400 sE sF n9 n258 118 1266 j
private def dvec97 : Fin 3 → ℤ := fun _ => 400*118*1266
private def vec97 : Fin 3 → CertField := fun j => scaled (ivec97 j) (dvec97 j)
private theorem dpos97 : ∀ j, (0:ℤ) < dvec97 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos9) pos258
private theorem vp97 : productBlend (3/4) (4/5) (⟨(27/118),0,0,(1/118)⟩ : CertField) (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = vec97 := by
  rw [cp9, cp258]
  exact s_blend_scaled n9 n258 118 1266 pos9 pos258
private def ivec98 : Fin 3 → IntField := fun j => blendN 400 sE sF n54 n89 1006 2749 j
private def dvec98 : Fin 3 → ℤ := fun _ => 400*1006*2749
private def vec98 : Fin 3 → CertField := fun j => scaled (ivec98 j) (dvec98 j)
private theorem dpos98 : ∀ j, (0:ℤ) < dvec98 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos54) pos89
private theorem vp98 : productBlend (3/4) (4/5) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) (⟨(767/2749),(1/2749),0,0⟩ : CertField) = vec98 := by
  rw [cp54, cp89]
  exact s_blend_scaled n54 n89 1006 2749 pos54 pos89
private def ivec99 : Fin 3 → IntField := fun j => blendN 400 sE sF n254 n89 14001 2749 j
private def dvec99 : Fin 3 → ℤ := fun _ => 400*14001*2749
private def vec99 : Fin 3 → CertField := fun j => scaled (ivec99 j) (dvec99 j)
private theorem dpos99 : ∀ j, (0:ℤ) < dvec99 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos254) pos89
private theorem vp99 : productBlend (3/4) (4/5) (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) (⟨(767/2749),(1/2749),0,0⟩ : CertField) = vec99 := by
  rw [cp254, cp89]
  exact s_blend_scaled n254 n89 14001 2749 pos254 pos89
private def ivec100 : Fin 3 → IntField := fun j => blendN 144 rE rF n269 n162 19270 670 j
private def dvec100 : Fin 3 → ℤ := fun _ => 144*19270*670
private def vec100 : Fin 3 → CertField := fun j => scaled (ivec100 j) (dvec100 j)
private theorem dpos100 : ∀ j, (0:ℤ) < dvec100 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos269) pos162
private theorem vp100 : productBlend (1/4) (1/3) (⟨(7081/19270),0,0,(1/19270)⟩ : CertField) (⟨(251/670),0,0,(-1/670)⟩ : CertField) = vec100 := by
  rw [cp269, cp162]
  exact r_blend_scaled n269 n162 19270 670 pos269 pos162
private def ivec101 : Fin 3 → IntField := fun j => blendN 144 rE rF n53 n270 12598 1318 j
private def dvec101 : Fin 3 → ℤ := fun _ => 144*12598*1318
private def vec101 : Fin 3 → CertField := fun j => scaled (ivec101 j) (dvec101 j)
private theorem dpos101 : ∀ j, (0:ℤ) < dvec101 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos53) pos270
private theorem vp101 : productBlend (1/4) (1/3) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(483/1318),(1/1318),0,0⟩ : CertField) = vec101 := by
  rw [cp53, cp270]
  exact r_blend_scaled n53 n270 12598 1318 pos53 pos270
private def ivec102 : Fin 3 → IntField := fun j => blendN 144 rE rF n273 n162 1258 670 j
private def dvec102 : Fin 3 → ℤ := fun _ => 144*1258*670
private def vec102 : Fin 3 → CertField := fun j => scaled (ivec102 j) (dvec102 j)
private theorem dpos102 : ∀ j, (0:ℤ) < dvec102 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos273) pos162
private theorem vp102 : productBlend (1/4) (1/3) (⟨(457/1258),0,0,(1/1258)⟩ : CertField) (⟨(251/670),0,0,(-1/670)⟩ : CertField) = vec102 := by
  rw [cp273, cp162]
  exact r_blend_scaled n273 n162 1258 670 pos273 pos162
private def ivec103 : Fin 3 → IntField := fun j => blendN 400 sE sF n70 n77 5893 478 j
private def dvec103 : Fin 3 → ℤ := fun _ => 400*5893*478
private def vec103 : Fin 3 → CertField := fun j => scaled (ivec103 j) (dvec103 j)
private theorem dpos103 : ∀ j, (0:ℤ) < dvec103 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos70) pos77
private theorem vp103 : productBlend (3/4) (4/5) (⟨(1590/5893),(1/5893),0,0⟩ : CertField) (⟨(133/478),(-1/478),0,0⟩ : CertField) = vec103 := by
  rw [cp70, cp77]
  exact s_blend_scaled n70 n77 5893 478 pos70 pos77
private def ivec104 : Fin 3 → IntField := fun j => blendN 144 rE rF n53 n276 12598 20353 j
private def dvec104 : Fin 3 → ℤ := fun _ => 144*12598*20353
private def vec104 : Fin 3 → CertField := fun j => scaled (ivec104 j) (dvec104 j)
private theorem dpos104 : ∀ j, (0:ℤ) < dvec104 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos53) pos276
private theorem vp104 : productBlend (1/4) (1/3) (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) (⟨(7480/20353),(1/20353),0,0⟩ : CertField) = vec104 := by
  rw [cp53, cp276]
  exact r_blend_scaled n53 n276 12598 20353 pos53 pos276
private def ivec105 : Fin 3 → IntField := fun j => blendN 144 rE rF n270 n93 1318 537 j
private def dvec105 : Fin 3 → ℤ := fun _ => 144*1318*537
private def vec105 : Fin 3 → CertField := fun j => scaled (ivec105 j) (dvec105 j)
private theorem dpos105 : ∀ j, (0:ℤ) < dvec105 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos270) pos93
private theorem vp105 : productBlend (1/4) (1/3) (⟨(483/1318),(1/1318),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec105 := by
  rw [cp270, cp93]
  exact r_blend_scaled n270 n93 1318 537 pos270 pos93
private def ivec106 : Fin 3 → IntField := fun j => blendN 144 rE rF n276 n93 20353 537 j
private def dvec106 : Fin 3 → ℤ := fun _ => 144*20353*537
private def vec106 : Fin 3 → CertField := fun j => scaled (ivec106 j) (dvec106 j)
private theorem dpos106 : ∀ j, (0:ℤ) < dvec106 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos276) pos93
private theorem vp106 : productBlend (1/4) (1/3) (⟨(7480/20353),(1/20353),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec106 := by
  rw [cp276, cp93]
  exact r_blend_scaled n276 n93 20353 537 pos276 pos93
private def ivec107 : Fin 3 → IntField := fun j => blendN 144 rE rF n84 n93 169 537 j
private def dvec107 : Fin 3 → ℤ := fun _ => 144*169*537
private def vec107 : Fin 3 → CertField := fun j => scaled (ivec107 j) (dvec107 j)
private theorem dpos107 : ∀ j, (0:ℤ) < dvec107 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos93
private theorem vp107 : productBlend (1/4) (1/3) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(66/179),(-1/537),0,0⟩ : CertField) = vec107 := by
  rw [cp84, cp93]
  exact r_blend_scaled n84 n93 169 537 pos84 pos93
private def ivec108 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n98 313 7081 j
private def dvec108 : Fin 3 → ℤ := fun _ => 400*313*7081
private def vec108 : Fin 3 → CertField := fun j => scaled (ivec108 j) (dvec108 j)
private theorem dpos108 : ∀ j, (0:ℤ) < dvec108 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos98
private theorem vp108 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) = vec108 := by
  rw [cp66, cp98]
  exact s_blend_scaled n66 n98 313 7081 pos66 pos98
private def ivec109 : Fin 3 → IntField := fun j => blendN 144 rE rF n84 n102 169 7501 j
private def dvec109 : Fin 3 → ℤ := fun _ => 144*169*7501
private def vec109 : Fin 3 → CertField := fun j => scaled (ivec109 j) (dvec109 j)
private theorem dpos109 : ∀ j, (0:ℤ) < dvec109 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos84) pos102
private theorem vp109 : productBlend (1/4) (1/3) (⟨(61/169),(1/169),0,0⟩ : CertField) (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) = vec109 := by
  rw [cp84, cp102]
  exact r_blend_scaled n84 n102 169 7501 pos84 pos102
private def ivec110 : Fin 3 → IntField := fun j => blendN 400 sE sF n82 n77 177 478 j
private def dvec110 : Fin 3 → ℤ := fun _ => 400*177*478
private def vec110 : Fin 3 → CertField := fun j => scaled (ivec110 j) (dvec110 j)
private theorem dpos110 : ∀ j, (0:ℤ) < dvec110 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos82) pos77
private theorem vp110 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(133/478),(-1/478),0,0⟩ : CertField) = vec110 := by
  rw [cp82, cp77]
  exact s_blend_scaled n82 n77 177 478 pos82 pos77
private def ivec111 : Fin 3 → IntField := fun j => blendN 400 sE sF n82 n98 177 7081 j
private def dvec111 : Fin 3 → ℤ := fun _ => 400*177*7081
private def vec111 : Fin 3 → CertField := fun j => scaled (ivec111 j) (dvec111 j)
private theorem dpos111 : ∀ j, (0:ℤ) < dvec111 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos82) pos98
private theorem vp111 : productBlend (3/4) (4/5) (⟨(16/59),(1/177),0,0⟩ : CertField) (⟨(1950/7081),(-1/7081),0,0⟩ : CertField) = vec111 := by
  rw [cp82, cp98]
  exact s_blend_scaled n82 n98 177 7081 pos82 pos98
private def ivec112 : Fin 3 → IntField := fun j => blendN 400 sE sF n122 n67 10753 37 j
private def dvec112 : Fin 3 → ℤ := fun _ => 400*10753*37
private def vec112 : Fin 3 → CertField := fun j => scaled (ivec112 j) (dvec112 j)
private theorem dpos112 : ∀ j, (0:ℤ) < dvec112 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos122) pos67
private theorem vp112 : productBlend (3/4) (4/5) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec112 := by
  rw [cp122, cp67]
  exact s_blend_scaled n122 n67 10753 37 pos122 pos67
private def ivec113 : Fin 3 → IntField := fun j => blendN 144 rE rF n238 n67 33937 37 j
private def dvec113 : Fin 3 → ℤ := fun _ => 144*33937*37
private def vec113 : Fin 3 → CertField := fun j => scaled (ivec113 j) (dvec113 j)
private theorem dpos113 : ∀ j, (0:ℤ) < dvec113 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos238) pos67
private theorem vp113 : productBlend (1/4) (1/3) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec113 := by
  rw [cp238, cp67]
  exact r_blend_scaled n238 n67 33937 37 pos238 pos67
private def ivec114 : Fin 3 → IntField := fun j => blendN 400 sE sF n3 n4 10 510 j
private def dvec114 : Fin 3 → ℤ := fun _ => 400*10*510
private def vec114 : Fin 3 → CertField := fun j => scaled (ivec114 j) (dvec114 j)
private theorem dpos114 : ∀ j, (0:ℤ) < dvec114 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos4
private theorem vp114 : productBlend (3/4) (4/5) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(63/170),0,0,(-1/510)⟩ : CertField) = vec114 := by
  rw [cp3, cp4]
  exact s_blend_scaled n3 n4 10 510 pos3 pos4
private def ivec115 : Fin 3 → IntField := fun j => blendN 144 rE rF n3 n58 10 10 j
private def dvec115 : Fin 3 → ℤ := fun _ => 144*10*10
private def vec115 : Fin 3 → CertField := fun j => scaled (ivec115 j) (dvec115 j)
private theorem dpos115 : ∀ j, (0:ℤ) < dvec115 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos58
private theorem vp115 : productBlend (1/4) (1/3) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(9/10),0,0,(-1/10)⟩ : CertField) = vec115 := by
  rw [cp3, cp58]
  exact r_blend_scaled n3 n58 10 10 pos3 pos58
private def ivec116 : Fin 3 → IntField := fun j => blendN 144 rE rF n171 n67 1429 37 j
private def dvec116 : Fin 3 → ℤ := fun _ => 144*1429*37
private def vec116 : Fin 3 → CertField := fun j => scaled (ivec116 j) (dvec116 j)
private theorem dpos116 : ∀ j, (0:ℤ) < dvec116 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos67
private theorem vp116 : productBlend (1/4) (1/3) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(15/37),(-1/37),0,0⟩ : CertField) = vec116 := by
  rw [cp171, cp67]
  exact r_blend_scaled n171 n67 1429 37 pos171 pos67
private def ivec117 : Fin 3 → IntField := fun j => blendN 400 sE sF n122 n116 10753 229 j
private def dvec117 : Fin 3 → ℤ := fun _ => 400*10753*229
private def vec117 : Fin 3 → CertField := fun j => scaled (ivec117 j) (dvec117 j)
private theorem dpos117 : ∀ j, (0:ℤ) < dvec117 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos122) pos116
private theorem vp117 : productBlend (3/4) (4/5) (⟨(3289/10753),(1/10753),0,0⟩ : CertField) (⟨(71/229),(-1/229),0,0⟩ : CertField) = vec117 := by
  rw [cp122, cp116]
  exact s_blend_scaled n122 n116 10753 229 pos122 pos116
private def ivec118 : Fin 3 → IntField := fun j => blendN 144 rE rF n308 n309 32926 1258 j
private def dvec118 : Fin 3 → ℤ := fun _ => 144*32926*1258
private def vec118 : Fin 3 → CertField := fun j => scaled (ivec118 j) (dvec118 j)
private theorem dpos118 : ∀ j, (0:ℤ) < dvec118 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos308) pos309
private theorem vp118 : productBlend (1/4) (1/3) (⟨(11835/32926),0,0,(1/32926)⟩ : CertField) (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = vec118 := by
  rw [cp308, cp309]
  exact r_blend_scaled n308 n309 32926 1258 pos308 pos309
private def ivec119 : Fin 3 → IntField := fun j => blendN 144 rE rF n311 n312 1858 30226 j
private def dvec119 : Fin 3 → ℤ := fun _ => 144*1858*30226
private def vec119 : Fin 3 → CertField := fun j => scaled (ivec119 j) (dvec119 j)
private theorem dpos119 : ∀ j, (0:ℤ) < dvec119 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos311) pos312
private theorem vp119 : productBlend (1/4) (1/3) (⟨(665/1858),0,0,(1/1858)⟩ : CertField) (⟨(1557/4318),0,0,(-1/30226)⟩ : CertField) = vec119 := by
  rw [cp311, cp312]
  exact r_blend_scaled n311 n312 1858 30226 pos311 pos312
private def ivec120 : Fin 3 → IntField := fun j => blendN 144 rE rF n311 n314 1858 1126 j
private def dvec120 : Fin 3 → ℤ := fun _ => 144*1858*1126
private def vec120 : Fin 3 → CertField := fun j => scaled (ivec120 j) (dvec120 j)
private theorem dpos120 : ∀ j, (0:ℤ) < dvec120 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos311) pos314
private theorem vp120 : productBlend (1/4) (1/3) (⟨(665/1858),0,0,(1/1858)⟩ : CertField) (⟨(411/1126),0,0,(-1/1126)⟩ : CertField) = vec120 := by
  rw [cp311, cp314]
  exact r_blend_scaled n311 n314 1858 1126 pos311 pos314
private def ivec121 : Fin 3 → IntField := fun j => blendN 144 rE rF n316 n309 2026 1258 j
private def dvec121 : Fin 3 → ℤ := fun _ => 144*2026*1258
private def vec121 : Fin 3 → CertField := fun j => scaled (ivec121 j) (dvec121 j)
private theorem dpos121 : ∀ j, (0:ℤ) < dvec121 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos316) pos309
private theorem vp121 : productBlend (1/4) (1/3) (⟨(723/2026),0,0,(1/2026)⟩ : CertField) (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = vec121 := by
  rw [cp316, cp309]
  exact r_blend_scaled n316 n309 2026 1258 pos316 pos309
private def ivec122 : Fin 3 → IntField := fun j => blendN 144 rE rF n319 n320 2221 1846 j
private def dvec122 : Fin 3 → ℤ := fun _ => 144*2221*1846
private def vec122 : Fin 3 → CertField := fun j => scaled (ivec122 j) (dvec122 j)
private theorem dpos122 : ∀ j, (0:ℤ) < dvec122 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos319) pos320
private theorem vp122 : productBlend (1/4) (1/3) (⟨(797/2221),(1/2221),0,0⟩ : CertField) (⟨(667/1846),(-1/1846),0,0⟩ : CertField) = vec122 := by
  rw [cp319, cp320]
  exact r_blend_scaled n319 n320 2221 1846 pos319 pos320
private def ivec123 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n54 313 1006 j
private def dvec123 : Fin 3 → ℤ := fun _ => 400*313*1006
private def vec123 : Fin 3 → CertField := fun j => scaled (ivec123 j) (dvec123 j)
private theorem dpos123 : ∀ j, (0:ℤ) < dvec123 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos54
private theorem vp123 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(271/1006),(-1/1006),0,0⟩ : CertField) = vec123 := by
  rw [cp66, cp54]
  exact s_blend_scaled n66 n54 313 1006 pos66 pos54
private def ivec124 : Fin 3 → IntField := fun j => blendN 400 sE sF n66 n254 313 14001 j
private def dvec124 : Fin 3 → ℤ := fun _ => 400*313*14001
private def vec124 : Fin 3 → CertField := fun j => scaled (ivec124 j) (dvec124 j)
private theorem dpos124 : ∀ j, (0:ℤ) < dvec124 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos66) pos254
private theorem vp124 : productBlend (3/4) (4/5) (⟨(83/313),(1/313),0,0⟩ : CertField) (⟨(1251/4667),(-1/14001),0,0⟩ : CertField) = vec124 := by
  rw [cp66, cp254]
  exact s_blend_scaled n66 n254 313 14001 pos66 pos254
private def ivec125 : Fin 3 → IntField := fun j => blendN 144 rE rF n319 n323 2221 32101 j
private def dvec125 : Fin 3 → ℤ := fun _ => 144*2221*32101
private def vec125 : Fin 3 → CertField := fun j => scaled (ivec125 j) (dvec125 j)
private theorem dpos125 : ∀ j, (0:ℤ) < dvec125 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos319) pos323
private theorem vp125 : productBlend (1/4) (1/3) (⟨(797/2221),(1/2221),0,0⟩ : CertField) (⟨(11574/32101),(-1/32101),0,0⟩ : CertField) = vec125 := by
  rw [cp319, cp323]
  exact r_blend_scaled n319 n323 2221 32101 pos319 pos323
private def ivec126 : Fin 3 → IntField := fun j => blendN 144 rE rF n3 n309 10 1258 j
private def dvec126 : Fin 3 → ℤ := fun _ => 144*10*1258
private def vec126 : Fin 3 → CertField := fun j => scaled (ivec126 j) (dvec126 j)
private theorem dpos126 : ∀ j, (0:ℤ) < dvec126 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos3) pos309
private theorem vp126 : productBlend (1/4) (1/3) (⟨(-1/10),0,0,(1/10)⟩ : CertField) (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) = vec126 := by
  rw [cp3, cp309]
  exact r_blend_scaled n3 n309 10 1258 pos3 pos309
private def ivec127 : Fin 3 → IntField := fun j => blendN 400 sE sF n327 n328 2461 1941 j
private def dvec127 : Fin 3 → ℤ := fun _ => 400*2461*1941
private def vec127 : Fin 3 → CertField := fun j => scaled (ivec127 j) (dvec127 j)
private theorem dpos127 : ∀ j, (0:ℤ) < dvec127 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos327) pos328
private theorem vp127 : productBlend (3/4) (4/5) (⟨(660/2461),(1/2461),0,0⟩ : CertField) (⟨(175/647),(-1/1941),0,0⟩ : CertField) = vec127 := by
  rw [cp327, cp328]
  exact s_blend_scaled n327 n328 2461 1941 pos327 pos328
private def ivec128 : Fin 3 → IntField := fun j => blendN 400 sE sF n330 n331 2098 1090 j
private def dvec128 : Fin 3 → ℤ := fun _ => 400*2098*1090
private def vec128 : Fin 3 → CertField := fun j => scaled (ivec128 j) (dvec128 j)
private theorem dpos128 : ∀ j, (0:ℤ) < dvec128 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos330) pos331
private theorem vp128 : productBlend (3/4) (4/5) (⟨(561/2098),0,0,(1/2098)⟩ : CertField) (⟨(299/1090),0,0,(-1/1090)⟩ : CertField) = vec128 := by
  rw [cp330, cp331]
  exact s_blend_scaled n330 n331 2098 1090 pos330 pos331
private def ivec129 : Fin 3 → IntField := fun j => blendN 400 sE sF n333 n258 36034 1266 j
private def dvec129 : Fin 3 → ℤ := fun _ => 400*36034*1266
private def vec129 : Fin 3 → CertField := fun j => scaled (ivec129 j) (dvec129 j)
private theorem dpos129 : ∀ j, (0:ℤ) < dvec129 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos333) pos258
private theorem vp129 : productBlend (3/4) (4/5) (⟨(9683/36034),0,0,(1/36034)⟩ : CertField) (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = vec129 := by
  rw [cp333, cp258]
  exact s_blend_scaled n333 n258 36034 1266 pos333 pos258
private def ivec130 : Fin 3 → IntField := fun j => blendN 400 sE sF n336 n258 2338 1266 j
private def dvec130 : Fin 3 → ℤ := fun _ => 400*2338*1266
private def vec130 : Fin 3 → CertField := fun j => scaled (ivec130 j) (dvec130 j)
private theorem dpos130 : ∀ j, (0:ℤ) < dvec130 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos336) pos258
private theorem vp130 : productBlend (3/4) (4/5) (⟨(89/334),0,0,(1/2338)⟩ : CertField) (⟨(115/422),0,0,(-1/1266)⟩ : CertField) = vec130 := by
  rw [cp336, cp258]
  exact s_blend_scaled n336 n258 2338 1266 pos336 pos258
private def ivec131 : Fin 3 → IntField := fun j => blendN 400 sE sF n345 n346 1237 877 j
private def dvec131 : Fin 3 → ℤ := fun _ => 400*1237*877
private def vec131 : Fin 3 → CertField := fun j => scaled (ivec131 j) (dvec131 j)
private theorem dpos131 : ∀ j, (0:ℤ) < dvec131 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos345) pos346
private theorem vp131 : productBlend (3/4) (4/5) (⟨(341/1237),(1/1237),0,0⟩ : CertField) (⟨(246/877),(-1/877),0,0⟩ : CertField) = vec131 := by
  rw [cp345, cp346]
  exact s_blend_scaled n345 n346 1237 877 pos345 pos346
private def ivec132 : Fin 3 → IntField := fun j => blendN 400 sE sF n348 n349 1090 402 j
private def dvec132 : Fin 3 → ℤ := fun _ => 400*1090*402
private def vec132 : Fin 3 → CertField := fun j => scaled (ivec132 j) (dvec132 j)
private theorem dpos132 : ∀ j, (0:ℤ) < dvec132 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos348) pos349
private theorem vp132 : productBlend (3/4) (4/5) (⟨(299/1090),0,0,(1/1090)⟩ : CertField) (⟨(39/134),0,0,(-1/402)⟩ : CertField) = vec132 := by
  rw [cp348, cp349]
  exact s_blend_scaled n348 n349 1090 402 pos348 pos349
private def ivec133 : Fin 3 → IntField := fun j => blendN 400 sE sF n351 n140 17682 514 j
private def dvec133 : Fin 3 → ℤ := fun _ => 400*17682*514
private def vec133 : Fin 3 → CertField := fun j => scaled (ivec133 j) (dvec133 j)
private theorem dpos133 : ∀ j, (0:ℤ) < dvec133 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos351) pos140
private theorem vp133 : productBlend (3/4) (4/5) (⟨(233/842),0,0,(1/17682)⟩ : CertField) (⟨(147/514),0,0,(-1/514)⟩ : CertField) = vec133 := by
  rw [cp351, cp140]
  exact s_blend_scaled n351 n140 17682 514 pos351 pos140
private def ivec134 : Fin 3 → IntField := fun j => blendN 400 sE sF n354 n140 1266 514 j
private def dvec134 : Fin 3 → ℤ := fun _ => 400*1266*514
private def vec134 : Fin 3 → CertField := fun j => scaled (ivec134 j) (dvec134 j)
private theorem dpos134 : ∀ j, (0:ℤ) < dvec134 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos354) pos140
private theorem vp134 : productBlend (3/4) (4/5) (⟨(115/422),0,0,(1/1266)⟩ : CertField) (⟨(147/514),0,0,(-1/514)⟩ : CertField) = vec134 := by
  rw [cp354, cp140]
  exact s_blend_scaled n354 n140 1266 514 pos354 pos140
private def ivec135 : Fin 3 → IntField := fun j => blendN 144 rE rF n357 n358 1126 17218 j
private def dvec135 : Fin 3 → ℤ := fun _ => 144*1126*17218
private def vec135 : Fin 3 → CertField := fun j => scaled (ivec135 j) (dvec135 j)
private theorem dpos135 : ∀ j, (0:ℤ) < dvec135 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos357) pos358
private theorem vp135 : productBlend (1/4) (1/3) (⟨(411/1126),0,0,(1/1126)⟩ : CertField) (⟨(6361/17218),0,0,(-1/17218)⟩ : CertField) = vec135 := by
  rw [cp357, cp358]
  exact r_blend_scaled n357 n358 1126 17218 pos357 pos358
private def ivec136 : Fin 3 → IntField := fun j => blendN 144 rE rF n357 n361 1126 574 j
private def dvec136 : Fin 3 → ℤ := fun _ => 144*1126*574
private def vec136 : Fin 3 → CertField := fun j => scaled (ivec136 j) (dvec136 j)
private theorem dpos136 : ∀ j, (0:ℤ) < dvec136 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos357) pos361
private theorem vp136 : productBlend (1/4) (1/3) (⟨(411/1126),0,0,(1/1126)⟩ : CertField) (⟨(31/82),0,0,(-1/574)⟩ : CertField) = vec136 := by
  rw [cp357, cp361]
  exact r_blend_scaled n357 n361 1126 574 pos357 pos361
private def ivec137 : Fin 3 → IntField := fun j => blendN 144 rE rF n270 n363 1318 1033 j
private def dvec137 : Fin 3 → ℤ := fun _ => 144*1318*1033
private def vec137 : Fin 3 → CertField := fun j => scaled (ivec137 j) (dvec137 j)
private theorem dpos137 : ∀ j, (0:ℤ) < dvec137 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos270) pos363
private theorem vp137 : productBlend (1/4) (1/3) (⟨(483/1318),(1/1318),0,0⟩ : CertField) (⟨(383/1033),(-1/1033),0,0⟩ : CertField) = vec137 := by
  rw [cp270, cp363]
  exact r_blend_scaled n270 n363 1318 1033 pos270 pos363
private def ivec138 : Fin 3 → IntField := fun j => blendN 144 rE rF n270 n366 1318 18301 j
private def dvec138 : Fin 3 → ℤ := fun _ => 144*1318*18301
private def vec138 : Fin 3 → CertField := fun j => scaled (ivec138 j) (dvec138 j)
private theorem dpos138 : ∀ j, (0:ℤ) < dvec138 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos270) pos366
private theorem vp138 : productBlend (1/4) (1/3) (⟨(483/1318),(1/1318),0,0⟩ : CertField) (⟨(6760/18301),(-1/18301),0,0⟩ : CertField) = vec138 := by
  rw [cp270, cp366]
  exact r_blend_scaled n270 n366 1318 18301 pos270 pos366
private def ivec139 : Fin 3 → IntField := fun j => blendN 400 sE sF n345 n370 1237 16062 j
private def dvec139 : Fin 3 → ℤ := fun _ => 400*1237*16062
private def vec139 : Fin 3 → CertField := fun j => scaled (ivec139 j) (dvec139 j)
private theorem dpos139 : ∀ j, (0:ℤ) < dvec139 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos345) pos370
private theorem vp139 : productBlend (3/4) (4/5) (⟨(341/1237),(1/1237),0,0⟩ : CertField) (⟨(1493/5354),(-1/16062),0,0⟩ : CertField) = vec139 := by
  rw [cp345, cp370]
  exact s_blend_scaled n345 n370 1237 16062 pos345 pos370
private def ivec140 : Fin 3 → IntField := fun j => blendN 144 rE rF n382 n320 34801 1846 j
private def dvec140 : Fin 3 → ℤ := fun _ => 144*34801*1846
private def vec140 : Fin 3 → CertField := fun j => scaled (ivec140 j) (dvec140 j)
private theorem dpos140 : ∀ j, (0:ℤ) < dvec140 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos382) pos320
private theorem vp140 : productBlend (1/4) (1/3) (⟨(12510/34801),(1/34801),0,0⟩ : CertField) (⟨(667/1846),(-1/1846),0,0⟩ : CertField) = vec140 := by
  rw [cp382, cp320]
  exact r_blend_scaled n382 n320 34801 1846 pos382 pos320
private def ivec141 : Fin 3 → IntField := fun j => blendN 400 sE sF n384 n385 814 1069 j
private def dvec141 : Fin 3 → ℤ := fun _ => 400*814*1069
private def vec141 : Fin 3 → CertField := fun j => scaled (ivec141 j) (dvec141 j)
private theorem dpos141 : ∀ j, (0:ℤ) < dvec141 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos384) pos385
private theorem vp141 : productBlend (3/4) (4/5) (⟨(237/814),(1/814),0,0⟩ : CertField) (⟨(317/1069),(-1/1069),0,0⟩ : CertField) = vec141 := by
  rw [cp384, cp385]
  exact s_blend_scaled n384 n385 814 1069 pos384 pos385
private def ivec142 : Fin 3 → IntField := fun j => blendN 400 sE sF n387 n388 13690 922 j
private def dvec142 : Fin 3 → ℤ := fun _ => 400*13690*922
private def vec142 : Fin 3 → CertField := fun j => scaled (ivec142 j) (dvec142 j)
private theorem dpos142 : ∀ j, (0:ℤ) < dvec142 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos387) pos388
private theorem vp142 : productBlend (3/4) (4/5) (⟨(4009/13690),0,0,(1/13690)⟩ : CertField) (⟨(275/922),0,0,(-1/922)⟩ : CertField) = vec142 := by
  rw [cp387, cp388]
  exact s_blend_scaled n387 n388 13690 922 pos387 pos388
private def ivec143 : Fin 3 → IntField := fun j => blendN 400 sE sF n391 n388 430 922 j
private def dvec143 : Fin 3 → ℤ := fun _ => 400*430*922
private def vec143 : Fin 3 → CertField := fun j => scaled (ivec143 j) (dvec143 j)
private theorem dpos143 : ∀ j, (0:ℤ) < dvec143 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos391) pos388
private theorem vp143 : productBlend (3/4) (4/5) (⟨(121/430),0,0,(1/430)⟩ : CertField) (⟨(275/922),0,0,(-1/922)⟩ : CertField) = vec143 := by
  rw [cp391, cp388]
  exact s_blend_scaled n391 n388 430 922 pos391 pos388
private def ivec144 : Fin 3 → IntField := fun j => blendN 400 sE sF n397 n398 1549 1894 j
private def dvec144 : Fin 3 → ℤ := fun _ => 400*1549*1894
private def vec144 : Fin 3 → CertField := fun j => scaled (ivec144 j) (dvec144 j)
private theorem dpos144 : ∀ j, (0:ℤ) < dvec144 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos397) pos398
private theorem vp144 : productBlend (3/4) (4/5) (⟨(469/1549),(1/1549),0,0⟩ : CertField) (⟨(579/1894),(-1/1894),0,0⟩ : CertField) = vec144 := by
  rw [cp397, cp398]
  exact s_blend_scaled n397 n398 1549 1894 pos397 pos398
private def ivec145 : Fin 3 → IntField := fun j => blendN 400 sE sF n400 n401 25486 1594 j
private def dvec145 : Fin 3 → ℤ := fun _ => 400*25486*1594
private def vec145 : Fin 3 → CertField := fun j => scaled (ivec145 j) (dvec145 j)
private theorem dpos145 : ∀ j, (0:ℤ) < dvec145 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos400) pos401
private theorem vp145 : productBlend (3/4) (4/5) (⟨(7739/25486),0,0,(1/25486)⟩ : CertField) (⟨(489/1594),0,0,(-1/1594)⟩ : CertField) = vec145 := by
  rw [cp400, cp401]
  exact s_blend_scaled n400 n401 25486 1594 pos400 pos401
private def ivec146 : Fin 3 → IntField := fun j => blendN 400 sE sF n404 n401 922 1594 j
private def dvec146 : Fin 3 → ℤ := fun _ => 400*922*1594
private def vec146 : Fin 3 → CertField := fun j => scaled (ivec146 j) (dvec146 j)
private theorem dpos146 : ∀ j, (0:ℤ) < dvec146 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos404) pos401
private theorem vp146 : productBlend (3/4) (4/5) (⟨(275/922),0,0,(1/922)⟩ : CertField) (⟨(489/1594),0,0,(-1/1594)⟩ : CertField) = vec146 := by
  rw [cp404, cp401]
  exact s_blend_scaled n404 n401 922 1594 pos404 pos401
private def ivec147 : Fin 3 → IntField := fun j => blendN 144 rE rF n276 n363 20353 1033 j
private def dvec147 : Fin 3 → ℤ := fun _ => 144*20353*1033
private def vec147 : Fin 3 → CertField := fun j => scaled (ivec147 j) (dvec147 j)
private theorem dpos147 : ∀ j, (0:ℤ) < dvec147 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos276) pos363
private theorem vp147 : productBlend (1/4) (1/3) (⟨(7480/20353),(1/20353),0,0⟩ : CertField) (⟨(383/1033),(-1/1033),0,0⟩ : CertField) = vec147 := by
  rw [cp276, cp363]
  exact r_blend_scaled n276 n363 20353 1033 pos276 pos363
private def ivec148 : Fin 3 → IntField := fun j => blendN 400 sE sF n384 n414 814 16393 j
private def dvec148 : Fin 3 → ℤ := fun _ => 400*814*16393
private def vec148 : Fin 3 → CertField := fun j => scaled (ivec148 j) (dvec148 j)
private theorem dpos148 : ∀ j, (0:ℤ) < dvec148 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos384) pos414
private theorem vp148 : productBlend (3/4) (4/5) (⟨(237/814),(1/814),0,0⟩ : CertField) (⟨(4840/16393),(-1/16393),0,0⟩ : CertField) = vec148 := by
  rw [cp384, cp414]
  exact s_blend_scaled n384 n414 814 16393 pos384 pos414
private def ivec149 : Fin 3 → IntField := fun j => blendN 144 rE rF n420 n421 20418 1510 j
private def dvec149 : Fin 3 → ℤ := fun _ => 144*20418*1510
private def vec149 : Fin 3 → CertField := fun j => scaled (ivec149 j) (dvec149 j)
private theorem dpos149 : ∀ j, (0:ℤ) < dvec149 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos420) pos421
private theorem vp149 : productBlend (1/4) (1/3) (⟨(2587/6806),0,0,(1/20418)⟩ : CertField) (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) = vec149 := by
  rw [cp420, cp421]
  exact r_blend_scaled n420 n421 20418 1510 pos420 pos421
private def ivec150 : Fin 3 → IntField := fun j => blendN 144 rE rF n423 n421 510 1510 j
private def dvec150 : Fin 3 → ℤ := fun _ => 144*510*1510
private def vec150 : Fin 3 → CertField := fun j => scaled (ivec150 j) (dvec150 j)
private theorem dpos150 : ∀ j, (0:ℤ) < dvec150 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos423) pos421
private theorem vp150 : productBlend (1/4) (1/3) (⟨(63/170),0,0,(1/510)⟩ : CertField) (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) = vec150 := by
  rw [cp423, cp421]
  exact r_blend_scaled n423 n421 510 1510 pos423 pos421
private def ivec151 : Fin 3 → IntField := fun j => blendN 144 rE rF n425 n426 1177 1702 j
private def dvec151 : Fin 3 → ℤ := fun _ => 144*1177*1702
private def vec151 : Fin 3 → CertField := fun j => scaled (ivec151 j) (dvec151 j)
private theorem dpos151 : ∀ j, (0:ℤ) < dvec151 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos425) pos426
private theorem vp151 : productBlend (1/4) (1/3) (⟨(446/1177),(1/1177),0,0⟩ : CertField) (⟨(651/1702),(-1/1702),0,0⟩ : CertField) = vec151 := by
  rw [cp425, cp426]
  exact r_blend_scaled n425 n426 1177 1702 pos425 pos426
private def ivec152 : Fin 3 → IntField := fun j => blendN 144 rE rF n425 n429 1177 25521 j
private def dvec152 : Fin 3 → ℤ := fun _ => 144*1177*25521
private def vec152 : Fin 3 → CertField := fun j => scaled (ivec152 j) (dvec152 j)
private theorem dpos152 : ∀ j, (0:ℤ) < dvec152 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos425) pos429
private theorem vp152 : productBlend (1/4) (1/3) (⟨(446/1177),(1/1177),0,0⟩ : CertField) (⟨(3247/8507),(-1/25521),0,0⟩ : CertField) = vec152 := by
  rw [cp425, cp429]
  exact r_blend_scaled n425 n429 1177 25521 pos425 pos429
private def ivec153 : Fin 3 → IntField := fun j => blendN 400 sE sF n348 n433 1090 15090 j
private def dvec153 : Fin 3 → ℤ := fun _ => 400*1090*15090
private def vec153 : Fin 3 → CertField := fun j => scaled (ivec153 j) (dvec153 j)
private theorem dpos153 : ∀ j, (0:ℤ) < dvec153 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos348) pos433
private theorem vp153 : productBlend (3/4) (4/5) (⟨(299/1090),0,0,(1/1090)⟩ : CertField) (⟨(1403/5030),0,0,(-1/15090)⟩ : CertField) = vec153 := by
  rw [cp348, cp433]
  exact s_blend_scaled n348 n433 1090 15090 pos348 pos433
private def ivec154 : Fin 3 → IntField := fun j => blendN 400 sE sF n437 n346 18654 877 j
private def dvec154 : Fin 3 → ℤ := fun _ => 400*18654*877
private def vec154 : Fin 3 → CertField := fun j => scaled (ivec154 j) (dvec154 j)
private theorem dpos154 : ∀ j, (0:ℤ) < dvec154 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos437) pos346
private theorem vp154 : productBlend (3/4) (4/5) (⟨(1721/6218),(1/18654),0,0⟩ : CertField) (⟨(246/877),(-1/877),0,0⟩ : CertField) = vec154 := by
  rw [cp437, cp346]
  exact s_blend_scaled n437 n346 18654 877 pos437 pos346
private def ivec155 : Fin 3 → IntField := fun j => blendN 144 rE rF n440 n441 45778 3010 j
private def dvec155 : Fin 3 → ℤ := fun _ => 144*45778*3010
private def vec155 : Fin 3 → CertField := fun j => scaled (ivec155 j) (dvec155 j)
private theorem dpos155 : ∀ j, (0:ℤ) < dvec155 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos440) pos441
private theorem vp155 : productBlend (1/4) (1/3) (⟨(17703/45778),0,0,(1/45778)⟩ : CertField) (⟨(167/430),0,0,(-1/3010)⟩ : CertField) = vec155 := by
  rw [cp440, cp441]
  exact r_blend_scaled n440 n441 45778 3010 pos440 pos441
private def ivec156 : Fin 3 → IntField := fun j => blendN 144 rE rF n443 n441 1510 3010 j
private def dvec156 : Fin 3 → ℤ := fun _ => 144*1510*3010
private def vec156 : Fin 3 → CertField := fun j => scaled (ivec156 j) (dvec156 j)
private theorem dpos156 : ∀ j, (0:ℤ) < dvec156 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos443) pos441
private theorem vp156 : productBlend (1/4) (1/3) (⟨(579/1510),0,0,(1/1510)⟩ : CertField) (⟨(167/430),0,0,(-1/3010)⟩ : CertField) = vec156 := by
  rw [cp443, cp441]
  exact r_blend_scaled n443 n441 1510 3010 pos443 pos441
private def ivec157 : Fin 3 → IntField := fun j => blendN 144 rE rF n445 n446 2742 3517 j
private def dvec157 : Fin 3 → ℤ := fun _ => 144*2742*3517
private def vec157 : Fin 3 → CertField := fun j => scaled (ivec157 j) (dvec157 j)
private theorem dpos157 : ∀ j, (0:ℤ) < dvec157 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos445) pos446
private theorem vp157 : productBlend (1/4) (1/3) (⟨(353/914),(1/2742),0,0⟩ : CertField) (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) = vec157 := by
  rw [cp445, cp446]
  exact r_blend_scaled n445 n446 2742 3517 pos445 pos446
private def ivec158 : Fin 3 → IntField := fun j => blendN 144 rE rF n445 n449 2742 54241 j
private def dvec158 : Fin 3 → ℤ := fun _ => 144*2742*54241
private def vec158 : Fin 3 → CertField := fun j => scaled (ivec158 j) (dvec158 j)
private theorem dpos158 : ∀ j, (0:ℤ) < dvec158 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos445) pos449
private theorem vp158 : productBlend (1/4) (1/3) (⟨(353/914),(1/2742),0,0⟩ : CertField) (⟨(21015/54241),(-1/54241),0,0⟩ : CertField) = vec158 := by
  rw [cp445, cp449]
  exact r_blend_scaled n445 n449 2742 54241 pos445 pos449
private def ivec159 : Fin 3 → IntField := fun j => blendN 144 rE rF n171 n188 1429 454 j
private def dvec159 : Fin 3 → ℤ := fun _ => 144*1429*454
private def vec159 : Fin 3 → CertField := fun j => scaled (ivec159 j) (dvec159 j)
private theorem dpos159 : ∀ j, (0:ℤ) < dvec159 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos171) pos188
private theorem vp159 : productBlend (1/4) (1/3) (⟨(553/1429),(1/1429),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec159 := by
  rw [cp171, cp188]
  exact r_blend_scaled n171 n188 1429 454 pos171 pos188
private def ivec160 : Fin 3 → IntField := fun j => blendN 144 rE rF n183 n188 20022 454 j
private def dvec160 : Fin 3 → ℤ := fun _ => 144*20022*454
private def vec160 : Fin 3 → CertField := fun j => scaled (ivec160 j) (dvec160 j)
private theorem dpos160 : ∀ j, (0:ℤ) < dvec160 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos183) pos188
private theorem vp160 : productBlend (1/4) (1/3) (⟨(2589/6674),(1/20022),0,0⟩ : CertField) (⟨(177/454),(-1/454),0,0⟩ : CertField) = vec160 := by
  rw [cp183, cp188]
  exact r_blend_scaled n183 n188 20022 454 pos183 pos188
private def ivec161 : Fin 3 → IntField := fun j => blendN 144 rE rF n159 n458 670 24198 j
private def dvec161 : Fin 3 → ℤ := fun _ => 144*670*24198
private def vec161 : Fin 3 → CertField := fun j => scaled (ivec161 j) (dvec161 j)
private theorem dpos161 : ∀ j, (0:ℤ) < dvec161 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos159) pos458
private theorem vp161 : productBlend (1/4) (1/3) (⟨(251/670),0,0,(1/670)⟩ : CertField) (⟨(3079/8066),0,0,(-1/24198)⟩ : CertField) = vec161 := by
  rw [cp159, cp458]
  exact r_blend_scaled n159 n458 670 24198 pos159 pos458
private def ivec162 : Fin 3 → IntField := fun j => blendN 144 rE rF n159 n460 670 1770 j
private def dvec162 : Fin 3 → ℤ := fun _ => 144*670*1770
private def vec162 : Fin 3 → CertField := fun j => scaled (ivec162 j) (dvec162 j)
private theorem dpos162 : ∀ j, (0:ℤ) < dvec162 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos159) pos460
private theorem vp162 : productBlend (1/4) (1/3) (⟨(251/670),0,0,(1/670)⟩ : CertField) (⟨(227/590),0,0,(-1/1770)⟩ : CertField) = vec162 := by
  rw [cp159, cp460]
  exact r_blend_scaled n159 n460 670 1770 pos159 pos460
private def ivec163 : Fin 3 → IntField := fun j => blendN 144 rE rF n466 n426 21741 1702 j
private def dvec163 : Fin 3 → ℤ := fun _ => 144*21741*1702
private def vec163 : Fin 3 → CertField := fun j => scaled (ivec163 j) (dvec163 j)
private theorem dpos163 : ∀ j, (0:ℤ) < dvec163 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos466) pos426
private theorem vp163 : productBlend (1/4) (1/3) (⟨(2755/7247),(1/21741),0,0⟩ : CertField) (⟨(651/1702),(-1/1702),0,0⟩ : CertField) = vec163 := by
  rw [cp466, cp426]
  exact r_blend_scaled n466 n426 21741 1702 pos466 pos426
private def ivec164 : Fin 3 → IntField := fun j => blendN 400 sE sF n112 n469 514 15526 j
private def dvec164 : Fin 3 → ℤ := fun _ => 400*514*15526
private def vec164 : Fin 3 → CertField := fun j => scaled (ivec164 j) (dvec164 j)
private theorem dpos164 : ∀ j, (0:ℤ) < dvec164 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos112) pos469
private theorem vp164 : productBlend (3/4) (4/5) (⟨(147/514),0,0,(1/514)⟩ : CertField) (⟨(655/2218),0,0,(-1/15526)⟩ : CertField) = vec164 := by
  rw [cp112, cp469]
  exact s_blend_scaled n112 n469 514 15526 pos112 pos469
private def ivec165 : Fin 3 → IntField := fun j => blendN 400 sE sF n112 n472 514 1042 j
private def dvec165 : Fin 3 → ℤ := fun _ => 400*514*1042
private def vec165 : Fin 3 → CertField := fun j => scaled (ivec165 j) (dvec165 j)
private theorem dpos165 : ∀ j, (0:ℤ) < dvec165 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos112) pos472
private theorem vp165 : productBlend (3/4) (4/5) (⟨(147/514),0,0,(1/514)⟩ : CertField) (⟨(313/1042),0,0,(-1/1042)⟩ : CertField) = vec165 := by
  rw [cp112, cp472]
  exact s_blend_scaled n112 n472 514 1042 pos112 pos472
private def ivec166 : Fin 3 → IntField := fun j => blendN 400 sE sF n474 n385 14557 1069 j
private def dvec166 : Fin 3 → ℤ := fun _ => 400*14557*1069
private def vec166 : Fin 3 → CertField := fun j => scaled (ivec166 j) (dvec166 j)
private theorem dpos166 : ∀ j, (0:ℤ) < dvec166 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos474) pos385
private theorem vp166 : productBlend (3/4) (4/5) (⟨(4264/14557),(1/14557),0,0⟩ : CertField) (⟨(317/1069),(-1/1069),0,0⟩ : CertField) = vec166 := by
  rw [cp474, cp385]
  exact s_blend_scaled n474 n385 14557 1069 pos474 pos385
private def ivec167 : Fin 3 → IntField := fun j => blendN 400 sE sF n485 n486 1042 27970 j
private def dvec167 : Fin 3 → ℤ := fun _ => 400*1042*27970
private def vec167 : Fin 3 → CertField := fun j => scaled (ivec167 j) (dvec167 j)
private theorem dpos167 : ∀ j, (0:ℤ) < dvec167 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos485) pos486
private theorem vp167 : productBlend (3/4) (4/5) (⟨(313/1042),0,0,(1/1042)⟩ : CertField) (⟨(8531/27970),0,0,(-1/27970)⟩ : CertField) = vec167 := by
  rw [cp485, cp486]
  exact s_blend_scaled n485 n486 1042 27970 pos485 pos486
private def ivec168 : Fin 3 → IntField := fun j => blendN 400 sE sF n485 n489 1042 1750 j
private def dvec168 : Fin 3 → ℤ := fun _ => 400*1042*1750
private def vec168 : Fin 3 → CertField := fun j => scaled (ivec168 j) (dvec168 j)
private theorem dpos168 : ∀ j, (0:ℤ) < dvec168 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos485) pos489
private theorem vp168 : productBlend (3/4) (4/5) (⟨(313/1042),0,0,(1/1042)⟩ : CertField) (⟨(77/250),0,0,(-1/1750)⟩ : CertField) = vec168 := by
  rw [cp485, cp489]
  exact s_blend_scaled n485 n489 1042 1750 pos485 pos489
private def ivec169 : Fin 3 → IntField := fun j => blendN 400 sE sF n491 n398 27073 1894 j
private def dvec169 : Fin 3 → ℤ := fun _ => 400*27073*1894
private def vec169 : Fin 3 → CertField := fun j => scaled (ivec169 j) (dvec169 j)
private theorem dpos169 : ∀ j, (0:ℤ) < dvec169 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos491) pos398
private theorem vp169 : productBlend (3/4) (4/5) (⟨(8222/27073),(1/27073),0,0⟩ : CertField) (⟨(579/1894),(-1/1894),0,0⟩ : CertField) = vec169 := by
  rw [cp491, cp398]
  exact s_blend_scaled n491 n398 27073 1894 pos491 pos398
private def ivec170 : Fin 3 → IntField := fun j => blendN 144 rE rF n176 n495 1770 51358 j
private def dvec170 : Fin 3 → ℤ := fun _ => 144*1770*51358
private def vec170 : Fin 3 → CertField := fun j => scaled (ivec170 j) (dvec170 j)
private theorem dpos170 : ∀ j, (0:ℤ) < dvec170 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos176) pos495
private theorem vp170 : productBlend (1/4) (1/3) (⟨(227/590),0,0,(1/1770)⟩ : CertField) (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) = vec170 := by
  rw [cp176, cp495]
  exact r_blend_scaled n176 n495 1770 51358 pos176 pos495
private def ivec171 : Fin 3 → IntField := fun j => blendN 144 rE rF n176 n497 1770 3370 j
private def dvec171 : Fin 3 → ℤ := fun _ => 144*1770*3370
private def vec171 : Fin 3 → CertField := fun j => scaled (ivec171 j) (dvec171 j)
private theorem dpos171 : ∀ j, (0:ℤ) < dvec171 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos176) pos497
private theorem vp171 : productBlend (1/4) (1/3) (⟨(227/590),0,0,(1/1770)⟩ : CertField) (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) = vec171 := by
  rw [cp176, cp497]
  exact r_blend_scaled n176 n497 1770 3370 pos176 pos497
private def ivec172 : Fin 3 → IntField := fun j => blendN 144 rE rF n503 n446 48661 3517 j
private def dvec172 : Fin 3 → ℤ := fun _ => 144*48661*3517
private def vec172 : Fin 3 → CertField := fun j => scaled (ivec172 j) (dvec172 j)
private theorem dpos172 : ∀ j, (0:ℤ) < dvec172 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos503) pos446
private theorem vp172 : productBlend (1/4) (1/3) (⟨(18819/48661),(1/48661),0,0⟩ : CertField) (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) = vec172 := by
  rw [cp503, cp446]
  exact r_blend_scaled n503 n446 48661 3517 pos503 pos446
private def ivec173 : Fin 3 → IntField := fun j => blendN 144 rE rF n513 n514 3370 88618 j
private def dvec173 : Fin 3 → ℤ := fun _ => 144*3370*88618
private def vec173 : Fin 3 → CertField := fun j => scaled (ivec173 j) (dvec173 j)
private theorem dpos173 : ∀ j, (0:ℤ) < dvec173 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos513) pos514
private theorem vp173 : productBlend (1/4) (1/3) (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) = vec173 := by
  rw [cp513, cp514]
  exact r_blend_scaled n513 n514 3370 88618 pos513 pos514
private def ivec174 : Fin 3 → IntField := fun j => blendN 144 rE rF n513 n516 3370 5470 j
private def dvec174 : Fin 3 → ℤ := fun _ => 144*3370*5470
private def vec174 : Fin 3 → CertField := fun j => scaled (ivec174 j) (dvec174 j)
private theorem dpos174 : ∀ j, (0:ℤ) < dvec174 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos513) pos516
private theorem vp174 : productBlend (1/4) (1/3) (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) = vec174 := by
  rw [cp513, cp516]
  exact r_blend_scaled n513 n516 3370 5470 pos513 pos516
private def ivec175 : Fin 3 → IntField := fun j => blendN 144 rE rF n518 n519 3010 5010 j
private def dvec175 : Fin 3 → ℤ := fun _ => 144*3010*5010
private def vec175 : Fin 3 → CertField := fun j => scaled (ivec175 j) (dvec175 j)
private theorem dpos175 : ∀ j, (0:ℤ) < dvec175 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos518) pos519
private theorem vp175 : productBlend (1/4) (1/3) (⟨(167/430),0,0,(1/3010)⟩ : CertField) (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) = vec175 := by
  rw [cp518, cp519]
  exact r_blend_scaled n518 n519 3010 5010 pos518 pos519
private def ivec176 : Fin 3 → IntField := fun j => blendN 144 rE rF n521 n522 4957 5982 j
private def dvec176 : Fin 3 → ℤ := fun _ => 144*4957*5982
private def vec176 : Fin 3 → CertField := fun j => scaled (ivec176 j) (dvec176 j)
private theorem dpos176 : ∀ j, (0:ℤ) < dvec176 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos521) pos522
private theorem vp176 : productBlend (1/4) (1/3) (⟨(1932/4957),(1/4957),0,0⟩ : CertField) (⟨(779/1994),(-1/5982),0,0⟩ : CertField) = vec176 := by
  rw [cp521, cp522]
  exact r_blend_scaled n521 n522 4957 5982 pos521 pos522
private def ivec177 : Fin 3 → IntField := fun j => blendN 144 rE rF n526 n522 86281 5982 j
private def dvec177 : Fin 3 → ℤ := fun _ => 144*86281*5982
private def vec177 : Fin 3 → CertField := fun j => scaled (ivec177 j) (dvec177 j)
private theorem dpos177 : ∀ j, (0:ℤ) < dvec177 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos526) pos522
private theorem vp177 : productBlend (1/4) (1/3) (⟨(33653/86281),(1/86281),0,0⟩ : CertField) (⟨(779/1994),(-1/5982),0,0⟩ : CertField) = vec177 := by
  rw [cp526, cp522]
  exact r_blend_scaled n526 n522 86281 5982 pos526 pos522
private def ivec178 : Fin 3 → IntField := fun j => blendN 144 rE rF n238 n232 33937 709 j
private def dvec178 : Fin 3 → ℤ := fun _ => 144*33937*709
private def vec178 : Fin 3 → CertField := fun j => scaled (ivec178 j) (dvec178 j)
private theorem dpos178 : ∀ j, (0:ℤ) < dvec178 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos238) pos232
private theorem vp178 : productBlend (1/4) (1/3) (⟨(13260/33937),(1/33937),0,0⟩ : CertField) (⟨(278/709),(-1/709),0,0⟩ : CertField) = vec178 := by
  rw [cp238, cp232]
  exact r_blend_scaled n238 n232 33937 709 pos238 pos232
private def ivec179 : Fin 3 → IntField := fun j => blendN 400 sE sF n327 n564 2461 34318 j
private def dvec179 : Fin 3 → ℤ := fun _ => 400*2461*34318
private def vec179 : Fin 3 → CertField := fun j => scaled (ivec179 j) (dvec179 j)
private theorem dpos179 : ∀ j, (0:ℤ) < dvec179 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos327) pos564
private theorem vp179 : productBlend (3/4) (4/5) (⟨(660/2461),(1/2461),0,0⟩ : CertField) (⟨(9257/34318),(-1/34318),0,0⟩ : CertField) = vec179 := by
  rw [cp327, cp564]
  exact s_blend_scaled n327 n564 2461 34318 pos327 pos564
private def ivec180 : Fin 3 → IntField := fun j => blendN 144 rE rF n571 n572 41226 3178 j
private def dvec180 : Fin 3 → ℤ := fun _ => 144*41226*3178
private def vec180 : Fin 3 → CertField := fun j => scaled (ivec180 j) (dvec180 j)
private theorem dpos180 : ∀ j, (0:ℤ) < dvec180 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos571) pos572
private theorem vp180 : productBlend (1/4) (1/3) (⟨(5033/13742),0,0,(1/41226)⟩ : CertField) (⟨(167/454),0,0,(-1/3178)⟩ : CertField) = vec180 := by
  rw [cp571, cp572]
  exact r_blend_scaled n571 n572 41226 3178 pos571 pos572
private def ivec181 : Fin 3 → IntField := fun j => blendN 144 rE rF n574 n572 906 3178 j
private def dvec181 : Fin 3 → ℤ := fun _ => 144*906*3178
private def vec181 : Fin 3 → CertField := fun j => scaled (ivec181 j) (dvec181 j)
private theorem dpos181 : ∀ j, (0:ℤ) < dvec181 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos574) pos572
private theorem vp181 : productBlend (1/4) (1/3) (⟨(109/302),0,0,(1/906)⟩ : CertField) (⟨(167/454),0,0,(-1/3178)⟩ : CertField) = vec181 := by
  rw [cp574, cp572]
  exact r_blend_scaled n574 n572 906 3178 pos574 pos572
private def ivec182 : Fin 3 → IntField := fun j => blendN 144 rE rF n576 n577 2341 3541 j
private def dvec182 : Fin 3 → ℤ := fun _ => 144*2341*3541
private def vec182 : Fin 3 → CertField := fun j => scaled (ivec182 j) (dvec182 j)
private theorem dpos182 : ∀ j, (0:ℤ) < dvec182 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos576) pos577
private theorem vp182 : productBlend (1/4) (1/3) (⟨(856/2341),(1/2341),0,0⟩ : CertField) (⟨(1301/3541),(-1/3541),0,0⟩ : CertField) = vec182 := by
  rw [cp576, cp577]
  exact r_blend_scaled n576 n577 2341 3541 pos576 pos577
private def ivec183 : Fin 3 → IntField := fun j => blendN 144 rE rF n576 n580 2341 52566 j
private def dvec183 : Fin 3 → ℤ := fun _ => 144*2341*52566
private def vec183 : Fin 3 → CertField := fun j => scaled (ivec183 j) (dvec183 j)
private theorem dpos183 : ∀ j, (0:ℤ) < dvec183 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos576) pos580
private theorem vp183 : productBlend (1/4) (1/3) (⟨(856/2341),(1/2341),0,0⟩ : CertField) (⟨(6431/17522),(-1/52566),0,0⟩ : CertField) = vec183 := by
  rw [cp576, cp580]
  exact r_blend_scaled n576 n580 2341 52566 pos576 pos580
private def ivec184 : Fin 3 → IntField := fun j => blendN 144 rE rF n273 n582 1258 49866 j
private def dvec184 : Fin 3 → ℤ := fun _ => 144*1258*49866
private def vec184 : Fin 3 → CertField := fun j => scaled (ivec184 j) (dvec184 j)
private theorem dpos184 : ∀ j, (0:ℤ) < dvec184 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos273) pos582
private theorem vp184 : productBlend (1/4) (1/3) (⟨(457/1258),0,0,(1/1258)⟩ : CertField) (⟨(6101/16622),0,0,(-1/49866)⟩ : CertField) = vec184 := by
  rw [cp273, cp582]
  exact r_blend_scaled n273 n582 1258 49866 pos273 pos582
private def ivec185 : Fin 3 → IntField := fun j => blendN 400 sE sF n330 n586 2098 32290 j
private def dvec185 : Fin 3 → ℤ := fun _ => 400*2098*32290
private def vec185 : Fin 3 → CertField := fun j => scaled (ivec185 j) (dvec185 j)
private theorem dpos185 : ∀ j, (0:ℤ) < dvec185 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos330) pos586
private theorem vp185 : productBlend (3/4) (4/5) (⟨(561/2098),0,0,(1/2098)⟩ : CertField) (⟨(8711/32290),0,0,(-1/32290)⟩ : CertField) = vec185 := by
  rw [cp330, cp586]
  exact s_blend_scaled n330 n586 2098 32290 pos330 pos586
private def ivec186 : Fin 3 → IntField := fun j => blendN 400 sE sF n590 n328 38062 1941 j
private def dvec186 : Fin 3 → ℤ := fun _ => 400*38062*1941
private def vec186 : Fin 3 → CertField := fun j => scaled (ivec186 j) (dvec186 j)
private theorem dpos186 : ∀ j, (0:ℤ) < dvec186 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos590) pos328
private theorem vp186 : productBlend (3/4) (4/5) (⟨(10229/38062),(1/38062),0,0⟩ : CertField) (⟨(175/647),(-1/1941),0,0⟩ : CertField) = vec186 := by
  rw [cp590, cp328]
  exact s_blend_scaled n590 n328 38062 1941 pos590 pos328
private def ivec187 : Fin 3 → IntField := fun j => blendN 144 rE rF n152 n152 9250 9250 j
private def dvec187 : Fin 3 → ℤ := fun _ => 144*9250*9250
private def vec187 : Fin 3 → CertField := fun j => scaled (ivec187 j) (dvec187 j)
private theorem dpos187 : ∀ j, (0:ℤ) < dvec187 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos152) pos152
private theorem vp187 : productBlend (1/4) (1/3) (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) = vec187 := by
  rw [cp152]
  exact r_blend_scaled n152 n152 9250 9250 pos152 pos152
private def ivec188 : Fin 3 → IntField := fun j => blendN 400 sE sF n16 n16 94 94 j
private def dvec188 : Fin 3 → ℤ := fun _ => 400*94*94
private def vec188 : Fin 3 → CertField := fun j => scaled (ivec188 j) (dvec188 j)
private theorem dpos188 : ∀ j, (0:ℤ) < dvec188 j := by
  intro j
  exact mul_pos (mul_pos (by norm_num) pos16) pos16
private theorem vp188 : productBlend (3/4) (4/5) (⟨(31/94),0,0,(-1/94)⟩ : CertField) (⟨(31/94),0,0,(-1/94)⟩ : CertField) = vec188 := by
  rw [cp16]
  exact s_blend_scaled n16 n16 94 94 pos16 pos16

private def eb1 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def eb110 : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

private def eb114 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

private def eb115 : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

private def eb145 : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩

private def eb146 : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩

private def eb147 : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩

private def eb162 : CertBound := ⟨false,true,⟨⟨(193703/848225),0,0,(-4748/848225)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb164 : CertBound := ⟨false,false,⟨⟨(13109/43885),0,0,(-176/43885)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb165 : CertBound := ⟨false,false,⟨⟨(3049/8282),0,0,(-391/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb170 : CertBound := ⟨true,false,⟨⟨(64145/160843),0,0,(311040/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb172 : CertBound := ⟨true,true,⟨⟨(628621/804215),0,0,(62208/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb173 : CertBound := ⟨true,true,⟨⟨(3553/4141),0,0,(108/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩

private def eb183 : CertBound := ⟨false,false,⟨⟨(1355921/3029375),0,0,(-33236/3029375)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb186 : CertBound := ⟨true,true,⟨⟨(9833/12314),0,0,(-171/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb194 : CertBound := ⟨true,false,⟨⟨(3216375/580027),0,0,(-294950/580027)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩

private def eb195 : CertBound := ⟨true,true,⟨⟨(25971/6157),0,0,(-34/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩

private def eb196 : CertBound := ⟨true,true,⟨⟨(900585/82861),0,0,(-82586/82861)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩

private def eb216 : CertBound := ⟨false,false,⟨⟨(33/101),0,0,(-4/707)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb218 : CertBound := ⟨false,true,⟨⟨(566107/1696450),0,0,(39413/1696450)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb225 : CertBound := ⟨true,false,⟨⟨(566107/1696450),0,0,(39413/1696450)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb229 : CertBound := ⟨true,true,⟨⟨(3962749/6058750),0,0,(275891/6058750)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb230 : CertBound := ⟨true,true,⟨⟨(8727/12314),0,0,(-143/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb242 : CertBound := ⟨true,false,⟨⟨(583805/165722),0,0,(-89725/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

private def eb244 : CertBound := ⟨true,true,⟨⟨(5721289/828610),0,0,(-25123/165722)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩

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

private def eb327 : CertBound := ⟨true,false,⟨⟨(1520885/1160054),0,0,(11855/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb329 : CertBound := ⟨true,true,⟨⟨(2129239/828610),0,0,(16597/828610)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def eb346 : CertBound := ⟨false,true,⟨⟨(922125/1160054),0,0,(-75625/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb348 : CertBound := ⟨true,false,⟨⟨(922125/1160054),0,0,(-75625/1160054)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb349 : CertBound := ⟨true,true,⟨⟨(258195/165722),0,0,(-21175/165722)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩

private def eb355 : CertBound := ⟨true,true,⟨⟨(671227/1541891),(499219/1541891),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb356 : CertBound := ⟨true,true,⟨⟨(6116773/18621299),(5788260/18621299),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩

private def eb357 : CertBound := ⟨true,true,⟨⟨(17121447/34534643),(7927814/34534643),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def eb359 : CertBound := ⟨false,true,⟨⟨(1007355/2251802),0,0,(-21065/2251802)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb375 : CertBound := ⟨false,true,⟨⟨(341305/1564547),0,0,(11720/10951829)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

private def eb376 : CertBound := ⟨false,true,⟨⟨(-8563189/52684372),(17479377/52684372),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩

private def eb380 : CertBound := ⟨false,false,⟨⟨(3344789/7822735),0,0,(16408/7822735)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1803/4622),0,0,(-1/13866)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩

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

private def eb533 : CertBound := ⟨true,true,⟨⟨(796509/1603375),0,0,(-72632/4810125)⟩,⟨(2463/6350),0,0,(1/19050)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

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

private def eb624 : CertBound := ⟨true,true,⟨⟨(114887/8457119),(6029423/25371357),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

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

private def eb833 : CertBound := ⟨true,true,⟨⟨(1893227/6455450),0,0,(165991/6455450)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

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

private def eb1176 : CertBound := ⟨false,false,⟨⟨(873/646),0,0,(-451/1938)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1178 : CertBound := ⟨true,false,⟨⟨(16587/850),0,0,(-8569/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1180 : CertBound := ⟨false,false,⟨⟨(545/646),0,0,(-299/1938)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1182 : CertBound := ⟨true,false,⟨⟨(2071/170),0,0,(-5681/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1184 : CertBound := ⟨false,false,⟨⟨(373/1406),0,0,(-187/29526)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1186 : CertBound := ⟨true,false,⟨⟨(7087/1850),0,0,(-3553/38850)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1188 : CertBound := ⟨false,false,⟨⟨(241/323),0,0,(-44/323)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1190 : CertBound := ⟨true,false,⟨⟨(4579/425),0,0,(-836/425)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1192 : CertBound := ⟨false,false,⟨⟨(341/646),0,0,(-43/646)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1194 : CertBound := ⟨true,false,⟨⟨(6479/850),0,0,(-817/850)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1196 : CertBound := ⟨false,false,⟨⟨(331/1406),0,0,(-53/9842)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1198 : CertBound := ⟨true,false,⟨⟨(6289/1850),0,0,(-1007/12950)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1200 : CertBound := ⟨false,false,⟨⟨(49165/233966),0,0,(-45/12314)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1202 : CertBound := ⟨true,false,⟨⟨(186827/61570),0,0,(-3249/61570)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1204 : CertBound := ⟨false,false,⟨⟨(15245/157358),0,0,(-1955/1101506)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1206 : CertBound := ⟨true,false,⟨⟨(57931/41410),0,0,(-7429/289870)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def eb1208 : CertBound := ⟨false,false,⟨⟨(43635/233966),0,0,(-715/233966)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1210 : CertBound := ⟨true,false,⟨⟨(165813/61570),0,0,(-2717/61570)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1212 : CertBound := ⟨false,false,⟨⟨(25575/116983),0,0,(130/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1214 : CertBound := ⟨true,false,⟨⟨(19437/6157),0,0,(9386/30785)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1216 : CertBound := ⟨false,false,⟨⟨(165/1919),0,0,(-20/13433)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1218 : CertBound := ⟨true,false,⟨⟨(627/505),0,0,(-76/3535)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1220 : CertBound := ⟨false,false,⟨⟨(4835/25726),0,0,(-295/9478)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1222 : CertBound := ⟨true,false,⟨⟨(18373/6770),0,0,(-21299/47390)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩

private def eb1224 : CertBound := ⟨false,false,⟨⟨(15825/157358),0,0,(10615/1101506)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1226 : CertBound := ⟨true,false,⟨⟨(12027/8282),0,0,(40337/289870)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1228 : CertBound := ⟨false,false,⟨⟨(367/1273),0,0,(-176/8911)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1230 : CertBound := ⟨true,false,⟨⟨(6973/1675),0,0,(-3344/11725)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1232 : CertBound := ⟨false,false,⟨⟨(669/1406),0,0,(109/29526)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1234 : CertBound := ⟨true,false,⟨⟨(12711/1850),0,0,(2071/38850)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩

private def eb1236 : CertBound := ⟨false,false,⟨⟨(1825/12863),0,0,(-1160/90041)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def eb1238 : CertBound := ⟨true,false,⟨⟨(1387/677),0,0,(-4408/23695)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

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
    lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 id = b := by
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
  (lowerEarlyTerminalBounds01[109]? = some eb110) ∧
  (lowerEarlyTerminalBounds01[113]? = some eb114) ∧
  (lowerEarlyTerminalBounds01[114]? = some eb115) ∧
  (lowerEarlyTerminalBounds01[144]? = some eb145) ∧
  (lowerEarlyTerminalBounds01[145]? = some eb146) ∧
  (lowerEarlyTerminalBounds01[146]? = some eb147) := by
  exact And.intro (Eq.refl (some eb1)) (And.intro (Eq.refl (some eb110)) (And.intro (Eq.refl (some eb114)) (And.intro (Eq.refl (some eb115)) (And.intro (Eq.refl (some eb145)) (And.intro (Eq.refl (some eb146)) (Eq.refl (some eb147)))))))

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
  (lowerEarlyTerminalBounds02[11]? = some eb162) ∧
  (lowerEarlyTerminalBounds02[13]? = some eb164) ∧
  (lowerEarlyTerminalBounds02[14]? = some eb165) ∧
  (lowerEarlyTerminalBounds02[19]? = some eb170) ∧
  (lowerEarlyTerminalBounds02[21]? = some eb172) ∧
  (lowerEarlyTerminalBounds02[22]? = some eb173) ∧
  (lowerEarlyTerminalBounds02[32]? = some eb183) ∧
  (lowerEarlyTerminalBounds02[35]? = some eb186) ∧
  (lowerEarlyTerminalBounds02[43]? = some eb194) ∧
  (lowerEarlyTerminalBounds02[44]? = some eb195) ∧
  (lowerEarlyTerminalBounds02[45]? = some eb196) ∧
  (lowerEarlyTerminalBounds02[65]? = some eb216) ∧
  (lowerEarlyTerminalBounds02[67]? = some eb218) ∧
  (lowerEarlyTerminalBounds02[74]? = some eb225) ∧
  (lowerEarlyTerminalBounds02[78]? = some eb229) ∧
  (lowerEarlyTerminalBounds02[79]? = some eb230) ∧
  (lowerEarlyTerminalBounds02[91]? = some eb242) ∧
  (lowerEarlyTerminalBounds02[93]? = some eb244) ∧
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
  exact And.intro (Eq.refl (some eb162)) (And.intro (Eq.refl (some eb164)) (And.intro (Eq.refl (some eb165)) (And.intro (Eq.refl (some eb170)) (And.intro (Eq.refl (some eb172)) (And.intro (Eq.refl (some eb173)) (And.intro (Eq.refl (some eb183)) (And.intro (Eq.refl (some eb186)) (And.intro (Eq.refl (some eb194)) (And.intro (Eq.refl (some eb195)) (And.intro (Eq.refl (some eb196)) (And.intro (Eq.refl (some eb216)) (And.intro (Eq.refl (some eb218)) (And.intro (Eq.refl (some eb225)) (And.intro (Eq.refl (some eb229)) (And.intro (Eq.refl (some eb230)) (And.intro (Eq.refl (some eb242)) (And.intro (Eq.refl (some eb244)) (And.intro (Eq.refl (some eb257)) (And.intro (Eq.refl (some eb258)) (And.intro (Eq.refl (some eb259)) (And.intro (Eq.refl (some eb260)) (And.intro (Eq.refl (some eb261)) (And.intro (Eq.refl (some eb268)) (And.intro (Eq.refl (some eb272)) (And.intro (Eq.refl (some eb280)) (And.intro (Eq.refl (some eb282)) (And.intro (Eq.refl (some eb283)) (And.intro (Eq.refl (some eb286)) (And.intro (Eq.refl (some eb292)) (And.intro (Eq.refl (some eb296)) (And.intro (Eq.refl (some eb297)) (And.intro (Eq.refl (some eb298)) (And.intro (Eq.refl (some eb299)) (Eq.refl (some eb300)))))))))))))))))))))))))))))))))))

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
  (lowerEarlyTerminalBounds03[26]? = some eb327) ∧
  (lowerEarlyTerminalBounds03[28]? = some eb329) ∧
  (lowerEarlyTerminalBounds03[45]? = some eb346) ∧
  (lowerEarlyTerminalBounds03[47]? = some eb348) ∧
  (lowerEarlyTerminalBounds03[48]? = some eb349) ∧
  (lowerEarlyTerminalBounds03[54]? = some eb355) ∧
  (lowerEarlyTerminalBounds03[55]? = some eb356) ∧
  (lowerEarlyTerminalBounds03[56]? = some eb357) ∧
  (lowerEarlyTerminalBounds03[58]? = some eb359) ∧
  (lowerEarlyTerminalBounds03[74]? = some eb375) ∧
  (lowerEarlyTerminalBounds03[75]? = some eb376) ∧
  (lowerEarlyTerminalBounds03[79]? = some eb380) ∧
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
  exact And.intro (Eq.refl (some eb301)) (And.intro (Eq.refl (some eb308)) (And.intro (Eq.refl (some eb312)) (And.intro (Eq.refl (some eb318)) (And.intro (Eq.refl (some eb320)) (And.intro (Eq.refl (some eb321)) (And.intro (Eq.refl (some eb324)) (And.intro (Eq.refl (some eb327)) (And.intro (Eq.refl (some eb329)) (And.intro (Eq.refl (some eb346)) (And.intro (Eq.refl (some eb348)) (And.intro (Eq.refl (some eb349)) (And.intro (Eq.refl (some eb355)) (And.intro (Eq.refl (some eb356)) (And.intro (Eq.refl (some eb357)) (And.intro (Eq.refl (some eb359)) (And.intro (Eq.refl (some eb375)) (And.intro (Eq.refl (some eb376)) (And.intro (Eq.refl (some eb380)) (And.intro (Eq.refl (some eb395)) (And.intro (Eq.refl (some eb396)) (And.intro (Eq.refl (some eb397)) (And.intro (Eq.refl (some eb398)) (And.intro (Eq.refl (some eb399)) (And.intro (Eq.refl (some eb402)) (And.intro (Eq.refl (some eb403)) (And.intro (Eq.refl (some eb404)) (And.intro (Eq.refl (some eb405)) (And.intro (Eq.refl (some eb406)) (And.intro (Eq.refl (some eb408)) (And.intro (Eq.refl (some eb411)) (And.intro (Eq.refl (some eb412)) (And.intro (Eq.refl (some eb414)) (And.intro (Eq.refl (some eb415)) (And.intro (Eq.refl (some eb416)) (And.intro (Eq.refl (some eb419)) (And.intro (Eq.refl (some eb420)) (And.intro (Eq.refl (some eb422)) (And.intro (Eq.refl (some eb424)) (And.intro (Eq.refl (some eb425)) (And.intro (Eq.refl (some eb426)) (And.intro (Eq.refl (some eb427)) (And.intro (Eq.refl (some eb431)) (And.intro (Eq.refl (some eb432)) (And.intro (Eq.refl (some eb433)) (And.intro (Eq.refl (some eb434)) (And.intro (Eq.refl (some eb435)) (And.intro (Eq.refl (some eb436)) (And.intro (Eq.refl (some eb437)) (And.intro (Eq.refl (some eb439)) (And.intro (Eq.refl (some eb440)) (And.intro (Eq.refl (some eb441)) (And.intro (Eq.refl (some eb443)) (And.intro (Eq.refl (some eb446)) (And.intro (Eq.refl (some eb447)) (And.intro (Eq.refl (some eb449)) (Eq.refl (some eb450)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  (lowerEarlyTerminalBounds04[82]? = some eb533) ∧
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
  exact And.intro (Eq.refl (some eb452)) (And.intro (Eq.refl (some eb454)) (And.intro (Eq.refl (some eb455)) (And.intro (Eq.refl (some eb456)) (And.intro (Eq.refl (some eb457)) (And.intro (Eq.refl (some eb460)) (And.intro (Eq.refl (some eb461)) (And.intro (Eq.refl (some eb462)) (And.intro (Eq.refl (some eb463)) (And.intro (Eq.refl (some eb464)) (And.intro (Eq.refl (some eb466)) (And.intro (Eq.refl (some eb468)) (And.intro (Eq.refl (some eb469)) (And.intro (Eq.refl (some eb470)) (And.intro (Eq.refl (some eb471)) (And.intro (Eq.refl (some eb472)) (And.intro (Eq.refl (some eb473)) (And.intro (Eq.refl (some eb474)) (And.intro (Eq.refl (some eb475)) (And.intro (Eq.refl (some eb476)) (And.intro (Eq.refl (some eb477)) (And.intro (Eq.refl (some eb478)) (And.intro (Eq.refl (some eb479)) (And.intro (Eq.refl (some eb480)) (And.intro (Eq.refl (some eb481)) (And.intro (Eq.refl (some eb482)) (And.intro (Eq.refl (some eb483)) (And.intro (Eq.refl (some eb484)) (And.intro (Eq.refl (some eb485)) (And.intro (Eq.refl (some eb486)) (And.intro (Eq.refl (some eb487)) (And.intro (Eq.refl (some eb488)) (And.intro (Eq.refl (some eb490)) (And.intro (Eq.refl (some eb491)) (And.intro (Eq.refl (some eb494)) (And.intro (Eq.refl (some eb495)) (And.intro (Eq.refl (some eb496)) (And.intro (Eq.refl (some eb497)) (And.intro (Eq.refl (some eb498)) (And.intro (Eq.refl (some eb499)) (And.intro (Eq.refl (some eb500)) (And.intro (Eq.refl (some eb501)) (And.intro (Eq.refl (some eb502)) (And.intro (Eq.refl (some eb503)) (And.intro (Eq.refl (some eb504)) (And.intro (Eq.refl (some eb505)) (And.intro (Eq.refl (some eb506)) (And.intro (Eq.refl (some eb507)) (And.intro (Eq.refl (some eb510)) (And.intro (Eq.refl (some eb512)) (And.intro (Eq.refl (some eb513)) (And.intro (Eq.refl (some eb516)) (And.intro (Eq.refl (some eb519)) (And.intro (Eq.refl (some eb522)) (And.intro (Eq.refl (some eb523)) (And.intro (Eq.refl (some eb524)) (And.intro (Eq.refl (some eb525)) (And.intro (Eq.refl (some eb526)) (And.intro (Eq.refl (some eb527)) (And.intro (Eq.refl (some eb528)) (And.intro (Eq.refl (some eb529)) (And.intro (Eq.refl (some eb531)) (And.intro (Eq.refl (some eb532)) (And.intro (Eq.refl (some eb533)) (And.intro (Eq.refl (some eb534)) (And.intro (Eq.refl (some eb535)) (And.intro (Eq.refl (some eb536)) (And.intro (Eq.refl (some eb537)) (And.intro (Eq.refl (some eb538)) (And.intro (Eq.refl (some eb539)) (And.intro (Eq.refl (some eb540)) (And.intro (Eq.refl (some eb545)) (And.intro (Eq.refl (some eb547)) (And.intro (Eq.refl (some eb550)) (And.intro (Eq.refl (some eb553)) (And.intro (Eq.refl (some eb554)) (And.intro (Eq.refl (some eb555)) (And.intro (Eq.refl (some eb556)) (And.intro (Eq.refl (some eb557)) (And.intro (Eq.refl (some eb558)) (And.intro (Eq.refl (some eb559)) (And.intro (Eq.refl (some eb560)) (And.intro (Eq.refl (some eb564)) (And.intro (Eq.refl (some eb567)) (And.intro (Eq.refl (some eb568)) (And.intro (Eq.refl (some eb569)) (And.intro (Eq.refl (some eb570)) (And.intro (Eq.refl (some eb571)) (And.intro (Eq.refl (some eb573)) (And.intro (Eq.refl (some eb575)) (And.intro (Eq.refl (some eb576)) (And.intro (Eq.refl (some eb577)) (And.intro (Eq.refl (some eb578)) (And.intro (Eq.refl (some eb579)) (And.intro (Eq.refl (some eb581)) (And.intro (Eq.refl (some eb582)) (And.intro (Eq.refl (some eb583)) (And.intro (Eq.refl (some eb584)) (And.intro (Eq.refl (some eb585)) (And.intro (Eq.refl (some eb586)) (And.intro (Eq.refl (some eb590)) (And.intro (Eq.refl (some eb591)) (And.intro (Eq.refl (some eb592)) (And.intro (Eq.refl (some eb595)) (Eq.refl (some eb598)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  (lowerEarlyTerminalBounds05[23]? = some eb624) ∧
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
  exact And.intro (Eq.refl (some eb601)) (And.intro (Eq.refl (some eb603)) (And.intro (Eq.refl (some eb604)) (And.intro (Eq.refl (some eb606)) (And.intro (Eq.refl (some eb607)) (And.intro (Eq.refl (some eb608)) (And.intro (Eq.refl (some eb609)) (And.intro (Eq.refl (some eb611)) (And.intro (Eq.refl (some eb612)) (And.intro (Eq.refl (some eb613)) (And.intro (Eq.refl (some eb620)) (And.intro (Eq.refl (some eb621)) (And.intro (Eq.refl (some eb624)) (And.intro (Eq.refl (some eb627)) (And.intro (Eq.refl (some eb630)) (And.intro (Eq.refl (some eb631)) (And.intro (Eq.refl (some eb632)) (And.intro (Eq.refl (some eb639)) (And.intro (Eq.refl (some eb642)) (And.intro (Eq.refl (some eb645)) (And.intro (Eq.refl (some eb646)) (And.intro (Eq.refl (some eb647)) (And.intro (Eq.refl (some eb648)) (And.intro (Eq.refl (some eb654)) (And.intro (Eq.refl (some eb655)) (And.intro (Eq.refl (some eb656)) (And.intro (Eq.refl (some eb657)) (And.intro (Eq.refl (some eb666)) (And.intro (Eq.refl (some eb669)) (And.intro (Eq.refl (some eb670)) (And.intro (Eq.refl (some eb673)) (And.intro (Eq.refl (some eb677)) (And.intro (Eq.refl (some eb679)) (And.intro (Eq.refl (some eb680)) (And.intro (Eq.refl (some eb683)) (And.intro (Eq.refl (some eb684)) (And.intro (Eq.refl (some eb685)) (And.intro (Eq.refl (some eb686)) (And.intro (Eq.refl (some eb692)) (And.intro (Eq.refl (some eb695)) (And.intro (Eq.refl (some eb704)) (And.intro (Eq.refl (some eb708)) (And.intro (Eq.refl (some eb711)) (And.intro (Eq.refl (some eb715)) (And.intro (Eq.refl (some eb717)) (And.intro (Eq.refl (some eb718)) (And.intro (Eq.refl (some eb721)) (And.intro (Eq.refl (some eb722)) (And.intro (Eq.refl (some eb723)) (And.intro (Eq.refl (some eb724)) (And.intro (Eq.refl (some eb730)) (And.intro (Eq.refl (some eb731)) (And.intro (Eq.refl (some eb733)) (And.intro (Eq.refl (some eb742)) (Eq.refl (some eb746)))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  (lowerEarlyTerminalBounds06[82]? = some eb833) ∧
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
  exact And.intro (Eq.refl (some eb751)) (And.intro (Eq.refl (some eb755)) (And.intro (Eq.refl (some eb757)) (And.intro (Eq.refl (some eb761)) (And.intro (Eq.refl (some eb765)) (And.intro (Eq.refl (some eb766)) (And.intro (Eq.refl (some eb771)) (And.intro (Eq.refl (some eb772)) (And.intro (Eq.refl (some eb773)) (And.intro (Eq.refl (some eb780)) (And.intro (Eq.refl (some eb783)) (And.intro (Eq.refl (some eb788)) (And.intro (Eq.refl (some eb792)) (And.intro (Eq.refl (some eb795)) (And.intro (Eq.refl (some eb797)) (And.intro (Eq.refl (some eb798)) (And.intro (Eq.refl (some eb801)) (And.intro (Eq.refl (some eb802)) (And.intro (Eq.refl (some eb803)) (And.intro (Eq.refl (some eb808)) (And.intro (Eq.refl (some eb810)) (And.intro (Eq.refl (some eb813)) (And.intro (Eq.refl (some eb815)) (And.intro (Eq.refl (some eb816)) (And.intro (Eq.refl (some eb819)) (And.intro (Eq.refl (some eb820)) (And.intro (Eq.refl (some eb821)) (And.intro (Eq.refl (some eb827)) (And.intro (Eq.refl (some eb830)) (And.intro (Eq.refl (some eb833)) (And.intro (Eq.refl (some eb834)) (And.intro (Eq.refl (some eb838)) (And.intro (Eq.refl (some eb842)) (And.intro (Eq.refl (some eb845)) (And.intro (Eq.refl (some eb847)) (And.intro (Eq.refl (some eb851)) (And.intro (Eq.refl (some eb852)) (And.intro (Eq.refl (some eb857)) (And.intro (Eq.refl (some eb858)) (And.intro (Eq.refl (some eb859)) (And.intro (Eq.refl (some eb862)) (And.intro (Eq.refl (some eb864)) (And.intro (Eq.refl (some eb872)) (And.intro (Eq.refl (some eb876)) (And.intro (Eq.refl (some eb880)) (And.intro (Eq.refl (some eb885)) (And.intro (Eq.refl (some eb889)) (And.intro (Eq.refl (some eb890)) (And.intro (Eq.refl (some eb891)) (And.intro (Eq.refl (some eb894)) (Eq.refl (some eb896)))))))))))))))))))))))))))))))))))))))))))))))))))

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
  (lowerEarlyTerminalBounds08[123]? = some eb1174) ∧
  (lowerEarlyTerminalBounds08[125]? = some eb1176) ∧
  (lowerEarlyTerminalBounds08[127]? = some eb1178) ∧
  (lowerEarlyTerminalBounds08[129]? = some eb1180) ∧
  (lowerEarlyTerminalBounds08[131]? = some eb1182) ∧
  (lowerEarlyTerminalBounds08[133]? = some eb1184) ∧
  (lowerEarlyTerminalBounds08[135]? = some eb1186) ∧
  (lowerEarlyTerminalBounds08[137]? = some eb1188) ∧
  (lowerEarlyTerminalBounds08[139]? = some eb1190) ∧
  (lowerEarlyTerminalBounds08[141]? = some eb1192) ∧
  (lowerEarlyTerminalBounds08[143]? = some eb1194) ∧
  (lowerEarlyTerminalBounds08[145]? = some eb1196) ∧
  (lowerEarlyTerminalBounds08[147]? = some eb1198) ∧
  (lowerEarlyTerminalBounds08[149]? = some eb1200) := by
  exact And.intro (Eq.refl (some eb1056)) (And.intro (Eq.refl (some eb1060)) (And.intro (Eq.refl (some eb1061)) (And.intro (Eq.refl (some eb1062)) (And.intro (Eq.refl (some eb1063)) (And.intro (Eq.refl (some eb1064)) (And.intro (Eq.refl (some eb1071)) (And.intro (Eq.refl (some eb1077)) (And.intro (Eq.refl (some eb1082)) (And.intro (Eq.refl (some eb1086)) (And.intro (Eq.refl (some eb1087)) (And.intro (Eq.refl (some eb1092)) (And.intro (Eq.refl (some eb1094)) (And.intro (Eq.refl (some eb1095)) (And.intro (Eq.refl (some eb1098)) (And.intro (Eq.refl (some eb1099)) (And.intro (Eq.refl (some eb1100)) (And.intro (Eq.refl (some eb1104)) (And.intro (Eq.refl (some eb1105)) (And.intro (Eq.refl (some eb1106)) (And.intro (Eq.refl (some eb1107)) (And.intro (Eq.refl (some eb1108)) (And.intro (Eq.refl (some eb1116)) (And.intro (Eq.refl (some eb1121)) (And.intro (Eq.refl (some eb1122)) (And.intro (Eq.refl (some eb1123)) (And.intro (Eq.refl (some eb1124)) (And.intro (Eq.refl (some eb1125)) (And.intro (Eq.refl (some eb1127)) (And.intro (Eq.refl (some eb1131)) (And.intro (Eq.refl (some eb1135)) (And.intro (Eq.refl (some eb1136)) (And.intro (Eq.refl (some eb1141)) (And.intro (Eq.refl (some eb1142)) (And.intro (Eq.refl (some eb1143)) (And.intro (Eq.refl (some eb1144)) (And.intro (Eq.refl (some eb1146)) (And.intro (Eq.refl (some eb1148)) (And.intro (Eq.refl (some eb1157)) (And.intro (Eq.refl (some eb1160)) (And.intro (Eq.refl (some eb1164)) (And.intro (Eq.refl (some eb1169)) (And.intro (Eq.refl (some eb1174)) (And.intro (Eq.refl (some eb1176)) (And.intro (Eq.refl (some eb1178)) (And.intro (Eq.refl (some eb1180)) (And.intro (Eq.refl (some eb1182)) (And.intro (Eq.refl (some eb1184)) (And.intro (Eq.refl (some eb1186)) (And.intro (Eq.refl (some eb1188)) (And.intro (Eq.refl (some eb1190)) (And.intro (Eq.refl (some eb1192)) (And.intro (Eq.refl (some eb1194)) (And.intro (Eq.refl (some eb1196)) (And.intro (Eq.refl (some eb1198)) (Eq.refl (some eb1200))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem chunk9 (k : Nat) (hk : k < 38) :
    lowerEarlyTerminalBounds[1200+k]? = lowerEarlyTerminalBounds09[k]? := by
  unfold lowerEarlyTerminalBounds

  rw [List.getElem?_append_right (l₁ := lowerEarlyTerminalBounds01 ++ lowerEarlyTerminalBounds02 ++ lowerEarlyTerminalBounds03 ++ lowerEarlyTerminalBounds04 ++ lowerEarlyTerminalBounds05 ++ lowerEarlyTerminalBounds06 ++ lowerEarlyTerminalBounds07 ++ lowerEarlyTerminalBounds08) (by simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]; omega)]

  simp only [List.length_append, length01, length02, length03, length04, length05, length06, length07, length08]

  exact congrArg (fun j => lowerEarlyTerminalBounds09[j]?) (by omega)

private theorem selected9 :
  (lowerEarlyTerminalBounds09[1]? = some eb1202) ∧
  (lowerEarlyTerminalBounds09[3]? = some eb1204) ∧
  (lowerEarlyTerminalBounds09[5]? = some eb1206) ∧
  (lowerEarlyTerminalBounds09[7]? = some eb1208) ∧
  (lowerEarlyTerminalBounds09[9]? = some eb1210) ∧
  (lowerEarlyTerminalBounds09[11]? = some eb1212) ∧
  (lowerEarlyTerminalBounds09[13]? = some eb1214) ∧
  (lowerEarlyTerminalBounds09[15]? = some eb1216) ∧
  (lowerEarlyTerminalBounds09[17]? = some eb1218) ∧
  (lowerEarlyTerminalBounds09[19]? = some eb1220) ∧
  (lowerEarlyTerminalBounds09[21]? = some eb1222) ∧
  (lowerEarlyTerminalBounds09[23]? = some eb1224) ∧
  (lowerEarlyTerminalBounds09[25]? = some eb1226) ∧
  (lowerEarlyTerminalBounds09[27]? = some eb1228) ∧
  (lowerEarlyTerminalBounds09[29]? = some eb1230) ∧
  (lowerEarlyTerminalBounds09[31]? = some eb1232) ∧
  (lowerEarlyTerminalBounds09[33]? = some eb1234) ∧
  (lowerEarlyTerminalBounds09[35]? = some eb1236) ∧
  (lowerEarlyTerminalBounds09[37]? = some eb1238) := by
  exact And.intro (Eq.refl (some eb1202)) (And.intro (Eq.refl (some eb1204)) (And.intro (Eq.refl (some eb1206)) (And.intro (Eq.refl (some eb1208)) (And.intro (Eq.refl (some eb1210)) (And.intro (Eq.refl (some eb1212)) (And.intro (Eq.refl (some eb1214)) (And.intro (Eq.refl (some eb1216)) (And.intro (Eq.refl (some eb1218)) (And.intro (Eq.refl (some eb1220)) (And.intro (Eq.refl (some eb1222)) (And.intro (Eq.refl (some eb1224)) (And.intro (Eq.refl (some eb1226)) (And.intro (Eq.refl (some eb1228)) (And.intro (Eq.refl (some eb1230)) (And.intro (Eq.refl (some eb1232)) (And.intro (Eq.refl (some eb1234)) (And.intro (Eq.refl (some eb1236)) (Eq.refl (some eb1238)))))))))))))))))))

end LookupFast17

private theorem lookup1 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1 = eb1 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 0 (by omega)).trans LookupFast17.selected1.1

private theorem lookup110 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 110 = eb110 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 109 (by omega)).trans LookupFast17.selected1.2.1

private theorem lookup114 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 114 = eb114 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 113 (by omega)).trans LookupFast17.selected1.2.2.1

private theorem lookup115 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 115 = eb115 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 114 (by omega)).trans LookupFast17.selected1.2.2.2.1

private theorem lookup145 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 145 = eb145 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 144 (by omega)).trans LookupFast17.selected1.2.2.2.2.1

private theorem lookup146 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 146 = eb146 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 145 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.1

private theorem lookup147 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 147 = eb147 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk1 146 (by omega)).trans LookupFast17.selected1.2.2.2.2.2.2

private theorem lookup162 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 162 = eb162 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 11 (by omega)).trans LookupFast17.selected2.1

private theorem lookup164 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 164 = eb164 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 13 (by omega)).trans LookupFast17.selected2.2.1

private theorem lookup165 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 165 = eb165 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 14 (by omega)).trans LookupFast17.selected2.2.2.1

private theorem lookup170 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 170 = eb170 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 19 (by omega)).trans LookupFast17.selected2.2.2.2.1

private theorem lookup172 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 172 = eb172 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 21 (by omega)).trans LookupFast17.selected2.2.2.2.2.1

private theorem lookup173 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 173 = eb173 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 22 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.1

private theorem lookup183 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 183 = eb183 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 32 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.1

private theorem lookup186 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 186 = eb186 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 35 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.1

private theorem lookup194 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 194 = eb194 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 43 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.1

private theorem lookup195 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 195 = eb195 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 44 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.1

private theorem lookup196 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 196 = eb196 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 45 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup216 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 216 = eb216 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 65 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup218 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 218 = eb218 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 67 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup225 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 225 = eb225 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 74 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup229 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 229 = eb229 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 78 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup230 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 230 = eb230 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 79 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup242 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 242 = eb242 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 91 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup244 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 244 = eb244 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 93 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup257 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 257 = eb257 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 106 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup258 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 258 = eb258 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 107 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup259 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 259 = eb259 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 108 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup260 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 260 = eb260 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 109 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup261 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 261 = eb261 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 110 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup268 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 268 = eb268 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 117 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup272 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 272 = eb272 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 121 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup280 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 280 = eb280 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 129 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup282 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 282 = eb282 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 131 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup283 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 283 = eb283 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 132 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup286 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 286 = eb286 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 135 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup292 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 292 = eb292 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 141 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup296 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 296 = eb296 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 145 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup297 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 297 = eb297 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 146 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup298 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 298 = eb298 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 147 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup299 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 299 = eb299 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 148 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup300 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 300 = eb300 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk2 149 (by omega)).trans LookupFast17.selected2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup301 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 301 = eb301 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 0 (by omega)).trans LookupFast17.selected3.1

private theorem lookup308 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 308 = eb308 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 7 (by omega)).trans LookupFast17.selected3.2.1

private theorem lookup312 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 312 = eb312 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 11 (by omega)).trans LookupFast17.selected3.2.2.1

private theorem lookup318 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 318 = eb318 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 17 (by omega)).trans LookupFast17.selected3.2.2.2.1

private theorem lookup320 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 320 = eb320 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 19 (by omega)).trans LookupFast17.selected3.2.2.2.2.1

private theorem lookup321 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 321 = eb321 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 20 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.1

private theorem lookup324 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 324 = eb324 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 23 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.1

private theorem lookup327 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 327 = eb327 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 26 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.1

private theorem lookup329 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 329 = eb329 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 28 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.1

private theorem lookup346 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 346 = eb346 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 45 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.1

private theorem lookup348 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 348 = eb348 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 47 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup349 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 349 = eb349 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 48 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup355 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 355 = eb355 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 54 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup356 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 356 = eb356 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 55 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup357 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 357 = eb357 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 56 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup359 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 359 = eb359 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 58 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup375 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 375 = eb375 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 74 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup376 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 376 = eb376 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 75 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup380 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 380 = eb380 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 79 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup395 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 395 = eb395 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 94 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup396 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 396 = eb396 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 95 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup397 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 397 = eb397 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 96 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup398 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 398 = eb398 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 97 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup399 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 399 = eb399 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 98 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup402 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 402 = eb402 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 101 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup403 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 403 = eb403 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 102 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup404 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 404 = eb404 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 103 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup405 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 405 = eb405 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 104 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup406 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 406 = eb406 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 105 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup408 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 408 = eb408 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 107 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup411 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 411 = eb411 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 110 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup412 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 412 = eb412 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 111 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup414 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 414 = eb414 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 113 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup415 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 415 = eb415 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 114 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup416 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 416 = eb416 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 115 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup419 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 419 = eb419 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 118 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup420 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 420 = eb420 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 119 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup422 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 422 = eb422 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 121 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup424 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 424 = eb424 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 123 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup425 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 425 = eb425 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 124 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup426 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 426 = eb426 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 125 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup427 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 427 = eb427 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 126 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup431 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 431 = eb431 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 130 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup432 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 432 = eb432 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 131 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup433 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 433 = eb433 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 132 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup434 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 434 = eb434 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 133 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup435 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 435 = eb435 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 134 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup436 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 436 = eb436 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 135 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup437 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 437 = eb437 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 136 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup439 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 439 = eb439 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 138 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup440 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 440 = eb440 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 139 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup441 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 441 = eb441 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 140 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup443 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 443 = eb443 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 142 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup446 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 446 = eb446 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 145 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup447 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 447 = eb447 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 146 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup449 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 449 = eb449 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 148 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup450 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 450 = eb450 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk3 149 (by omega)).trans LookupFast17.selected3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup452 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 452 = eb452 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 1 (by omega)).trans LookupFast17.selected4.1

private theorem lookup454 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 454 = eb454 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 3 (by omega)).trans LookupFast17.selected4.2.1

private theorem lookup455 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 455 = eb455 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 4 (by omega)).trans LookupFast17.selected4.2.2.1

private theorem lookup456 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 456 = eb456 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 5 (by omega)).trans LookupFast17.selected4.2.2.2.1

private theorem lookup457 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 457 = eb457 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 6 (by omega)).trans LookupFast17.selected4.2.2.2.2.1

private theorem lookup460 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 460 = eb460 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 9 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.1

private theorem lookup461 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 461 = eb461 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 10 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.1

private theorem lookup462 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 462 = eb462 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 11 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.1

private theorem lookup463 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 463 = eb463 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 12 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.1

private theorem lookup464 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 464 = eb464 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 13 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.1

private theorem lookup466 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 466 = eb466 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 15 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup468 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 468 = eb468 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 17 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup469 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 469 = eb469 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 18 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup470 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 470 = eb470 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 19 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup471 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 471 = eb471 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 20 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup472 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 472 = eb472 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 21 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup473 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 473 = eb473 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 22 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup474 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 474 = eb474 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 23 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup475 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 475 = eb475 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 24 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup476 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 476 = eb476 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 25 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup477 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 477 = eb477 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 26 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup478 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 478 = eb478 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 27 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup479 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 479 = eb479 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 28 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup480 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 480 = eb480 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 29 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup481 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 481 = eb481 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 30 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup482 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 482 = eb482 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 31 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup483 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 483 = eb483 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 32 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup484 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 484 = eb484 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 33 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup485 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 485 = eb485 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 34 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup486 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 486 = eb486 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 35 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup487 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 487 = eb487 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 36 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup488 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 488 = eb488 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 37 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup490 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 490 = eb490 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 39 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup491 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 491 = eb491 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 40 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup494 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 494 = eb494 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 43 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup495 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 495 = eb495 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 44 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup496 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 496 = eb496 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 45 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup497 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 497 = eb497 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 46 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup498 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 498 = eb498 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 47 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup499 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 499 = eb499 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 48 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup500 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 500 = eb500 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 49 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup501 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 501 = eb501 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 50 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup502 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 502 = eb502 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 51 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup503 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 503 = eb503 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 52 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup504 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 504 = eb504 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 53 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup505 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 505 = eb505 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 54 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup506 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 506 = eb506 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 55 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup507 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 507 = eb507 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 56 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup510 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 510 = eb510 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 59 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup512 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 512 = eb512 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 61 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup513 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 513 = eb513 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 62 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup516 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 516 = eb516 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 65 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup519 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 519 = eb519 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 68 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup522 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 522 = eb522 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 71 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup523 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 523 = eb523 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 72 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup524 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 524 = eb524 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 73 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup525 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 525 = eb525 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 74 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup526 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 526 = eb526 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 75 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup527 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 527 = eb527 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 76 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup528 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 528 = eb528 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 77 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup529 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 529 = eb529 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 78 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup531 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 531 = eb531 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 80 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup532 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 532 = eb532 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 81 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup533 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 533 = eb533 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 82 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup534 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 534 = eb534 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 83 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup535 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 535 = eb535 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 84 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup536 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 536 = eb536 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 85 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup537 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 537 = eb537 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 86 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup538 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 538 = eb538 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 87 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup539 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 539 = eb539 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 88 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup540 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 540 = eb540 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 89 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup545 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 545 = eb545 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 94 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup547 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 547 = eb547 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 96 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup550 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 550 = eb550 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 99 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup553 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 553 = eb553 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 102 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup554 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 554 = eb554 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 103 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup555 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 555 = eb555 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 104 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup556 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 556 = eb556 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 105 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup557 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 557 = eb557 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 106 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup558 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 558 = eb558 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 107 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup559 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 559 = eb559 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 108 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup560 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 560 = eb560 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 109 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup564 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 564 = eb564 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 113 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup567 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 567 = eb567 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 116 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup568 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 568 = eb568 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 117 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup569 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 569 = eb569 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 118 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup570 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 570 = eb570 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 119 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup571 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 571 = eb571 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 120 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup573 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 573 = eb573 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 122 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup575 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 575 = eb575 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 124 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup576 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 576 = eb576 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 125 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup577 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 577 = eb577 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 126 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup578 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 578 = eb578 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 127 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup579 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 579 = eb579 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 128 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup581 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 581 = eb581 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 130 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup582 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 582 = eb582 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 131 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup583 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 583 = eb583 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 132 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup584 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 584 = eb584 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 133 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup585 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 585 = eb585 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 134 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup586 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 586 = eb586 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 135 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup590 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 590 = eb590 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 139 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup591 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 591 = eb591 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 140 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup592 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 592 = eb592 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 141 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup595 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 595 = eb595 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 144 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup598 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 598 = eb598 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk4 147 (by omega)).trans LookupFast17.selected4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup601 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 601 = eb601 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 0 (by omega)).trans LookupFast17.selected5.1

private theorem lookup603 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 603 = eb603 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 2 (by omega)).trans LookupFast17.selected5.2.1

private theorem lookup604 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 604 = eb604 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 3 (by omega)).trans LookupFast17.selected5.2.2.1

private theorem lookup606 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 606 = eb606 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 5 (by omega)).trans LookupFast17.selected5.2.2.2.1

private theorem lookup607 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 607 = eb607 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 6 (by omega)).trans LookupFast17.selected5.2.2.2.2.1

private theorem lookup608 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 608 = eb608 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 7 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.1

private theorem lookup609 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 609 = eb609 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 8 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.1

private theorem lookup611 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 611 = eb611 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 10 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.1

private theorem lookup612 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 612 = eb612 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 11 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.1

private theorem lookup613 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 613 = eb613 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 12 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.1

private theorem lookup620 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 620 = eb620 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 19 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup621 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 621 = eb621 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 20 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup624 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 624 = eb624 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 23 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup627 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 627 = eb627 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 26 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup630 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 630 = eb630 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 29 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup631 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 631 = eb631 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 30 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup632 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 632 = eb632 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 31 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup639 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 639 = eb639 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 38 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup642 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 642 = eb642 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 41 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup645 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 645 = eb645 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 44 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup646 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 646 = eb646 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 45 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup647 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 647 = eb647 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 46 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup648 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 648 = eb648 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 47 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup654 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 654 = eb654 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 53 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup655 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 655 = eb655 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 54 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup656 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 656 = eb656 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 55 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup657 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 657 = eb657 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 56 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup666 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 666 = eb666 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 65 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup669 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 669 = eb669 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 68 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup670 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 670 = eb670 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 69 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup673 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 673 = eb673 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 72 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup677 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 677 = eb677 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 76 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup679 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 679 = eb679 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 78 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup680 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 680 = eb680 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 79 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup683 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 683 = eb683 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 82 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup684 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 684 = eb684 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 83 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup685 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 685 = eb685 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 84 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup686 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 686 = eb686 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 85 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup692 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 692 = eb692 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 91 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup695 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 695 = eb695 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 94 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup704 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 704 = eb704 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 103 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup708 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 708 = eb708 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 107 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup711 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 711 = eb711 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 110 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup715 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 715 = eb715 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 114 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup717 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 717 = eb717 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 116 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup718 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 718 = eb718 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 117 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup721 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 721 = eb721 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 120 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup722 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 722 = eb722 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 121 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup723 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 723 = eb723 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 122 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup724 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 724 = eb724 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 123 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup730 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 730 = eb730 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 129 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup731 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 731 = eb731 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 130 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup733 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 733 = eb733 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 132 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup742 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 742 = eb742 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 141 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup746 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 746 = eb746 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk5 145 (by omega)).trans LookupFast17.selected5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup751 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 751 = eb751 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 0 (by omega)).trans LookupFast17.selected6.1

private theorem lookup755 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 755 = eb755 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 4 (by omega)).trans LookupFast17.selected6.2.1

private theorem lookup757 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 757 = eb757 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 6 (by omega)).trans LookupFast17.selected6.2.2.1

private theorem lookup761 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 761 = eb761 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 10 (by omega)).trans LookupFast17.selected6.2.2.2.1

private theorem lookup765 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 765 = eb765 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 14 (by omega)).trans LookupFast17.selected6.2.2.2.2.1

private theorem lookup766 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 766 = eb766 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 15 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.1

private theorem lookup771 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 771 = eb771 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 20 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.1

private theorem lookup772 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 772 = eb772 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 21 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.1

private theorem lookup773 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 773 = eb773 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 22 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.1

private theorem lookup780 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 780 = eb780 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 29 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.1

private theorem lookup783 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 783 = eb783 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 32 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup788 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 788 = eb788 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 37 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup792 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 792 = eb792 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 41 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup795 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 795 = eb795 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 44 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup797 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 797 = eb797 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 46 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup798 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 798 = eb798 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 47 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup801 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 801 = eb801 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 50 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup802 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 802 = eb802 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 51 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup803 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 803 = eb803 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 52 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup808 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 808 = eb808 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 57 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup810 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 810 = eb810 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 59 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup813 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 813 = eb813 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 62 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup815 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 815 = eb815 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 64 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup816 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 816 = eb816 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 65 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup819 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 819 = eb819 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 68 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup820 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 820 = eb820 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 69 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup821 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 821 = eb821 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 70 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup827 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 827 = eb827 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 76 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup830 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 830 = eb830 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 79 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup833 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 833 = eb833 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 82 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup834 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 834 = eb834 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 83 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup838 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 838 = eb838 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 87 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup842 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 842 = eb842 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 91 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup845 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 845 = eb845 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 94 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup847 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 847 = eb847 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 96 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup851 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 851 = eb851 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 100 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup852 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 852 = eb852 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 101 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup857 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 857 = eb857 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 106 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup858 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 858 = eb858 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 107 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup859 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 859 = eb859 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 108 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup862 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 862 = eb862 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 111 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup864 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 864 = eb864 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 113 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup872 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 872 = eb872 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 121 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup876 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 876 = eb876 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 125 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup880 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 880 = eb880 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 129 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup885 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 885 = eb885 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 134 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup889 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 889 = eb889 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 138 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup890 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 890 = eb890 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 139 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup891 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 891 = eb891 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 140 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup894 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 894 = eb894 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 143 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup896 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 896 = eb896 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk6 145 (by omega)).trans LookupFast17.selected6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup904 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 904 = eb904 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 3 (by omega)).trans LookupFast17.selected7.1

private theorem lookup908 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 908 = eb908 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 7 (by omega)).trans LookupFast17.selected7.2.1

private theorem lookup912 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 912 = eb912 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 11 (by omega)).trans LookupFast17.selected7.2.2.1

private theorem lookup914 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 914 = eb914 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 13 (by omega)).trans LookupFast17.selected7.2.2.2.1

private theorem lookup915 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 915 = eb915 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 14 (by omega)).trans LookupFast17.selected7.2.2.2.2.1

private theorem lookup918 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 918 = eb918 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 17 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.1

private theorem lookup923 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 923 = eb923 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 22 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.1

private theorem lookup927 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 927 = eb927 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 26 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.1

private theorem lookup928 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 928 = eb928 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 27 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.1

private theorem lookup929 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 929 = eb929 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 28 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.1

private theorem lookup930 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 930 = eb930 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 29 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup937 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 937 = eb937 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 36 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup943 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 943 = eb943 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 42 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup948 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 948 = eb948 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 47 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup952 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 952 = eb952 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 51 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup960 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 960 = eb960 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 59 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup962 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 962 = eb962 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 61 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup968 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 968 = eb968 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 67 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup972 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 972 = eb972 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 71 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup973 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 973 = eb973 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 72 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup974 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 974 = eb974 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 73 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup975 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 975 = eb975 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 74 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup976 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 976 = eb976 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 75 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup983 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 983 = eb983 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 82 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup984 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 984 = eb984 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 83 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup986 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 986 = eb986 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 85 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup994 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 994 = eb994 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 93 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup996 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 996 = eb996 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 95 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup997 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 997 = eb997 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 96 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1000 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1000 = eb1000 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 99 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1006 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1006 = eb1006 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 105 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1010 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1010 = eb1010 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 109 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1011 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1011 = eb1011 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 110 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1012 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1012 = eb1012 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 111 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1013 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1013 = eb1013 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 112 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1014 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1014 = eb1014 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 113 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1021 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1021 = eb1021 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 120 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1027 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1027 = eb1027 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 126 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1032 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1032 = eb1032 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 131 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1036 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1036 = eb1036 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 135 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1037 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1037 = eb1037 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 136 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1044 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1044 = eb1044 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 143 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1046 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1046 = eb1046 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 145 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1047 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1047 = eb1047 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 146 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1050 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1050 = eb1050 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk7 149 (by omega)).trans LookupFast17.selected7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup1056 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1056 = eb1056 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 5 (by omega)).trans LookupFast17.selected8.1

private theorem lookup1060 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1060 = eb1060 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 9 (by omega)).trans LookupFast17.selected8.2.1

private theorem lookup1061 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1061 = eb1061 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 10 (by omega)).trans LookupFast17.selected8.2.2.1

private theorem lookup1062 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1062 = eb1062 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 11 (by omega)).trans LookupFast17.selected8.2.2.2.1

private theorem lookup1063 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1063 = eb1063 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 12 (by omega)).trans LookupFast17.selected8.2.2.2.2.1

private theorem lookup1064 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1064 = eb1064 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 13 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.1

private theorem lookup1071 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1071 = eb1071 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 20 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.1

private theorem lookup1077 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1077 = eb1077 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 26 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.1

private theorem lookup1082 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1082 = eb1082 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 31 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.1

private theorem lookup1086 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1086 = eb1086 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 35 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.1

private theorem lookup1087 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1087 = eb1087 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 36 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1092 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1092 = eb1092 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 41 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1094 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1094 = eb1094 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 43 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1095 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1095 = eb1095 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 44 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1098 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1098 = eb1098 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 47 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1099 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1099 = eb1099 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 48 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1100 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1100 = eb1100 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 49 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1104 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1104 = eb1104 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 53 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1105 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1105 = eb1105 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 54 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1106 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1106 = eb1106 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 55 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1107 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1107 = eb1107 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 56 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1108 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1108 = eb1108 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 57 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1116 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1116 = eb1116 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 65 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1121 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1121 = eb1121 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 70 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1122 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1122 = eb1122 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 71 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1123 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1123 = eb1123 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 72 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1124 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1124 = eb1124 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 73 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1125 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1125 = eb1125 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 74 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1127 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1127 = eb1127 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 76 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1131 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1131 = eb1131 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 80 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1135 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1135 = eb1135 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 84 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1136 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1136 = eb1136 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 85 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1141 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1141 = eb1141 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 90 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1142 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1142 = eb1142 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 91 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1143 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1143 = eb1143 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 92 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1144 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1144 = eb1144 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 93 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1146 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1146 = eb1146 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 95 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1148 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1148 = eb1148 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 97 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1157 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1157 = eb1157 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 106 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1160 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1160 = eb1160 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 109 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1164 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1164 = eb1164 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 113 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1169 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1169 = eb1169 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 118 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1174 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1174 = eb1174 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 123 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1176 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1176 = eb1176 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 125 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1178 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1178 = eb1178 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 127 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1180 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1180 = eb1180 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 129 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1182 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1182 = eb1182 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 131 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1184 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1184 = eb1184 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 133 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1186 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1186 = eb1186 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 135 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1188 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1188 = eb1188 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 137 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1190 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1190 = eb1190 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 139 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1192 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1192 = eb1192 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 141 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1194 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1194 = eb1194 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 143 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1196 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1196 = eb1196 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 145 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1198 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1198 = eb1198 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 147 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1200 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1200 = eb1200 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk8 149 (by omega)).trans LookupFast17.selected8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem lookup1202 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1202 = eb1202 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 1 (by omega)).trans LookupFast17.selected9.1

private theorem lookup1204 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1204 = eb1204 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 3 (by omega)).trans LookupFast17.selected9.2.1

private theorem lookup1206 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1206 = eb1206 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 5 (by omega)).trans LookupFast17.selected9.2.2.1

private theorem lookup1208 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1208 = eb1208 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 7 (by omega)).trans LookupFast17.selected9.2.2.2.1

private theorem lookup1210 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1210 = eb1210 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 9 (by omega)).trans LookupFast17.selected9.2.2.2.2.1

private theorem lookup1212 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1212 = eb1212 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 11 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.1

private theorem lookup1214 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1214 = eb1214 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 13 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.1

private theorem lookup1216 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1216 = eb1216 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 15 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.1

private theorem lookup1218 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1218 = eb1218 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 17 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.1

private theorem lookup1220 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1220 = eb1220 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 19 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.1

private theorem lookup1222 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1222 = eb1222 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 21 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1224 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1224 = eb1224 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 23 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1226 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1226 = eb1226 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 25 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1228 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1228 = eb1228 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 27 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1230 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1230 = eb1230 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 29 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1232 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1232 = eb1232 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 31 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1234 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1234 = eb1234 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 33 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1236 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1236 = eb1236 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 35 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem lookup1238 : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 1238 = eb1238 := by
  apply LookupFast17.of_local
  exact (LookupFast17.chunk9 37 (by omega)).trans LookupFast17.selected9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem endpointNonneg1 : 0 ≤ certFieldLower (⟨(5/22),(1/22),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg2 : 0 ≤ certFieldLower (⟨2,-1,0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg3 : 0 ≤ certFieldLower (⟨(39/134),0,0,(1/402)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg4 : 0 ≤ certFieldLower (⟨(15/34),0,0,(-1/34)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg5 : 0 ≤ certFieldLower (⟨(-1/2),0,0,(1/6)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg6 : 0 ≤ certFieldLower (⟨(-1/10),0,0,(1/10)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg7 : 0 ≤ certFieldLower (⟨(63/170),0,0,(-1/510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg8 : 0 ≤ certFieldLower (⟨(9/10),0,0,(-1/10)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg9 : 0 ≤ certFieldLower (⟨(3539/9250),0,0,(1/9250)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg10 : 0 ≤ certFieldLower (⟨(105/262),0,0,(-1/262)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg11 : 0 ≤ certFieldLower (⟨(251/670),0,0,(1/670)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg12 : 0 ≤ certFieldLower (⟨(31/82),0,0,(1/574)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg13 : 0 ≤ certFieldLower (⟨(83/202),0,0,(-1/202)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg14 : 0 ≤ certFieldLower (⟨(3035/7846),0,0,(-1/7846)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg15 : 0 ≤ certFieldLower (⟨(31/94),0,0,(1/94)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg16 : 0 ≤ certFieldLower (⟨(1341/3526),0,0,(-1/3526)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg17 : 0 ≤ certFieldLower (⟨(227/590),0,0,(1/1770)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg18 : 0 ≤ certFieldLower (⟨(19899/51358),0,0,(-1/51358)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg19 : 0 ≤ certFieldLower (⟨(353/914),(1/2742),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg20 : 0 ≤ certFieldLower (⟨(1364/3517),(-1/3517),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg21 : 0 ≤ certFieldLower (⟨(1311/3370),0,0,(-1/3370)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg22 : 0 ≤ certFieldLower (⟨(579/1510),0,0,(1/1510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg23 : 0 ≤ certFieldLower (⟨(167/430),0,0,(-1/3010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg24 : 0 ≤ certFieldLower (⟨(553/1429),(1/1429),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg25 : 0 ≤ certFieldLower (⟨(177/454),(-1/454),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg26 : 0 ≤ certFieldLower (⟨(2589/6674),(1/20022),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg27 : 0 ≤ certFieldLower (⟨(523/1354),0,0,(1/1354)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg28 : 0 ≤ certFieldLower (⟨(1/2),0,0,(-1/42)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg29 : 0 ≤ certFieldLower (⟨(1311/3370),0,0,(1/3370)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg30 : 0 ≤ certFieldLower (⟨(34601/88618),0,0,(-1/88618)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg31 : 0 ≤ certFieldLower (⟨(1932/4957),(1/4957),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg32 : 0 ≤ certFieldLower (⟨(779/1994),(-1/5982),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg33 : 0 ≤ certFieldLower (⟨(2141/5470),0,0,(-1/5470)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg34 : 0 ≤ certFieldLower (⟨(167/430),0,0,(1/3010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg35 : 0 ≤ certFieldLower (⟨(653/1670),0,0,(-1/5010)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg36 : 0 ≤ certFieldLower (⟨(13260/33937),(1/33937),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg37 : 0 ≤ certFieldLower (⟨(278/709),(-1/709),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg38 : 0 ≤ certFieldLower (⟨(1803/4622),0,0,(-1/13866)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg39 : 0 ≤ certFieldLower (⟨(32/83),(-1/249),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg40 : 0 ≤ certFieldLower (⟨(1413/3718),(-1/3718),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg41 : 0 ≤ certFieldLower (⟨(35/94),(1/94),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg42 : 0 ≤ certFieldLower (⟨(4519/12598),(-1/12598),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg43 : 0 ≤ certFieldLower (⟨(42/143),(1/429),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg44 : 0 ≤ certFieldLower (⟨(271/1006),(-1/1006),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg45 : 0 ≤ certFieldLower (⟨(93/262),(1/262),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg46 : 0 ≤ certFieldLower (⟨(1859/5158),0,0,(1/5158)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg47 : 0 ≤ certFieldLower (⟨(1991/5521),(1/5521),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg48 : 0 ≤ certFieldLower (⟨(61/169),(1/169),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg49 : 0 ≤ certFieldLower (⟨(1089/2950),0,0,(1/2950)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg50 : 0 ≤ certFieldLower (⟨(29/74),0,0,(-1/222)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg51 : 0 ≤ certFieldLower (⟨(3/10),0,0,(1/70)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg52 : 0 ≤ certFieldLower (⟨(1161/3142),(1/3142),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg53 : 0 ≤ certFieldLower (⟨(66/179),(-1/537),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg54 : 0 ≤ certFieldLower (⟨(2615/7138),0,0,(-1/7138)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg55 : 0 ≤ certFieldLower (⟨(2747/7501),(-1/7501),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg56 : 0 ≤ certFieldLower (⟨(251/670),0,0,(-1/670)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg57 : 0 ≤ certFieldLower (⟨(247/649),(1/649),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg58 : 0 ≤ certFieldLower (⟨(3734/9757),(1/9757),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg59 : 0 ≤ certFieldLower (⟨(2463/6350),0,0,(1/19050)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg60 : 0 ≤ certFieldLower (⟨(3230/8353),(-1/8353),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg61 : 0 ≤ certFieldLower (⟨(1929/4946),(-1/14838),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg62 : 0 ≤ certFieldLower (⟨(483/1318),(1/1318),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg63 : 0 ≤ certFieldLower (⟨(7081/19270),0,0,(1/19270)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg64 : 0 ≤ certFieldLower (⟨(457/1258),0,0,(1/1258)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg65 : 0 ≤ certFieldLower (⟨(7480/20353),(1/20353),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg66 : 0 ≤ certFieldLower (⟨(15/37),(-1/37),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg67 : 0 ≤ certFieldLower (⟨(11835/32926),0,0,(1/32926)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg68 : 0 ≤ certFieldLower (⟨(457/1258),0,0,(-1/1258)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg69 : 0 ≤ certFieldLower (⟨(797/2221),(1/2221),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg70 : 0 ≤ certFieldLower (⟨(667/1846),(-1/1846),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg71 : 0 ≤ certFieldLower (⟨(723/2026),0,0,(1/2026)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg72 : 0 ≤ certFieldLower (⟨(665/1858),0,0,(1/1858)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg73 : 0 ≤ certFieldLower (⟨(411/1126),0,0,(-1/1126)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg74 : 0 ≤ certFieldLower (⟨(1557/4318),0,0,(-1/30226)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg75 : 0 ≤ certFieldLower (⟨(11574/32101),(-1/32101),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg76 : 0 ≤ certFieldLower (⟨(383/1033),(-1/1033),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg77 : 0 ≤ certFieldLower (⟨(411/1126),0,0,(1/1126)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg78 : 0 ≤ certFieldLower (⟨(31/82),0,0,(-1/574)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg79 : 0 ≤ certFieldLower (⟨(6361/17218),0,0,(-1/17218)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg80 : 0 ≤ certFieldLower (⟨(6760/18301),(-1/18301),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg81 : 0 ≤ certFieldLower (⟨(12510/34801),(1/34801),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg82 : 0 ≤ certFieldLower (⟨(2587/6806),0,0,(1/20418)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg83 : 0 ≤ certFieldLower (⟨(579/1510),0,0,(-1/1510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg84 : 0 ≤ certFieldLower (⟨(446/1177),(1/1177),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg85 : 0 ≤ certFieldLower (⟨(651/1702),(-1/1702),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg86 : 0 ≤ certFieldLower (⟨(63/170),0,0,(1/510)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg87 : 0 ≤ certFieldLower (⟨(3247/8507),(-1/25521),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg88 : 0 ≤ certFieldLower (⟨(17703/45778),0,0,(1/45778)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg89 : 0 ≤ certFieldLower (⟨(21015/54241),(-1/54241),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg90 : 0 ≤ certFieldLower (⟨(3079/8066),0,0,(-1/24198)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg91 : 0 ≤ certFieldLower (⟨(227/590),0,0,(-1/1770)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg92 : 0 ≤ certFieldLower (⟨(2755/7247),(1/21741),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg93 : 0 ≤ certFieldLower (⟨(18819/48661),(1/48661),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg94 : 0 ≤ certFieldLower (⟨(33653/86281),(1/86281),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg95 : 0 ≤ certFieldLower (⟨(5033/13742),0,0,(1/41226)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg96 : 0 ≤ certFieldLower (⟨(167/454),0,0,(-1/3178)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg97 : 0 ≤ certFieldLower (⟨(856/2341),(1/2341),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg98 : 0 ≤ certFieldLower (⟨(1301/3541),(-1/3541),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg99 : 0 ≤ certFieldLower (⟨(109/302),0,0,(1/906)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg100 : 0 ≤ certFieldLower (⟨(6101/16622),0,0,(-1/49866)⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem endpointNonneg101 : 0 ≤ certFieldLower (⟨(6431/17522),(-1/52566),0,0⟩ : CertField) := by
  norm_num [certFieldLower, certDirectedTerm, certSqrt3Lower, certSqrt3Upper, certSqrt7Lower, certSqrt7Upper, certSqrt21Lower, certSqrt21Upper]

private theorem threshold1 : certThresholdDataValid eb1.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg2⟩

private theorem indexOk1 : 0 < 1 ∧ 1 ≤ 1238 := by norm_num

private theorem threshold110 : certThresholdDataValid eb110.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg4⟩

private theorem indexOk110 : 0 < 110 ∧ 110 ≤ 1238 := by norm_num

private theorem threshold114 : certThresholdDataValid eb114.threshold := by
  exact ⟨endpointNonneg3, endpointNonneg4⟩

private theorem indexOk114 : 0 < 114 ∧ 114 ≤ 1238 := by norm_num

private theorem threshold115 : certThresholdDataValid eb115.threshold := by
  exact ⟨endpointNonneg5, endpointNonneg4⟩

private theorem indexOk115 : 0 < 115 ∧ 115 ≤ 1238 := by norm_num

private theorem threshold145 : certThresholdDataValid eb145.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk145 : 0 < 145 ∧ 145 ≤ 1238 := by norm_num

private theorem threshold146 : certThresholdDataValid eb146.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk146 : 0 < 146 ∧ 146 ≤ 1238 := by norm_num

private theorem threshold147 : certThresholdDataValid eb147.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg8⟩

private theorem indexOk147 : 0 < 147 ∧ 147 ≤ 1238 := by norm_num

private theorem threshold162 : certThresholdDataValid eb162.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg10⟩

private theorem indexOk162 : 0 < 162 ∧ 162 ≤ 1238 := by norm_num

private theorem threshold164 : certThresholdDataValid eb164.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg10⟩

private theorem indexOk164 : 0 < 164 ∧ 164 ≤ 1238 := by norm_num

private theorem threshold165 : certThresholdDataValid eb165.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk165 : 0 < 165 ∧ 165 ≤ 1238 := by norm_num

private theorem threshold170 : certThresholdDataValid eb170.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk170 : 0 < 170 ∧ 170 ≤ 1238 := by norm_num

private theorem threshold172 : certThresholdDataValid eb172.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk172 : 0 < 172 ∧ 172 ≤ 1238 := by norm_num

private theorem threshold173 : certThresholdDataValid eb173.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk173 : 0 < 173 ∧ 173 ≤ 1238 := by norm_num

private theorem threshold183 : certThresholdDataValid eb183.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg10⟩

private theorem indexOk183 : 0 < 183 ∧ 183 ≤ 1238 := by norm_num

private theorem threshold186 : certThresholdDataValid eb186.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk186 : 0 < 186 ∧ 186 ≤ 1238 := by norm_num

private theorem threshold194 : certThresholdDataValid eb194.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk194 : 0 < 194 ∧ 194 ≤ 1238 := by norm_num

private theorem threshold195 : certThresholdDataValid eb195.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk195 : 0 < 195 ∧ 195 ≤ 1238 := by norm_num

private theorem threshold196 : certThresholdDataValid eb196.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk196 : 0 < 196 ∧ 196 ≤ 1238 := by norm_num

private theorem threshold216 : certThresholdDataValid eb216.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk216 : 0 < 216 ∧ 216 ≤ 1238 := by norm_num

private theorem threshold218 : certThresholdDataValid eb218.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg10⟩

private theorem indexOk218 : 0 < 218 ∧ 218 ≤ 1238 := by norm_num

private theorem threshold225 : certThresholdDataValid eb225.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg10⟩

private theorem indexOk225 : 0 < 225 ∧ 225 ≤ 1238 := by norm_num

private theorem threshold229 : certThresholdDataValid eb229.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg10⟩

private theorem indexOk229 : 0 < 229 ∧ 229 ≤ 1238 := by norm_num

private theorem threshold230 : certThresholdDataValid eb230.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk230 : 0 < 230 ∧ 230 ≤ 1238 := by norm_num

private theorem threshold242 : certThresholdDataValid eb242.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk242 : 0 < 242 ∧ 242 ≤ 1238 := by norm_num

private theorem threshold244 : certThresholdDataValid eb244.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk244 : 0 < 244 ∧ 244 ≤ 1238 := by norm_num

private theorem threshold257 : certThresholdDataValid eb257.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk257 : 0 < 257 ∧ 257 ≤ 1238 := by norm_num

private theorem threshold258 : certThresholdDataValid eb258.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg18⟩

private theorem indexOk258 : 0 < 258 ∧ 258 ≤ 1238 := by norm_num

private theorem threshold259 : certThresholdDataValid eb259.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg20⟩

private theorem indexOk259 : 0 < 259 ∧ 259 ≤ 1238 := by norm_num

private theorem threshold260 : certThresholdDataValid eb260.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg21⟩

private theorem indexOk260 : 0 < 260 ∧ 260 ≤ 1238 := by norm_num

private theorem threshold261 : certThresholdDataValid eb261.threshold := by
  exact ⟨endpointNonneg22, endpointNonneg23⟩

private theorem indexOk261 : 0 < 261 ∧ 261 ≤ 1238 := by norm_num

private theorem threshold268 : certThresholdDataValid eb268.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg18⟩

private theorem indexOk268 : 0 < 268 ∧ 268 ≤ 1238 := by norm_num

private theorem threshold272 : certThresholdDataValid eb272.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg25⟩

private theorem indexOk272 : 0 < 272 ∧ 272 ≤ 1238 := by norm_num

private theorem threshold280 : certThresholdDataValid eb280.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk280 : 0 < 280 ∧ 280 ≤ 1238 := by norm_num

private theorem threshold282 : certThresholdDataValid eb282.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk282 : 0 < 282 ∧ 282 ≤ 1238 := by norm_num

private theorem threshold283 : certThresholdDataValid eb283.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk283 : 0 < 283 ∧ 283 ≤ 1238 := by norm_num

private theorem threshold286 : certThresholdDataValid eb286.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg25⟩

private theorem indexOk286 : 0 < 286 ∧ 286 ≤ 1238 := by norm_num

private theorem threshold292 : certThresholdDataValid eb292.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg25⟩

private theorem indexOk292 : 0 < 292 ∧ 292 ≤ 1238 := by norm_num

private theorem threshold296 : certThresholdDataValid eb296.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk296 : 0 < 296 ∧ 296 ≤ 1238 := by norm_num

private theorem threshold297 : certThresholdDataValid eb297.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk297 : 0 < 297 ∧ 297 ≤ 1238 := by norm_num

private theorem threshold298 : certThresholdDataValid eb298.threshold := by
  exact ⟨endpointNonneg29, endpointNonneg30⟩

private theorem indexOk298 : 0 < 298 ∧ 298 ≤ 1238 := by norm_num

private theorem threshold299 : certThresholdDataValid eb299.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg32⟩

private theorem indexOk299 : 0 < 299 ∧ 299 ≤ 1238 := by norm_num

private theorem threshold300 : certThresholdDataValid eb300.threshold := by
  exact ⟨endpointNonneg29, endpointNonneg33⟩

private theorem indexOk300 : 0 < 300 ∧ 300 ≤ 1238 := by norm_num

private theorem threshold301 : certThresholdDataValid eb301.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk301 : 0 < 301 ∧ 301 ≤ 1238 := by norm_num

private theorem threshold308 : certThresholdDataValid eb308.threshold := by
  exact ⟨endpointNonneg29, endpointNonneg30⟩

private theorem indexOk308 : 0 < 308 ∧ 308 ≤ 1238 := by norm_num

private theorem threshold312 : certThresholdDataValid eb312.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem indexOk312 : 0 < 312 ∧ 312 ≤ 1238 := by norm_num

private theorem threshold318 : certThresholdDataValid eb318.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk318 : 0 < 318 ∧ 318 ≤ 1238 := by norm_num

private theorem threshold320 : certThresholdDataValid eb320.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk320 : 0 < 320 ∧ 320 ≤ 1238 := by norm_num

private theorem threshold321 : certThresholdDataValid eb321.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk321 : 0 < 321 ∧ 321 ≤ 1238 := by norm_num

private theorem threshold324 : certThresholdDataValid eb324.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk324 : 0 < 324 ∧ 324 ≤ 1238 := by norm_num

private theorem threshold327 : certThresholdDataValid eb327.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk327 : 0 < 327 ∧ 327 ≤ 1238 := by norm_num

private theorem threshold329 : certThresholdDataValid eb329.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk329 : 0 < 329 ∧ 329 ≤ 1238 := by norm_num

private theorem threshold346 : certThresholdDataValid eb346.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk346 : 0 < 346 ∧ 346 ≤ 1238 := by norm_num

private theorem threshold348 : certThresholdDataValid eb348.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk348 : 0 < 348 ∧ 348 ≤ 1238 := by norm_num

private theorem threshold349 : certThresholdDataValid eb349.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk349 : 0 < 349 ∧ 349 ≤ 1238 := by norm_num

private theorem threshold355 : certThresholdDataValid eb355.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk355 : 0 < 355 ∧ 355 ≤ 1238 := by norm_num

private theorem threshold356 : certThresholdDataValid eb356.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk356 : 0 < 356 ∧ 356 ≤ 1238 := by norm_num

private theorem threshold357 : certThresholdDataValid eb357.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg24⟩

private theorem indexOk357 : 0 < 357 ∧ 357 ≤ 1238 := by norm_num

private theorem threshold359 : certThresholdDataValid eb359.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk359 : 0 < 359 ∧ 359 ≤ 1238 := by norm_num

private theorem threshold375 : certThresholdDataValid eb375.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk375 : 0 < 375 ∧ 375 ≤ 1238 := by norm_num

private theorem threshold376 : certThresholdDataValid eb376.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg37⟩

private theorem indexOk376 : 0 < 376 ∧ 376 ≤ 1238 := by norm_num

private theorem threshold380 : certThresholdDataValid eb380.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk380 : 0 < 380 ∧ 380 ≤ 1238 := by norm_num

private theorem threshold395 : certThresholdDataValid eb395.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg41⟩

private theorem indexOk395 : 0 < 395 ∧ 395 ≤ 1238 := by norm_num

private theorem threshold396 : certThresholdDataValid eb396.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg42⟩

private theorem indexOk396 : 0 < 396 ∧ 396 ≤ 1238 := by norm_num

private theorem threshold397 : certThresholdDataValid eb397.threshold := by
  exact ⟨endpointNonneg1, endpointNonneg42⟩

private theorem indexOk397 : 0 < 397 ∧ 397 ≤ 1238 := by norm_num

private theorem threshold398 : certThresholdDataValid eb398.threshold := by
  exact ⟨endpointNonneg43, endpointNonneg42⟩

private theorem indexOk398 : 0 < 398 ∧ 398 ≤ 1238 := by norm_num

private theorem threshold399 : certThresholdDataValid eb399.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg45⟩

private theorem indexOk399 : 0 < 399 ∧ 399 ≤ 1238 := by norm_num

private theorem threshold402 : certThresholdDataValid eb402.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg45⟩

private theorem indexOk402 : 0 < 402 ∧ 402 ≤ 1238 := by norm_num

private theorem threshold403 : certThresholdDataValid eb403.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk403 : 0 < 403 ∧ 403 ≤ 1238 := by norm_num

private theorem threshold404 : certThresholdDataValid eb404.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk404 : 0 < 404 ∧ 404 ≤ 1238 := by norm_num

private theorem threshold405 : certThresholdDataValid eb405.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk405 : 0 < 405 ∧ 405 ≤ 1238 := by norm_num

private theorem threshold406 : certThresholdDataValid eb406.threshold := by
  exact ⟨endpointNonneg44, endpointNonneg47⟩

private theorem indexOk406 : 0 < 406 ∧ 406 ≤ 1238 := by norm_num

private theorem threshold408 : certThresholdDataValid eb408.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg42⟩

private theorem indexOk408 : 0 < 408 ∧ 408 ≤ 1238 := by norm_num

private theorem threshold411 : certThresholdDataValid eb411.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg48⟩

private theorem indexOk411 : 0 < 411 ∧ 411 ≤ 1238 := by norm_num

private theorem threshold412 : certThresholdDataValid eb412.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk412 : 0 < 412 ∧ 412 ≤ 1238 := by norm_num

private theorem threshold414 : certThresholdDataValid eb414.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk414 : 0 < 414 ∧ 414 ≤ 1238 := by norm_num

private theorem threshold415 : certThresholdDataValid eb415.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk415 : 0 < 415 ∧ 415 ≤ 1238 := by norm_num

private theorem threshold416 : certThresholdDataValid eb416.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg48⟩

private theorem indexOk416 : 0 < 416 ∧ 416 ≤ 1238 := by norm_num

private theorem threshold419 : certThresholdDataValid eb419.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk419 : 0 < 419 ∧ 419 ≤ 1238 := by norm_num

private theorem threshold420 : certThresholdDataValid eb420.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg52⟩

private theorem indexOk420 : 0 < 420 ∧ 420 ≤ 1238 := by norm_num

private theorem threshold422 : certThresholdDataValid eb422.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk422 : 0 < 422 ∧ 422 ≤ 1238 := by norm_num

private theorem threshold424 : certThresholdDataValid eb424.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk424 : 0 < 424 ∧ 424 ≤ 1238 := by norm_num

private theorem threshold425 : certThresholdDataValid eb425.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk425 : 0 < 425 ∧ 425 ≤ 1238 := by norm_num

private theorem threshold426 : certThresholdDataValid eb426.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk426 : 0 < 426 ∧ 426 ≤ 1238 := by norm_num

private theorem threshold427 : certThresholdDataValid eb427.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk427 : 0 < 427 ∧ 427 ≤ 1238 := by norm_num

private theorem threshold431 : certThresholdDataValid eb431.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk431 : 0 < 431 ∧ 431 ≤ 1238 := by norm_num

private theorem threshold432 : certThresholdDataValid eb432.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk432 : 0 < 432 ∧ 432 ≤ 1238 := by norm_num

private theorem threshold433 : certThresholdDataValid eb433.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk433 : 0 < 433 ∧ 433 ≤ 1238 := by norm_num

private theorem threshold434 : certThresholdDataValid eb434.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk434 : 0 < 434 ∧ 434 ≤ 1238 := by norm_num

private theorem threshold435 : certThresholdDataValid eb435.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk435 : 0 < 435 ∧ 435 ≤ 1238 := by norm_num

private theorem threshold436 : certThresholdDataValid eb436.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk436 : 0 < 436 ∧ 436 ≤ 1238 := by norm_num

private theorem threshold437 : certThresholdDataValid eb437.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg53⟩

private theorem indexOk437 : 0 < 437 ∧ 437 ≤ 1238 := by norm_num

private theorem threshold439 : certThresholdDataValid eb439.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg53⟩

private theorem indexOk439 : 0 < 439 ∧ 439 ≤ 1238 := by norm_num

private theorem threshold440 : certThresholdDataValid eb440.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg55⟩

private theorem indexOk440 : 0 < 440 ∧ 440 ≤ 1238 := by norm_num

private theorem threshold441 : certThresholdDataValid eb441.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg42⟩

private theorem indexOk441 : 0 < 441 ∧ 441 ≤ 1238 := by norm_num

private theorem threshold443 : certThresholdDataValid eb443.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk443 : 0 < 443 ∧ 443 ≤ 1238 := by norm_num

private theorem threshold446 : certThresholdDataValid eb446.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk446 : 0 < 446 ∧ 446 ≤ 1238 := by norm_num

private theorem threshold447 : certThresholdDataValid eb447.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg56⟩

private theorem indexOk447 : 0 < 447 ∧ 447 ≤ 1238 := by norm_num

private theorem threshold449 : certThresholdDataValid eb449.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk449 : 0 < 449 ∧ 449 ≤ 1238 := by norm_num

private theorem threshold450 : certThresholdDataValid eb450.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk450 : 0 < 450 ∧ 450 ≤ 1238 := by norm_num

private theorem threshold452 : certThresholdDataValid eb452.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk452 : 0 < 452 ∧ 452 ≤ 1238 := by norm_num

private theorem threshold454 : certThresholdDataValid eb454.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk454 : 0 < 454 ∧ 454 ≤ 1238 := by norm_num

private theorem threshold455 : certThresholdDataValid eb455.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk455 : 0 < 455 ∧ 455 ≤ 1238 := by norm_num

private theorem threshold456 : certThresholdDataValid eb456.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk456 : 0 < 456 ∧ 456 ≤ 1238 := by norm_num

private theorem threshold457 : certThresholdDataValid eb457.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg48⟩

private theorem indexOk457 : 0 < 457 ∧ 457 ≤ 1238 := by norm_num

private theorem threshold460 : certThresholdDataValid eb460.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg48⟩

private theorem indexOk460 : 0 < 460 ∧ 460 ≤ 1238 := by norm_num

private theorem threshold461 : certThresholdDataValid eb461.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk461 : 0 < 461 ∧ 461 ≤ 1238 := by norm_num

private theorem threshold462 : certThresholdDataValid eb462.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk462 : 0 < 462 ∧ 462 ≤ 1238 := by norm_num

private theorem threshold463 : certThresholdDataValid eb463.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk463 : 0 < 463 ∧ 463 ≤ 1238 := by norm_num

private theorem threshold464 : certThresholdDataValid eb464.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg52⟩

private theorem indexOk464 : 0 < 464 ∧ 464 ≤ 1238 := by norm_num

private theorem threshold466 : certThresholdDataValid eb466.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg39⟩

private theorem indexOk466 : 0 < 466 ∧ 466 ≤ 1238 := by norm_num

private theorem threshold468 : certThresholdDataValid eb468.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg39⟩

private theorem indexOk468 : 0 < 468 ∧ 468 ≤ 1238 := by norm_num

private theorem threshold469 : certThresholdDataValid eb469.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk469 : 0 < 469 ∧ 469 ≤ 1238 := by norm_num

private theorem threshold470 : certThresholdDataValid eb470.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg40⟩

private theorem indexOk470 : 0 < 470 ∧ 470 ≤ 1238 := by norm_num

private theorem threshold471 : certThresholdDataValid eb471.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg39⟩

private theorem indexOk471 : 0 < 471 ∧ 471 ≤ 1238 := by norm_num

private theorem threshold472 : certThresholdDataValid eb472.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg39⟩

private theorem indexOk472 : 0 < 472 ∧ 472 ≤ 1238 := by norm_num

private theorem threshold473 : certThresholdDataValid eb473.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg40⟩

private theorem indexOk473 : 0 < 473 ∧ 473 ≤ 1238 := by norm_num

private theorem threshold474 : certThresholdDataValid eb474.threshold := by
  exact ⟨endpointNonneg52, endpointNonneg39⟩

private theorem indexOk474 : 0 < 474 ∧ 474 ≤ 1238 := by norm_num

private theorem threshold475 : certThresholdDataValid eb475.threshold := by
  exact ⟨endpointNonneg52, endpointNonneg39⟩

private theorem indexOk475 : 0 < 475 ∧ 475 ≤ 1238 := by norm_num

private theorem threshold476 : certThresholdDataValid eb476.threshold := by
  exact ⟨endpointNonneg52, endpointNonneg40⟩

private theorem indexOk476 : 0 < 476 ∧ 476 ≤ 1238 := by norm_num

private theorem threshold477 : certThresholdDataValid eb477.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg57⟩

private theorem indexOk477 : 0 < 477 ∧ 477 ≤ 1238 := by norm_num

private theorem threshold478 : certThresholdDataValid eb478.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg57⟩

private theorem indexOk478 : 0 < 478 ∧ 478 ≤ 1238 := by norm_num

private theorem threshold479 : certThresholdDataValid eb479.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg57⟩

private theorem indexOk479 : 0 < 479 ∧ 479 ≤ 1238 := by norm_num

private theorem threshold480 : certThresholdDataValid eb480.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg57⟩

private theorem indexOk480 : 0 < 480 ∧ 480 ≤ 1238 := by norm_num

private theorem threshold481 : certThresholdDataValid eb481.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg57⟩

private theorem indexOk481 : 0 < 481 ∧ 481 ≤ 1238 := by norm_num

private theorem threshold482 : certThresholdDataValid eb482.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg57⟩

private theorem indexOk482 : 0 < 482 ∧ 482 ≤ 1238 := by norm_num

private theorem threshold483 : certThresholdDataValid eb483.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg58⟩

private theorem indexOk483 : 0 < 483 ∧ 483 ≤ 1238 := by norm_num

private theorem threshold484 : certThresholdDataValid eb484.threshold := by
  exact ⟨endpointNonneg53, endpointNonneg58⟩

private theorem indexOk484 : 0 < 484 ∧ 484 ≤ 1238 := by norm_num

private theorem threshold485 : certThresholdDataValid eb485.threshold := by
  exact ⟨endpointNonneg55, endpointNonneg58⟩

private theorem indexOk485 : 0 < 485 ∧ 485 ≤ 1238 := by norm_num

private theorem threshold486 : certThresholdDataValid eb486.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg13⟩

private theorem indexOk486 : 0 < 486 ∧ 486 ≤ 1238 := by norm_num

private theorem threshold487 : certThresholdDataValid eb487.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg13⟩

private theorem indexOk487 : 0 < 487 ∧ 487 ≤ 1238 := by norm_num

private theorem threshold488 : certThresholdDataValid eb488.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk488 : 0 < 488 ∧ 488 ≤ 1238 := by norm_num

private theorem threshold490 : certThresholdDataValid eb490.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk490 : 0 < 490 ∧ 490 ≤ 1238 := by norm_num

private theorem threshold491 : certThresholdDataValid eb491.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg24⟩

private theorem indexOk491 : 0 < 491 ∧ 491 ≤ 1238 := by norm_num

private theorem threshold494 : certThresholdDataValid eb494.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg26⟩

private theorem indexOk494 : 0 < 494 ∧ 494 ≤ 1238 := by norm_num

private theorem threshold495 : certThresholdDataValid eb495.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg13⟩

private theorem indexOk495 : 0 < 495 ∧ 495 ≤ 1238 := by norm_num

private theorem threshold496 : certThresholdDataValid eb496.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg26⟩

private theorem indexOk496 : 0 < 496 ∧ 496 ≤ 1238 := by norm_num

private theorem threshold497 : certThresholdDataValid eb497.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg26⟩

private theorem indexOk497 : 0 < 497 ∧ 497 ≤ 1238 := by norm_num

private theorem threshold498 : certThresholdDataValid eb498.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk498 : 0 < 498 ∧ 498 ≤ 1238 := by norm_num

private theorem threshold499 : certThresholdDataValid eb499.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk499 : 0 < 499 ∧ 499 ≤ 1238 := by norm_num

private theorem threshold500 : certThresholdDataValid eb500.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg60⟩

private theorem indexOk500 : 0 < 500 ∧ 500 ≤ 1238 := by norm_num

private theorem threshold501 : certThresholdDataValid eb501.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk501 : 0 < 501 ∧ 501 ≤ 1238 := by norm_num

private theorem threshold502 : certThresholdDataValid eb502.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk502 : 0 < 502 ∧ 502 ≤ 1238 := by norm_num

private theorem threshold503 : certThresholdDataValid eb503.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg60⟩

private theorem indexOk503 : 0 < 503 ∧ 503 ≤ 1238 := by norm_num

private theorem threshold504 : certThresholdDataValid eb504.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg25⟩

private theorem indexOk504 : 0 < 504 ∧ 504 ≤ 1238 := by norm_num

private theorem threshold505 : certThresholdDataValid eb505.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg25⟩

private theorem indexOk505 : 0 < 505 ∧ 505 ≤ 1238 := by norm_num

private theorem threshold506 : certThresholdDataValid eb506.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg60⟩

private theorem indexOk506 : 0 < 506 ∧ 506 ≤ 1238 := by norm_num

private theorem threshold507 : certThresholdDataValid eb507.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk507 : 0 < 507 ∧ 507 ≤ 1238 := by norm_num

private theorem threshold510 : certThresholdDataValid eb510.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk510 : 0 < 510 ∧ 510 ≤ 1238 := by norm_num

private theorem threshold512 : certThresholdDataValid eb512.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk512 : 0 < 512 ∧ 512 ≤ 1238 := by norm_num

private theorem threshold513 : certThresholdDataValid eb513.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk513 : 0 < 513 ∧ 513 ≤ 1238 := by norm_num

private theorem threshold516 : certThresholdDataValid eb516.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk516 : 0 < 516 ∧ 516 ≤ 1238 := by norm_num

private theorem threshold519 : certThresholdDataValid eb519.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg39⟩

private theorem indexOk519 : 0 < 519 ∧ 519 ≤ 1238 := by norm_num

private theorem threshold522 : certThresholdDataValid eb522.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk522 : 0 < 522 ∧ 522 ≤ 1238 := by norm_num

private theorem threshold523 : certThresholdDataValid eb523.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk523 : 0 < 523 ∧ 523 ≤ 1238 := by norm_num

private theorem threshold524 : certThresholdDataValid eb524.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg60⟩

private theorem indexOk524 : 0 < 524 ∧ 524 ≤ 1238 := by norm_num

private theorem threshold525 : certThresholdDataValid eb525.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk525 : 0 < 525 ∧ 525 ≤ 1238 := by norm_num

private theorem threshold526 : certThresholdDataValid eb526.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg13⟩

private theorem indexOk526 : 0 < 526 ∧ 526 ≤ 1238 := by norm_num

private theorem threshold527 : certThresholdDataValid eb527.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk527 : 0 < 527 ∧ 527 ≤ 1238 := by norm_num

private theorem threshold528 : certThresholdDataValid eb528.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg24⟩

private theorem indexOk528 : 0 < 528 ∧ 528 ≤ 1238 := by norm_num

private theorem threshold529 : certThresholdDataValid eb529.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk529 : 0 < 529 ∧ 529 ≤ 1238 := by norm_num

private theorem threshold531 : certThresholdDataValid eb531.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg24⟩

private theorem indexOk531 : 0 < 531 ∧ 531 ≤ 1238 := by norm_num

private theorem threshold532 : certThresholdDataValid eb532.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg24⟩

private theorem indexOk532 : 0 < 532 ∧ 532 ≤ 1238 := by norm_num

private theorem threshold533 : certThresholdDataValid eb533.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg13⟩

private theorem indexOk533 : 0 < 533 ∧ 533 ≤ 1238 := by norm_num

private theorem threshold534 : certThresholdDataValid eb534.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg26⟩

private theorem indexOk534 : 0 < 534 ∧ 534 ≤ 1238 := by norm_num

private theorem threshold535 : certThresholdDataValid eb535.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg13⟩

private theorem indexOk535 : 0 < 535 ∧ 535 ≤ 1238 := by norm_num

private theorem threshold536 : certThresholdDataValid eb536.threshold := by
  exact ⟨endpointNonneg39, endpointNonneg26⟩

private theorem indexOk536 : 0 < 536 ∧ 536 ≤ 1238 := by norm_num

private theorem threshold537 : certThresholdDataValid eb537.threshold := by
  exact ⟨endpointNonneg40, endpointNonneg26⟩

private theorem indexOk537 : 0 < 537 ∧ 537 ≤ 1238 := by norm_num

private theorem threshold538 : certThresholdDataValid eb538.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk538 : 0 < 538 ∧ 538 ≤ 1238 := by norm_num

private theorem threshold539 : certThresholdDataValid eb539.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk539 : 0 < 539 ∧ 539 ≤ 1238 := by norm_num

private theorem threshold540 : certThresholdDataValid eb540.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg37⟩

private theorem indexOk540 : 0 < 540 ∧ 540 ≤ 1238 := by norm_num

private theorem threshold545 : certThresholdDataValid eb545.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk545 : 0 < 545 ∧ 545 ≤ 1238 := by norm_num

private theorem threshold547 : certThresholdDataValid eb547.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg37⟩

private theorem indexOk547 : 0 < 547 ∧ 547 ≤ 1238 := by norm_num

private theorem threshold550 : certThresholdDataValid eb550.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg37⟩

private theorem indexOk550 : 0 < 550 ∧ 550 ≤ 1238 := by norm_num

private theorem threshold553 : certThresholdDataValid eb553.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg36⟩

private theorem indexOk553 : 0 < 553 ∧ 553 ≤ 1238 := by norm_num

private theorem threshold554 : certThresholdDataValid eb554.threshold := by
  exact ⟨endpointNonneg25, endpointNonneg36⟩

private theorem indexOk554 : 0 < 554 ∧ 554 ≤ 1238 := by norm_num

private theorem threshold555 : certThresholdDataValid eb555.threshold := by
  exact ⟨endpointNonneg60, endpointNonneg36⟩

private theorem indexOk555 : 0 < 555 ∧ 555 ≤ 1238 := by norm_num

private theorem threshold556 : certThresholdDataValid eb556.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg37⟩

private theorem indexOk556 : 0 < 556 ∧ 556 ≤ 1238 := by norm_num

private theorem threshold557 : certThresholdDataValid eb557.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg37⟩

private theorem indexOk557 : 0 < 557 ∧ 557 ≤ 1238 := by norm_num

private theorem threshold558 : certThresholdDataValid eb558.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg61⟩

private theorem indexOk558 : 0 < 558 ∧ 558 ≤ 1238 := by norm_num

private theorem threshold559 : certThresholdDataValid eb559.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg51⟩

private theorem indexOk559 : 0 < 559 ∧ 559 ≤ 1238 := by norm_num

private theorem threshold560 : certThresholdDataValid eb560.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk560 : 0 < 560 ∧ 560 ≤ 1238 := by norm_num

private theorem threshold564 : certThresholdDataValid eb564.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg56⟩

private theorem indexOk564 : 0 < 564 ∧ 564 ≤ 1238 := by norm_num

private theorem threshold567 : certThresholdDataValid eb567.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk567 : 0 < 567 ∧ 567 ≤ 1238 := by norm_num

private theorem threshold568 : certThresholdDataValid eb568.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk568 : 0 < 568 ∧ 568 ≤ 1238 := by norm_num

private theorem threshold569 : certThresholdDataValid eb569.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk569 : 0 < 569 ∧ 569 ≤ 1238 := by norm_num

private theorem threshold570 : certThresholdDataValid eb570.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg56⟩

private theorem indexOk570 : 0 < 570 ∧ 570 ≤ 1238 := by norm_num

private theorem threshold571 : certThresholdDataValid eb571.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk571 : 0 < 571 ∧ 571 ≤ 1238 := by norm_num

private theorem threshold573 : certThresholdDataValid eb573.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk573 : 0 < 573 ∧ 573 ≤ 1238 := by norm_num

private theorem threshold575 : certThresholdDataValid eb575.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg53⟩

private theorem indexOk575 : 0 < 575 ∧ 575 ≤ 1238 := by norm_num

private theorem threshold576 : certThresholdDataValid eb576.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg55⟩

private theorem indexOk576 : 0 < 576 ∧ 576 ≤ 1238 := by norm_num

private theorem threshold577 : certThresholdDataValid eb577.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk577 : 0 < 577 ∧ 577 ≤ 1238 := by norm_num

private theorem threshold578 : certThresholdDataValid eb578.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk578 : 0 < 578 ∧ 578 ≤ 1238 := by norm_num

private theorem threshold579 : certThresholdDataValid eb579.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg53⟩

private theorem indexOk579 : 0 < 579 ∧ 579 ≤ 1238 := by norm_num

private theorem threshold581 : certThresholdDataValid eb581.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg53⟩

private theorem indexOk581 : 0 < 581 ∧ 581 ≤ 1238 := by norm_num

private theorem threshold582 : certThresholdDataValid eb582.threshold := by
  exact ⟨endpointNonneg47, endpointNonneg55⟩

private theorem indexOk582 : 0 < 582 ∧ 582 ≤ 1238 := by norm_num

private theorem threshold583 : certThresholdDataValid eb583.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg62⟩

private theorem indexOk583 : 0 < 583 ∧ 583 ≤ 1238 := by norm_num

private theorem threshold584 : certThresholdDataValid eb584.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg56⟩

private theorem indexOk584 : 0 < 584 ∧ 584 ≤ 1238 := by norm_num

private theorem threshold585 : certThresholdDataValid eb585.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg56⟩

private theorem indexOk585 : 0 < 585 ∧ 585 ≤ 1238 := by norm_num

private theorem threshold586 : certThresholdDataValid eb586.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg62⟩

private theorem indexOk586 : 0 < 586 ∧ 586 ≤ 1238 := by norm_num

private theorem threshold590 : certThresholdDataValid eb590.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg65⟩

private theorem indexOk590 : 0 < 590 ∧ 590 ≤ 1238 := by norm_num

private theorem threshold591 : certThresholdDataValid eb591.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg56⟩

private theorem indexOk591 : 0 < 591 ∧ 591 ≤ 1238 := by norm_num

private theorem threshold592 : certThresholdDataValid eb592.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg53⟩

private theorem indexOk592 : 0 < 592 ∧ 592 ≤ 1238 := by norm_num

private theorem threshold595 : certThresholdDataValid eb595.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg53⟩

private theorem indexOk595 : 0 < 595 ∧ 595 ≤ 1238 := by norm_num

private theorem threshold598 : certThresholdDataValid eb598.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg53⟩

private theorem indexOk598 : 0 < 598 ∧ 598 ≤ 1238 := by norm_num

private theorem threshold601 : certThresholdDataValid eb601.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg51⟩

private theorem indexOk601 : 0 < 601 ∧ 601 ≤ 1238 := by norm_num

private theorem threshold603 : certThresholdDataValid eb603.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk603 : 0 < 603 ∧ 603 ≤ 1238 := by norm_num

private theorem threshold604 : certThresholdDataValid eb604.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg48⟩

private theorem indexOk604 : 0 < 604 ∧ 604 ≤ 1238 := by norm_num

private theorem threshold606 : certThresholdDataValid eb606.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg48⟩

private theorem indexOk606 : 0 < 606 ∧ 606 ≤ 1238 := by norm_num

private theorem threshold607 : certThresholdDataValid eb607.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk607 : 0 < 607 ∧ 607 ≤ 1238 := by norm_num

private theorem threshold608 : certThresholdDataValid eb608.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk608 : 0 < 608 ∧ 608 ≤ 1238 := by norm_num

private theorem threshold609 : certThresholdDataValid eb609.threshold := by
  exact ⟨endpointNonneg42, endpointNonneg52⟩

private theorem indexOk609 : 0 < 609 ∧ 609 ≤ 1238 := by norm_num

private theorem threshold611 : certThresholdDataValid eb611.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk611 : 0 < 611 ∧ 611 ≤ 1238 := by norm_num

private theorem threshold612 : certThresholdDataValid eb612.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk612 : 0 < 612 ∧ 612 ≤ 1238 := by norm_num

private theorem threshold613 : certThresholdDataValid eb613.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg55⟩

private theorem indexOk613 : 0 < 613 ∧ 613 ≤ 1238 := by norm_num

private theorem threshold620 : certThresholdDataValid eb620.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk620 : 0 < 620 ∧ 620 ≤ 1238 := by norm_num

private theorem threshold621 : certThresholdDataValid eb621.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk621 : 0 < 621 ∧ 621 ≤ 1238 := by norm_num

private theorem threshold624 : certThresholdDataValid eb624.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk624 : 0 < 624 ∧ 624 ≤ 1238 := by norm_num

private theorem threshold627 : certThresholdDataValid eb627.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg39⟩

private theorem indexOk627 : 0 < 627 ∧ 627 ≤ 1238 := by norm_num

private theorem threshold630 : certThresholdDataValid eb630.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk630 : 0 < 630 ∧ 630 ≤ 1238 := by norm_num

private theorem threshold631 : certThresholdDataValid eb631.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg25⟩

private theorem indexOk631 : 0 < 631 ∧ 631 ≤ 1238 := by norm_num

private theorem threshold632 : certThresholdDataValid eb632.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg60⟩

private theorem indexOk632 : 0 < 632 ∧ 632 ≤ 1238 := by norm_num

private theorem threshold639 : certThresholdDataValid eb639.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg66⟩

private theorem indexOk639 : 0 < 639 ∧ 639 ≤ 1238 := by norm_num

private theorem threshold642 : certThresholdDataValid eb642.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg66⟩

private theorem indexOk642 : 0 < 642 ∧ 642 ≤ 1238 := by norm_num

private theorem threshold645 : certThresholdDataValid eb645.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg68⟩

private theorem indexOk645 : 0 < 645 ∧ 645 ≤ 1238 := by norm_num

private theorem threshold646 : certThresholdDataValid eb646.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk646 : 0 < 646 ∧ 646 ≤ 1238 := by norm_num

private theorem threshold647 : certThresholdDataValid eb647.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg68⟩

private theorem indexOk647 : 0 < 647 ∧ 647 ≤ 1238 := by norm_num

private theorem threshold648 : certThresholdDataValid eb648.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg73⟩

private theorem indexOk648 : 0 < 648 ∧ 648 ≤ 1238 := by norm_num

private theorem threshold654 : certThresholdDataValid eb654.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk654 : 0 < 654 ∧ 654 ≤ 1238 := by norm_num

private theorem threshold655 : certThresholdDataValid eb655.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg74⟩

private theorem indexOk655 : 0 < 655 ∧ 655 ≤ 1238 := by norm_num

private theorem threshold656 : certThresholdDataValid eb656.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg73⟩

private theorem indexOk656 : 0 < 656 ∧ 656 ≤ 1238 := by norm_num

private theorem threshold657 : certThresholdDataValid eb657.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg75⟩

private theorem indexOk657 : 0 < 657 ∧ 657 ≤ 1238 := by norm_num

private theorem threshold666 : certThresholdDataValid eb666.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg68⟩

private theorem indexOk666 : 0 < 666 ∧ 666 ≤ 1238 := by norm_num

private theorem threshold669 : certThresholdDataValid eb669.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg68⟩

private theorem indexOk669 : 0 < 669 ∧ 669 ≤ 1238 := by norm_num

private theorem threshold670 : certThresholdDataValid eb670.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg42⟩

private theorem indexOk670 : 0 < 670 ∧ 670 ≤ 1238 := by norm_num

private theorem threshold673 : certThresholdDataValid eb673.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk673 : 0 < 673 ∧ 673 ≤ 1238 := by norm_num

private theorem threshold677 : certThresholdDataValid eb677.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk677 : 0 < 677 ∧ 677 ≤ 1238 := by norm_num

private theorem threshold679 : certThresholdDataValid eb679.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk679 : 0 < 679 ∧ 679 ≤ 1238 := by norm_num

private theorem threshold680 : certThresholdDataValid eb680.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk680 : 0 < 680 ∧ 680 ≤ 1238 := by norm_num

private theorem threshold683 : certThresholdDataValid eb683.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg68⟩

private theorem indexOk683 : 0 < 683 ∧ 683 ≤ 1238 := by norm_num

private theorem threshold684 : certThresholdDataValid eb684.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk684 : 0 < 684 ∧ 684 ≤ 1238 := by norm_num

private theorem threshold685 : certThresholdDataValid eb685.threshold := by
  exact ⟨endpointNonneg71, endpointNonneg68⟩

private theorem indexOk685 : 0 < 685 ∧ 685 ≤ 1238 := by norm_num

private theorem threshold686 : certThresholdDataValid eb686.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg73⟩

private theorem indexOk686 : 0 < 686 ∧ 686 ≤ 1238 := by norm_num

private theorem threshold692 : certThresholdDataValid eb692.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk692 : 0 < 692 ∧ 692 ≤ 1238 := by norm_num

private theorem threshold695 : certThresholdDataValid eb695.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg75⟩

private theorem indexOk695 : 0 < 695 ∧ 695 ≤ 1238 := by norm_num

private theorem threshold704 : certThresholdDataValid eb704.threshold := by
  exact ⟨endpointNonneg67, endpointNonneg68⟩

private theorem indexOk704 : 0 < 704 ∧ 704 ≤ 1238 := by norm_num

private theorem threshold708 : certThresholdDataValid eb708.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg42⟩

private theorem indexOk708 : 0 < 708 ∧ 708 ≤ 1238 := by norm_num

private theorem threshold711 : certThresholdDataValid eb711.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk711 : 0 < 711 ∧ 711 ≤ 1238 := by norm_num

private theorem threshold715 : certThresholdDataValid eb715.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk715 : 0 < 715 ∧ 715 ≤ 1238 := by norm_num

private theorem threshold717 : certThresholdDataValid eb717.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk717 : 0 < 717 ∧ 717 ≤ 1238 := by norm_num

private theorem threshold718 : certThresholdDataValid eb718.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk718 : 0 < 718 ∧ 718 ≤ 1238 := by norm_num

private theorem threshold721 : certThresholdDataValid eb721.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg56⟩

private theorem indexOk721 : 0 < 721 ∧ 721 ≤ 1238 := by norm_num

private theorem threshold722 : certThresholdDataValid eb722.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg76⟩

private theorem indexOk722 : 0 < 722 ∧ 722 ≤ 1238 := by norm_num

private theorem threshold723 : certThresholdDataValid eb723.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg56⟩

private theorem indexOk723 : 0 < 723 ∧ 723 ≤ 1238 := by norm_num

private theorem threshold724 : certThresholdDataValid eb724.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg78⟩

private theorem indexOk724 : 0 < 724 ∧ 724 ≤ 1238 := by norm_num

private theorem threshold730 : certThresholdDataValid eb730.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg76⟩

private theorem indexOk730 : 0 < 730 ∧ 730 ≤ 1238 := by norm_num

private theorem threshold731 : certThresholdDataValid eb731.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg79⟩

private theorem indexOk731 : 0 < 731 ∧ 731 ≤ 1238 := by norm_num

private theorem threshold733 : certThresholdDataValid eb733.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg80⟩

private theorem indexOk733 : 0 < 733 ∧ 733 ≤ 1238 := by norm_num

private theorem threshold742 : certThresholdDataValid eb742.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg56⟩

private theorem indexOk742 : 0 < 742 ∧ 742 ≤ 1238 := by norm_num

private theorem threshold746 : certThresholdDataValid eb746.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk746 : 0 < 746 ∧ 746 ≤ 1238 := by norm_num

private theorem threshold751 : certThresholdDataValid eb751.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk751 : 0 < 751 ∧ 751 ≤ 1238 := by norm_num

private theorem threshold755 : certThresholdDataValid eb755.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg55⟩

private theorem indexOk755 : 0 < 755 ∧ 755 ≤ 1238 := by norm_num

private theorem threshold757 : certThresholdDataValid eb757.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk757 : 0 < 757 ∧ 757 ≤ 1238 := by norm_num

private theorem threshold761 : certThresholdDataValid eb761.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk761 : 0 < 761 ∧ 761 ≤ 1238 := by norm_num

private theorem threshold765 : certThresholdDataValid eb765.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk765 : 0 < 765 ∧ 765 ≤ 1238 := by norm_num

private theorem threshold766 : certThresholdDataValid eb766.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk766 : 0 < 766 ∧ 766 ≤ 1238 := by norm_num

private theorem threshold771 : certThresholdDataValid eb771.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg74⟩

private theorem indexOk771 : 0 < 771 ∧ 771 ≤ 1238 := by norm_num

private theorem threshold772 : certThresholdDataValid eb772.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk772 : 0 < 772 ∧ 772 ≤ 1238 := by norm_num

private theorem threshold773 : certThresholdDataValid eb773.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg73⟩

private theorem indexOk773 : 0 < 773 ∧ 773 ≤ 1238 := by norm_num

private theorem threshold780 : certThresholdDataValid eb780.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg74⟩

private theorem indexOk780 : 0 < 780 ∧ 780 ≤ 1238 := by norm_num

private theorem threshold783 : certThresholdDataValid eb783.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk783 : 0 < 783 ∧ 783 ≤ 1238 := by norm_num

private theorem threshold788 : certThresholdDataValid eb788.threshold := by
  exact ⟨endpointNonneg81, endpointNonneg70⟩

private theorem indexOk788 : 0 < 788 ∧ 788 ≤ 1238 := by norm_num

private theorem threshold792 : certThresholdDataValid eb792.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg42⟩

private theorem indexOk792 : 0 < 792 ∧ 792 ≤ 1238 := by norm_num

private theorem threshold795 : certThresholdDataValid eb795.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk795 : 0 < 795 ∧ 795 ≤ 1238 := by norm_num

private theorem threshold797 : certThresholdDataValid eb797.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk797 : 0 < 797 ∧ 797 ≤ 1238 := by norm_num

private theorem threshold798 : certThresholdDataValid eb798.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk798 : 0 < 798 ∧ 798 ≤ 1238 := by norm_num

private theorem threshold801 : certThresholdDataValid eb801.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg74⟩

private theorem indexOk801 : 0 < 801 ∧ 801 ≤ 1238 := by norm_num

private theorem threshold802 : certThresholdDataValid eb802.threshold := by
  exact ⟨endpointNonneg69, endpointNonneg70⟩

private theorem indexOk802 : 0 < 802 ∧ 802 ≤ 1238 := by norm_num

private theorem threshold803 : certThresholdDataValid eb803.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg73⟩

private theorem indexOk803 : 0 < 803 ∧ 803 ≤ 1238 := by norm_num

private theorem threshold808 : certThresholdDataValid eb808.threshold := by
  exact ⟨endpointNonneg72, endpointNonneg74⟩

private theorem indexOk808 : 0 < 808 ∧ 808 ≤ 1238 := by norm_num

private theorem threshold810 : certThresholdDataValid eb810.threshold := by
  exact ⟨endpointNonneg45, endpointNonneg42⟩

private theorem indexOk810 : 0 < 810 ∧ 810 ≤ 1238 := by norm_num

private theorem threshold813 : certThresholdDataValid eb813.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk813 : 0 < 813 ∧ 813 ≤ 1238 := by norm_num

private theorem threshold815 : certThresholdDataValid eb815.threshold := by
  exact ⟨endpointNonneg46, endpointNonneg7⟩

private theorem indexOk815 : 0 < 815 ∧ 815 ≤ 1238 := by norm_num

private theorem threshold816 : certThresholdDataValid eb816.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk816 : 0 < 816 ∧ 816 ≤ 1238 := by norm_num

private theorem threshold819 : certThresholdDataValid eb819.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg79⟩

private theorem indexOk819 : 0 < 819 ∧ 819 ≤ 1238 := by norm_num

private theorem threshold820 : certThresholdDataValid eb820.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg76⟩

private theorem indexOk820 : 0 < 820 ∧ 820 ≤ 1238 := by norm_num

private theorem threshold821 : certThresholdDataValid eb821.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg78⟩

private theorem indexOk821 : 0 < 821 ∧ 821 ≤ 1238 := by norm_num

private theorem threshold827 : certThresholdDataValid eb827.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg79⟩

private theorem indexOk827 : 0 < 827 ∧ 827 ≤ 1238 := by norm_num

private theorem threshold830 : certThresholdDataValid eb830.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg76⟩

private theorem indexOk830 : 0 < 830 ∧ 830 ≤ 1238 := by norm_num

private theorem threshold833 : certThresholdDataValid eb833.threshold := by
  exact ⟨endpointNonneg63, endpointNonneg56⟩

private theorem indexOk833 : 0 < 833 ∧ 833 ≤ 1238 := by norm_num

private theorem threshold834 : certThresholdDataValid eb834.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg76⟩

private theorem indexOk834 : 0 < 834 ∧ 834 ≤ 1238 := by norm_num

private theorem threshold838 : certThresholdDataValid eb838.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk838 : 0 < 838 ∧ 838 ≤ 1238 := by norm_num

private theorem threshold842 : certThresholdDataValid eb842.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk842 : 0 < 842 ∧ 842 ≤ 1238 := by norm_num

private theorem threshold845 : certThresholdDataValid eb845.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg55⟩

private theorem indexOk845 : 0 < 845 ∧ 845 ≤ 1238 := by norm_num

private theorem threshold847 : certThresholdDataValid eb847.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk847 : 0 < 847 ∧ 847 ≤ 1238 := by norm_num

private theorem threshold851 : certThresholdDataValid eb851.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk851 : 0 < 851 ∧ 851 ≤ 1238 := by norm_num

private theorem threshold852 : certThresholdDataValid eb852.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk852 : 0 < 852 ∧ 852 ≤ 1238 := by norm_num

private theorem threshold857 : certThresholdDataValid eb857.threshold := by
  exact ⟨endpointNonneg82, endpointNonneg83⟩

private theorem indexOk857 : 0 < 857 ∧ 857 ≤ 1238 := by norm_num

private theorem threshold858 : certThresholdDataValid eb858.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg85⟩

private theorem indexOk858 : 0 < 858 ∧ 858 ≤ 1238 := by norm_num

private theorem threshold859 : certThresholdDataValid eb859.threshold := by
  exact ⟨endpointNonneg86, endpointNonneg83⟩

private theorem indexOk859 : 0 < 859 ∧ 859 ≤ 1238 := by norm_num

private theorem threshold862 : certThresholdDataValid eb862.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg85⟩

private theorem indexOk862 : 0 < 862 ∧ 862 ≤ 1238 := by norm_num

private theorem threshold864 : certThresholdDataValid eb864.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg87⟩

private theorem indexOk864 : 0 < 864 ∧ 864 ≤ 1238 := by norm_num

private theorem threshold872 : certThresholdDataValid eb872.threshold := by
  exact ⟨endpointNonneg82, endpointNonneg83⟩

private theorem indexOk872 : 0 < 872 ∧ 872 ≤ 1238 := by norm_num

private theorem threshold876 : certThresholdDataValid eb876.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk876 : 0 < 876 ∧ 876 ≤ 1238 := by norm_num

private theorem threshold880 : certThresholdDataValid eb880.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk880 : 0 < 880 ∧ 880 ≤ 1238 := by norm_num

private theorem threshold885 : certThresholdDataValid eb885.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg39⟩

private theorem indexOk885 : 0 < 885 ∧ 885 ≤ 1238 := by norm_num

private theorem threshold889 : certThresholdDataValid eb889.threshold := by
  exact ⟨endpointNonneg88, endpointNonneg23⟩

private theorem indexOk889 : 0 < 889 ∧ 889 ≤ 1238 := by norm_num

private theorem threshold890 : certThresholdDataValid eb890.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg20⟩

private theorem indexOk890 : 0 < 890 ∧ 890 ≤ 1238 := by norm_num

private theorem threshold891 : certThresholdDataValid eb891.threshold := by
  exact ⟨endpointNonneg22, endpointNonneg23⟩

private theorem indexOk891 : 0 < 891 ∧ 891 ≤ 1238 := by norm_num

private theorem threshold894 : certThresholdDataValid eb894.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg20⟩

private theorem indexOk894 : 0 < 894 ∧ 894 ≤ 1238 := by norm_num

private theorem threshold896 : certThresholdDataValid eb896.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg89⟩

private theorem indexOk896 : 0 < 896 ∧ 896 ≤ 1238 := by norm_num

private theorem threshold904 : certThresholdDataValid eb904.threshold := by
  exact ⟨endpointNonneg88, endpointNonneg23⟩

private theorem indexOk904 : 0 < 904 ∧ 904 ≤ 1238 := by norm_num

private theorem threshold908 : certThresholdDataValid eb908.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg25⟩

private theorem indexOk908 : 0 < 908 ∧ 908 ≤ 1238 := by norm_num

private theorem threshold912 : certThresholdDataValid eb912.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk912 : 0 < 912 ∧ 912 ≤ 1238 := by norm_num

private theorem threshold914 : certThresholdDataValid eb914.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk914 : 0 < 914 ∧ 914 ≤ 1238 := by norm_num

private theorem threshold915 : certThresholdDataValid eb915.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk915 : 0 < 915 ∧ 915 ≤ 1238 := by norm_num

private theorem threshold918 : certThresholdDataValid eb918.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg25⟩

private theorem indexOk918 : 0 < 918 ∧ 918 ≤ 1238 := by norm_num

private theorem threshold923 : certThresholdDataValid eb923.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg25⟩

private theorem indexOk923 : 0 < 923 ∧ 923 ≤ 1238 := by norm_num

private theorem threshold927 : certThresholdDataValid eb927.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg90⟩

private theorem indexOk927 : 0 < 927 ∧ 927 ≤ 1238 := by norm_num

private theorem threshold928 : certThresholdDataValid eb928.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg85⟩

private theorem indexOk928 : 0 < 928 ∧ 928 ≤ 1238 := by norm_num

private theorem threshold929 : certThresholdDataValid eb929.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg91⟩

private theorem indexOk929 : 0 < 929 ∧ 929 ≤ 1238 := by norm_num

private theorem threshold930 : certThresholdDataValid eb930.threshold := by
  exact ⟨endpointNonneg86, endpointNonneg83⟩

private theorem indexOk930 : 0 < 930 ∧ 930 ≤ 1238 := by norm_num

private theorem threshold937 : certThresholdDataValid eb937.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg90⟩

private theorem indexOk937 : 0 < 937 ∧ 937 ≤ 1238 := by norm_num

private theorem threshold943 : certThresholdDataValid eb943.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg85⟩

private theorem indexOk943 : 0 < 943 ∧ 943 ≤ 1238 := by norm_num

private theorem threshold948 : certThresholdDataValid eb948.threshold := by
  exact ⟨endpointNonneg92, endpointNonneg85⟩

private theorem indexOk948 : 0 < 948 ∧ 948 ≤ 1238 := by norm_num

private theorem threshold952 : certThresholdDataValid eb952.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk952 : 0 < 952 ∧ 952 ≤ 1238 := by norm_num

private theorem threshold960 : certThresholdDataValid eb960.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk960 : 0 < 960 ∧ 960 ≤ 1238 := by norm_num

private theorem threshold962 : certThresholdDataValid eb962.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk962 : 0 < 962 ∧ 962 ≤ 1238 := by norm_num

private theorem threshold968 : certThresholdDataValid eb968.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg39⟩

private theorem indexOk968 : 0 < 968 ∧ 968 ≤ 1238 := by norm_num

private theorem threshold972 : certThresholdDataValid eb972.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk972 : 0 < 972 ∧ 972 ≤ 1238 := by norm_num

private theorem threshold973 : certThresholdDataValid eb973.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg90⟩

private theorem indexOk973 : 0 < 973 ∧ 973 ≤ 1238 := by norm_num

private theorem threshold974 : certThresholdDataValid eb974.threshold := by
  exact ⟨endpointNonneg84, endpointNonneg85⟩

private theorem indexOk974 : 0 < 974 ∧ 974 ≤ 1238 := by norm_num

private theorem threshold975 : certThresholdDataValid eb975.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg91⟩

private theorem indexOk975 : 0 < 975 ∧ 975 ≤ 1238 := by norm_num

private theorem threshold976 : certThresholdDataValid eb976.threshold := by
  exact ⟨endpointNonneg86, endpointNonneg83⟩

private theorem indexOk976 : 0 < 976 ∧ 976 ≤ 1238 := by norm_num

private theorem threshold983 : certThresholdDataValid eb983.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg90⟩

private theorem indexOk983 : 0 < 983 ∧ 983 ≤ 1238 := by norm_num

private theorem threshold984 : certThresholdDataValid eb984.threshold := by
  exact ⟨endpointNonneg11, endpointNonneg10⟩

private theorem indexOk984 : 0 < 984 ∧ 984 ≤ 1238 := by norm_num

private theorem threshold986 : certThresholdDataValid eb986.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk986 : 0 < 986 ∧ 986 ≤ 1238 := by norm_num

private theorem threshold994 : certThresholdDataValid eb994.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk994 : 0 < 994 ∧ 994 ≤ 1238 := by norm_num

private theorem threshold996 : certThresholdDataValid eb996.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg16⟩

private theorem indexOk996 : 0 < 996 ∧ 996 ≤ 1238 := by norm_num

private theorem threshold997 : certThresholdDataValid eb997.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk997 : 0 < 997 ∧ 997 ≤ 1238 := by norm_num

private theorem threshold1000 : certThresholdDataValid eb1000.threshold := by
  exact ⟨endpointNonneg57, endpointNonneg39⟩

private theorem indexOk1000 : 0 < 1000 ∧ 1000 ≤ 1238 := by norm_num

private theorem threshold1006 : certThresholdDataValid eb1006.threshold := by
  exact ⟨endpointNonneg58, endpointNonneg39⟩

private theorem indexOk1006 : 0 < 1006 ∧ 1006 ≤ 1238 := by norm_num

private theorem threshold1010 : certThresholdDataValid eb1010.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1010 : 0 < 1010 ∧ 1010 ≤ 1238 := by norm_num

private theorem threshold1011 : certThresholdDataValid eb1011.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg18⟩

private theorem indexOk1011 : 0 < 1011 ∧ 1011 ≤ 1238 := by norm_num

private theorem threshold1012 : certThresholdDataValid eb1012.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg20⟩

private theorem indexOk1012 : 0 < 1012 ∧ 1012 ≤ 1238 := by norm_num

private theorem threshold1013 : certThresholdDataValid eb1013.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg21⟩

private theorem indexOk1013 : 0 < 1013 ∧ 1013 ≤ 1238 := by norm_num

private theorem threshold1014 : certThresholdDataValid eb1014.threshold := by
  exact ⟨endpointNonneg22, endpointNonneg23⟩

private theorem indexOk1014 : 0 < 1014 ∧ 1014 ≤ 1238 := by norm_num

private theorem threshold1021 : certThresholdDataValid eb1021.threshold := by
  exact ⟨endpointNonneg17, endpointNonneg18⟩

private theorem indexOk1021 : 0 < 1021 ∧ 1021 ≤ 1238 := by norm_num

private theorem threshold1027 : certThresholdDataValid eb1027.threshold := by
  exact ⟨endpointNonneg19, endpointNonneg20⟩

private theorem indexOk1027 : 0 < 1027 ∧ 1027 ≤ 1238 := by norm_num

private theorem threshold1032 : certThresholdDataValid eb1032.threshold := by
  exact ⟨endpointNonneg93, endpointNonneg20⟩

private theorem indexOk1032 : 0 < 1032 ∧ 1032 ≤ 1238 := by norm_num

private theorem threshold1036 : certThresholdDataValid eb1036.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg25⟩

private theorem indexOk1036 : 0 < 1036 ∧ 1036 ≤ 1238 := by norm_num

private theorem threshold1037 : certThresholdDataValid eb1037.threshold := by
  exact ⟨endpointNonneg59, endpointNonneg13⟩

private theorem indexOk1037 : 0 < 1037 ∧ 1037 ≤ 1238 := by norm_num

private theorem threshold1044 : certThresholdDataValid eb1044.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk1044 : 0 < 1044 ∧ 1044 ≤ 1238 := by norm_num

private theorem threshold1046 : certThresholdDataValid eb1046.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg14⟩

private theorem indexOk1046 : 0 < 1046 ∧ 1046 ≤ 1238 := by norm_num

private theorem threshold1047 : certThresholdDataValid eb1047.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1047 : 0 < 1047 ∧ 1047 ≤ 1238 := by norm_num

private theorem threshold1050 : certThresholdDataValid eb1050.threshold := by
  exact ⟨endpointNonneg24, endpointNonneg25⟩

private theorem indexOk1050 : 0 < 1050 ∧ 1050 ≤ 1238 := by norm_num

private theorem threshold1056 : certThresholdDataValid eb1056.threshold := by
  exact ⟨endpointNonneg26, endpointNonneg25⟩

private theorem indexOk1056 : 0 < 1056 ∧ 1056 ≤ 1238 := by norm_num

private theorem threshold1060 : certThresholdDataValid eb1060.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1060 : 0 < 1060 ∧ 1060 ≤ 1238 := by norm_num

private theorem threshold1061 : certThresholdDataValid eb1061.threshold := by
  exact ⟨endpointNonneg29, endpointNonneg30⟩

private theorem indexOk1061 : 0 < 1061 ∧ 1061 ≤ 1238 := by norm_num

private theorem threshold1062 : certThresholdDataValid eb1062.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg32⟩

private theorem indexOk1062 : 0 < 1062 ∧ 1062 ≤ 1238 := by norm_num

private theorem threshold1063 : certThresholdDataValid eb1063.threshold := by
  exact ⟨endpointNonneg29, endpointNonneg33⟩

private theorem indexOk1063 : 0 < 1063 ∧ 1063 ≤ 1238 := by norm_num

private theorem threshold1064 : certThresholdDataValid eb1064.threshold := by
  exact ⟨endpointNonneg34, endpointNonneg35⟩

private theorem indexOk1064 : 0 < 1064 ∧ 1064 ≤ 1238 := by norm_num

private theorem threshold1071 : certThresholdDataValid eb1071.threshold := by
  exact ⟨endpointNonneg29, endpointNonneg30⟩

private theorem indexOk1071 : 0 < 1071 ∧ 1071 ≤ 1238 := by norm_num

private theorem threshold1077 : certThresholdDataValid eb1077.threshold := by
  exact ⟨endpointNonneg31, endpointNonneg32⟩

private theorem indexOk1077 : 0 < 1077 ∧ 1077 ≤ 1238 := by norm_num

private theorem threshold1082 : certThresholdDataValid eb1082.threshold := by
  exact ⟨endpointNonneg94, endpointNonneg32⟩

private theorem indexOk1082 : 0 < 1082 ∧ 1082 ≤ 1238 := by norm_num

private theorem threshold1086 : certThresholdDataValid eb1086.threshold := by
  exact ⟨endpointNonneg36, endpointNonneg37⟩

private theorem indexOk1086 : 0 < 1086 ∧ 1086 ≤ 1238 := by norm_num

private theorem threshold1087 : certThresholdDataValid eb1087.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1087 : 0 < 1087 ∧ 1087 ≤ 1238 := by norm_num

private theorem threshold1092 : certThresholdDataValid eb1092.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk1092 : 0 < 1092 ∧ 1092 ≤ 1238 := by norm_num

private theorem threshold1094 : certThresholdDataValid eb1094.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg38⟩

private theorem indexOk1094 : 0 < 1094 ∧ 1094 ≤ 1238 := by norm_num

private theorem threshold1095 : certThresholdDataValid eb1095.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1095 : 0 < 1095 ∧ 1095 ≤ 1238 := by norm_num

private theorem threshold1098 : certThresholdDataValid eb1098.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1098 : 0 < 1098 ∧ 1098 ≤ 1238 := by norm_num

private theorem threshold1099 : certThresholdDataValid eb1099.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg76⟩

private theorem indexOk1099 : 0 < 1099 ∧ 1099 ≤ 1238 := by norm_num

private theorem threshold1100 : certThresholdDataValid eb1100.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg78⟩

private theorem indexOk1100 : 0 < 1100 ∧ 1100 ≤ 1238 := by norm_num

private theorem threshold1104 : certThresholdDataValid eb1104.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg79⟩

private theorem indexOk1104 : 0 < 1104 ∧ 1104 ≤ 1238 := by norm_num

private theorem threshold1105 : certThresholdDataValid eb1105.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg76⟩

private theorem indexOk1105 : 0 < 1105 ∧ 1105 ≤ 1238 := by norm_num

private theorem threshold1106 : certThresholdDataValid eb1106.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg79⟩

private theorem indexOk1106 : 0 < 1106 ∧ 1106 ≤ 1238 := by norm_num

private theorem threshold1107 : certThresholdDataValid eb1107.threshold := by
  exact ⟨endpointNonneg77, endpointNonneg78⟩

private theorem indexOk1107 : 0 < 1107 ∧ 1107 ≤ 1238 := by norm_num

private theorem threshold1108 : certThresholdDataValid eb1108.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg80⟩

private theorem indexOk1108 : 0 < 1108 ∧ 1108 ≤ 1238 := by norm_num

private theorem threshold1116 : certThresholdDataValid eb1116.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk1116 : 0 < 1116 ∧ 1116 ≤ 1238 := by norm_num

private theorem threshold1121 : certThresholdDataValid eb1121.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg53⟩

private theorem indexOk1121 : 0 < 1121 ∧ 1121 ≤ 1238 := by norm_num

private theorem threshold1122 : certThresholdDataValid eb1122.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk1122 : 0 < 1122 ∧ 1122 ≤ 1238 := by norm_num

private theorem threshold1123 : certThresholdDataValid eb1123.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg56⟩

private theorem indexOk1123 : 0 < 1123 ∧ 1123 ≤ 1238 := by norm_num

private theorem threshold1124 : certThresholdDataValid eb1124.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg54⟩

private theorem indexOk1124 : 0 < 1124 ∧ 1124 ≤ 1238 := by norm_num

private theorem threshold1125 : certThresholdDataValid eb1125.threshold := by
  exact ⟨endpointNonneg48, endpointNonneg55⟩

private theorem indexOk1125 : 0 < 1125 ∧ 1125 ≤ 1238 := by norm_num

private theorem threshold1127 : certThresholdDataValid eb1127.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1127 : 0 < 1127 ∧ 1127 ≤ 1238 := by norm_num

private theorem threshold1131 : certThresholdDataValid eb1131.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk1131 : 0 < 1131 ∧ 1131 ≤ 1238 := by norm_num

private theorem threshold1135 : certThresholdDataValid eb1135.threshold := by
  exact ⟨endpointNonneg49, endpointNonneg50⟩

private theorem indexOk1135 : 0 < 1135 ∧ 1135 ≤ 1238 := by norm_num

private theorem threshold1136 : certThresholdDataValid eb1136.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1136 : 0 < 1136 ∧ 1136 ≤ 1238 := by norm_num

private theorem threshold1141 : certThresholdDataValid eb1141.threshold := by
  exact ⟨endpointNonneg95, endpointNonneg96⟩

private theorem indexOk1141 : 0 < 1141 ∧ 1141 ≤ 1238 := by norm_num

private theorem threshold1142 : certThresholdDataValid eb1142.threshold := by
  exact ⟨endpointNonneg97, endpointNonneg98⟩

private theorem indexOk1142 : 0 < 1142 ∧ 1142 ≤ 1238 := by norm_num

private theorem threshold1143 : certThresholdDataValid eb1143.threshold := by
  exact ⟨endpointNonneg99, endpointNonneg96⟩

private theorem indexOk1143 : 0 < 1143 ∧ 1143 ≤ 1238 := by norm_num

private theorem threshold1144 : certThresholdDataValid eb1144.threshold := by
  exact ⟨endpointNonneg64, endpointNonneg100⟩

private theorem indexOk1144 : 0 < 1144 ∧ 1144 ≤ 1238 := by norm_num

private theorem threshold1146 : certThresholdDataValid eb1146.threshold := by
  exact ⟨endpointNonneg97, endpointNonneg98⟩

private theorem indexOk1146 : 0 < 1146 ∧ 1146 ≤ 1238 := by norm_num

private theorem threshold1148 : certThresholdDataValid eb1148.threshold := by
  exact ⟨endpointNonneg97, endpointNonneg101⟩

private theorem indexOk1148 : 0 < 1148 ∧ 1148 ≤ 1238 := by norm_num

private theorem threshold1157 : certThresholdDataValid eb1157.threshold := by
  exact ⟨endpointNonneg95, endpointNonneg96⟩

private theorem indexOk1157 : 0 < 1157 ∧ 1157 ≤ 1238 := by norm_num

private theorem threshold1160 : certThresholdDataValid eb1160.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg53⟩

private theorem indexOk1160 : 0 < 1160 ∧ 1160 ≤ 1238 := by norm_num

private theorem threshold1164 : certThresholdDataValid eb1164.threshold := by
  exact ⟨endpointNonneg62, endpointNonneg53⟩

private theorem indexOk1164 : 0 < 1164 ∧ 1164 ≤ 1238 := by norm_num

private theorem threshold1169 : certThresholdDataValid eb1169.threshold := by
  exact ⟨endpointNonneg65, endpointNonneg53⟩

private theorem indexOk1169 : 0 < 1169 ∧ 1169 ≤ 1238 := by norm_num

private theorem threshold1174 : certThresholdDataValid eb1174.threshold := by
  exact ⟨endpointNonneg9, endpointNonneg9⟩

private theorem indexOk1174 : 0 < 1174 ∧ 1174 ≤ 1238 := by norm_num

private theorem threshold1176 : certThresholdDataValid eb1176.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1176 : 0 < 1176 ∧ 1176 ≤ 1238 := by norm_num

private theorem threshold1178 : certThresholdDataValid eb1178.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1178 : 0 < 1178 ∧ 1178 ≤ 1238 := by norm_num

private theorem threshold1180 : certThresholdDataValid eb1180.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1180 : 0 < 1180 ∧ 1180 ≤ 1238 := by norm_num

private theorem threshold1182 : certThresholdDataValid eb1182.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1182 : 0 < 1182 ∧ 1182 ≤ 1238 := by norm_num

private theorem threshold1184 : certThresholdDataValid eb1184.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1184 : 0 < 1184 ∧ 1184 ≤ 1238 := by norm_num

private theorem threshold1186 : certThresholdDataValid eb1186.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1186 : 0 < 1186 ∧ 1186 ≤ 1238 := by norm_num

private theorem threshold1188 : certThresholdDataValid eb1188.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1188 : 0 < 1188 ∧ 1188 ≤ 1238 := by norm_num

private theorem threshold1190 : certThresholdDataValid eb1190.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1190 : 0 < 1190 ∧ 1190 ≤ 1238 := by norm_num

private theorem threshold1192 : certThresholdDataValid eb1192.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1192 : 0 < 1192 ∧ 1192 ≤ 1238 := by norm_num

private theorem threshold1194 : certThresholdDataValid eb1194.threshold := by
  exact ⟨endpointNonneg6, endpointNonneg7⟩

private theorem indexOk1194 : 0 < 1194 ∧ 1194 ≤ 1238 := by norm_num

private theorem threshold1196 : certThresholdDataValid eb1196.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1196 : 0 < 1196 ∧ 1196 ≤ 1238 := by norm_num

private theorem threshold1198 : certThresholdDataValid eb1198.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1198 : 0 < 1198 ∧ 1198 ≤ 1238 := by norm_num

private theorem threshold1200 : certThresholdDataValid eb1200.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1200 : 0 < 1200 ∧ 1200 ≤ 1238 := by norm_num

private theorem threshold1202 : certThresholdDataValid eb1202.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1202 : 0 < 1202 ∧ 1202 ≤ 1238 := by norm_num

private theorem threshold1204 : certThresholdDataValid eb1204.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1204 : 0 < 1204 ∧ 1204 ≤ 1238 := by norm_num

private theorem threshold1206 : certThresholdDataValid eb1206.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1206 : 0 < 1206 ∧ 1206 ≤ 1238 := by norm_num

private theorem threshold1208 : certThresholdDataValid eb1208.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1208 : 0 < 1208 ∧ 1208 ≤ 1238 := by norm_num

private theorem threshold1210 : certThresholdDataValid eb1210.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1210 : 0 < 1210 ∧ 1210 ≤ 1238 := by norm_num

private theorem threshold1212 : certThresholdDataValid eb1212.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1212 : 0 < 1212 ∧ 1212 ≤ 1238 := by norm_num

private theorem threshold1214 : certThresholdDataValid eb1214.threshold := by
  exact ⟨endpointNonneg15, endpointNonneg10⟩

private theorem indexOk1214 : 0 < 1214 ∧ 1214 ≤ 1238 := by norm_num

private theorem threshold1216 : certThresholdDataValid eb1216.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1216 : 0 < 1216 ∧ 1216 ≤ 1238 := by norm_num

private theorem threshold1218 : certThresholdDataValid eb1218.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1218 : 0 < 1218 ∧ 1218 ≤ 1238 := by norm_num

private theorem threshold1220 : certThresholdDataValid eb1220.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1220 : 0 < 1220 ∧ 1220 ≤ 1238 := by norm_num

private theorem threshold1222 : certThresholdDataValid eb1222.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1222 : 0 < 1222 ∧ 1222 ≤ 1238 := by norm_num

private theorem threshold1224 : certThresholdDataValid eb1224.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1224 : 0 < 1224 ∧ 1224 ≤ 1238 := by norm_num

private theorem threshold1226 : certThresholdDataValid eb1226.threshold := by
  exact ⟨endpointNonneg12, endpointNonneg13⟩

private theorem indexOk1226 : 0 < 1226 ∧ 1226 ≤ 1238 := by norm_num

private theorem threshold1228 : certThresholdDataValid eb1228.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg56⟩

private theorem indexOk1228 : 0 < 1228 ∧ 1228 ≤ 1238 := by norm_num

private theorem threshold1230 : certThresholdDataValid eb1230.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg56⟩

private theorem indexOk1230 : 0 < 1230 ∧ 1230 ≤ 1238 := by norm_num

private theorem threshold1232 : certThresholdDataValid eb1232.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1232 : 0 < 1232 ∧ 1232 ≤ 1238 := by norm_num

private theorem threshold1234 : certThresholdDataValid eb1234.threshold := by
  exact ⟨endpointNonneg51, endpointNonneg50⟩

private theorem indexOk1234 : 0 < 1234 ∧ 1234 ≤ 1238 := by norm_num

private theorem threshold1236 : certThresholdDataValid eb1236.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1236 : 0 < 1236 ∧ 1236 ≤ 1238 := by norm_num

private theorem threshold1238 : certThresholdDataValid eb1238.threshold := by
  exact ⟨endpointNonneg27, endpointNonneg28⟩

private theorem indexOk1238 : 0 < 1238 ∧ 1238 ≤ 1238 := by norm_num

private theorem explicit_pair_valid (lid uid : ℕ) (q : ℚ) (l u : CertBound)
    (hlid : 0 < lid) (hlength : lid ≤ 1238)
    (huid : 0 < uid) (hulength : uid ≤ 1238)
    (hl : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 lid = l)
    (hu : lowerEarlyTerminalBound lowerEarlyTerminalTerminal3 uid = u)
    (hll : l.lower = true) (hul : u.lower = false)
    (hlt : certThresholdDataValid l.threshold)
    (hut : certThresholdDataValid u.threshold)
    (hc : ∀ i j : Fin 3, certCoefficientBoundValid
      ((certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) earlyRect) i j) q)
    (hq : 0 < q ∨ l.strict = true ∨ u.strict = true) :
    lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 ⟨lid,uid,q⟩ := by
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
   n1,100,pos1,cp1,ivec3,dvec3,dpos3,vp3,ivec2,dvec2,dpos2,vp2⟩

private def bk110 : BoundKit true :=
  ⟨110,eb110,indexOk110.1,indexOk110.2,lookup110,rfl,threshold110,
   n55,47838,pos55,cp55,ivec17,dvec17,dpos17,vp17,ivec16,dvec16,dpos16,vp16⟩

private def bk114 : BoundKit true :=
  ⟨114,eb114,indexOk114.1,indexOk114.2,lookup114,rfl,threshold114,
   n60,34170,pos60,cp60,ivec17,dvec17,dpos17,vp17,ivec16,dvec16,dpos16,vp16⟩

private def bk115 : BoundKit true :=
  ⟨115,eb115,indexOk115.1,indexOk115.2,lookup115,rfl,threshold115,
   n61,102,pos61,cp61,ivec21,dvec21,dpos21,vp21,ivec20,dvec20,dpos20,vp20⟩

private def bk145 : BoundKit true :=
  ⟨145,eb145,indexOk145.1,indexOk145.2,lookup145,rfl,threshold145,
   n299,7,pos299,cp299,ivec1,dvec1,dpos1,vp1,ivec114,dvec114,dpos114,vp114⟩

private def bk146 : BoundKit true :=
  ⟨146,eb146,indexOk146.1,indexOk146.2,lookup146,rfl,threshold146,
   n300,5,pos300,cp300,ivec1,dvec1,dpos1,vp1,ivec114,dvec114,dpos114,vp114⟩

private def bk147 : BoundKit true :=
  ⟨147,eb147,indexOk147.1,indexOk147.2,lookup147,rfl,threshold147,
   n301,1,pos301,cp301,ivec115,dvec115,dpos115,vp115,ivec20,dvec20,dpos20,vp20⟩

private def bk162 : BoundKit false :=
  ⟨162,eb162,indexOk162.1,indexOk162.2,lookup162,rfl,threshold162,
   n151,848225,pos151,cp151,ivec59,dvec59,dpos59,vp59,ivec33,dvec33,dpos33,vp33⟩

private def bk164 : BoundKit false :=
  ⟨164,eb164,indexOk164.1,indexOk164.2,lookup164,rfl,threshold164,
   n158,43885,pos158,cp158,ivec63,dvec63,dpos63,vp63,ivec7,dvec7,dpos7,vp7⟩

private def bk165 : BoundKit false :=
  ⟨165,eb165,indexOk165.1,indexOk165.2,lookup165,rfl,threshold165,
   n180,57974,pos180,cp180,ivec12,dvec12,dpos12,vp12,ivec7,dvec7,dpos7,vp7⟩

private def bk170 : BoundKit true :=
  ⟨170,eb170,indexOk170.1,indexOk170.2,lookup170,rfl,threshold170,
   n189,7881307,pos189,cp189,ivec75,dvec75,dpos75,vp75,ivec38,dvec38,dpos38,vp38⟩

private def bk172 : BoundKit true :=
  ⟨172,eb172,indexOk172.1,indexOk172.2,lookup172,rfl,threshold172,
   n192,804215,pos192,cp192,ivec75,dvec75,dpos75,vp75,ivec38,dvec38,dpos38,vp38⟩

private def bk173 : BoundKit true :=
  ⟨173,eb173,indexOk173.1,indexOk173.2,lookup173,rfl,threshold173,
   n193,28987,pos193,cp193,ivec12,dvec12,dpos12,vp12,ivec56,dvec56,dpos56,vp56⟩

private def bk183 : BoundKit false :=
  ⟨183,eb183,indexOk183.1,indexOk183.2,lookup183,rfl,threshold183,
   n166,3029375,pos166,cp166,ivec59,dvec59,dpos59,vp59,ivec33,dvec33,dpos33,vp33⟩

private def bk186 : BoundKit true :=
  ⟨186,eb186,indexOk186.1,indexOk186.2,lookup186,rfl,threshold186,
   n132,12314,pos132,cp132,ivec11,dvec11,dpos11,vp11,ivec7,dvec7,dpos7,vp7⟩

private def bk194 : BoundKit true :=
  ⟨194,eb194,indexOk194.1,indexOk194.2,lookup194,rfl,threshold194,
   n432,580027,pos432,cp432,ivec54,dvec54,dpos54,vp54,ivec153,dvec153,dpos153,vp153⟩

private def bk195 : BoundKit true :=
  ⟨195,eb195,indexOk195.1,indexOk195.2,lookup195,rfl,threshold195,
   n435,6157,pos435,cp435,ivec11,dvec11,dpos11,vp11,ivec132,dvec132,dpos132,vp132⟩

private def bk196 : BoundKit true :=
  ⟨196,eb196,indexOk196.1,indexOk196.2,lookup196,rfl,threshold196,
   n434,82861,pos434,cp434,ivec54,dvec54,dpos54,vp54,ivec153,dvec153,dpos153,vp153⟩

private def bk216 : BoundKit false :=
  ⟨216,eb216,indexOk216.1,indexOk216.2,lookup216,rfl,threshold216,
   n221,707,pos221,cp221,ivec12,dvec12,dpos12,vp12,ivec9,dvec9,dpos9,vp9⟩

private def bk218 : BoundKit false :=
  ⟨218,eb218,indexOk218.1,indexOk218.2,lookup218,rfl,threshold218,
   n196,1696450,pos196,cp196,ivec59,dvec59,dpos59,vp59,ivec42,dvec42,dpos42,vp42⟩

private def bk225 : BoundKit true :=
  ⟨225,eb225,indexOk225.1,indexOk225.2,lookup225,rfl,threshold225,
   n196,1696450,pos196,cp196,ivec59,dvec59,dpos59,vp59,ivec42,dvec42,dpos42,vp42⟩

private def bk229 : BoundKit true :=
  ⟨229,eb229,indexOk229.1,indexOk229.2,lookup229,rfl,threshold229,
   n200,6058750,pos200,cp200,ivec59,dvec59,dpos59,vp59,ivec42,dvec42,dpos42,vp42⟩

private def bk230 : BoundKit true :=
  ⟨230,eb230,indexOk230.1,indexOk230.2,lookup230,rfl,threshold230,
   n201,12314,pos201,cp201,ivec11,dvec11,dpos11,vp11,ivec9,dvec9,dpos9,vp9⟩

private def bk242 : BoundKit true :=
  ⟨242,eb242,indexOk242.1,indexOk242.2,lookup242,rfl,threshold242,
   n468,1160054,pos468,cp468,ivec54,dvec54,dpos54,vp54,ivec164,dvec164,dpos164,vp164⟩

private def bk244 : BoundKit true :=
  ⟨244,eb244,indexOk244.1,indexOk244.2,lookup244,rfl,threshold244,
   n470,828610,pos470,cp470,ivec54,dvec54,dpos54,vp54,ivec164,dvec164,dpos164,vp164⟩

private def bk257 : BoundKit false :=
  ⟨257,eb257,indexOk257.1,indexOk257.2,lookup257,rfl,threshold257,
   n240,57974,pos240,cp240,ivec12,dvec12,dpos12,vp12,ivec10,dvec10,dpos10,vp10⟩

private def bk258 : BoundKit false :=
  ⟨258,eb258,indexOk258.1,indexOk258.2,lookup258,rfl,threshold258,
   n533,21210854,pos533,cp533,ivec170,dvec170,dpos170,vp170,ivec80,dvec80,dpos80,vp80⟩

private def bk259 : BoundKit false :=
  ⟨259,eb259,indexOk259.1,indexOk259.2,lookup259,rfl,threshold259,
   n536,250733964,pos536,cp536,ivec157,dvec157,dpos157,vp157,ivec117,dvec117,dpos117,vp117⟩

private def bk260 : BoundKit false :=
  ⟨260,eb260,indexOk260.1,indexOk260.2,lookup260,rfl,threshold260,
   n534,198830,pos534,cp534,ivec171,dvec171,dpos171,vp171,ivec10,dvec10,dpos10,vp10⟩

private def bk261 : BoundKit false :=
  ⟨261,eb261,indexOk261.1,indexOk261.2,lookup261,rfl,threshold261,
   n535,454510,pos535,cp535,ivec156,dvec156,dpos156,vp156,ivec10,dvec10,dpos10,vp10⟩

private def bk268 : BoundKit false :=
  ⟨268,eb268,indexOk268.1,indexOk268.2,lookup268,rfl,threshold268,
   n537,75753050,pos537,cp537,ivec170,dvec170,dpos170,vp170,ivec80,dvec80,dpos80,vp80⟩

private def bk272 : BoundKit true :=
  ⟨272,eb272,indexOk272.1,indexOk272.2,lookup272,rfl,threshold272,
   n538,4216979,pos538,cp538,ivec159,dvec159,dpos159,vp159,ivec144,dvec144,dpos144,vp144⟩

private def bk280 : BoundKit true :=
  ⟨280,eb280,indexOk280.1,indexOk280.2,lookup280,rfl,threshold280,
   n539,7881307,pos539,cp539,ivec75,dvec75,dpos75,vp75,ivec167,dvec167,dpos167,vp167⟩

private def bk282 : BoundKit true :=
  ⟨282,eb282,indexOk282.1,indexOk282.2,lookup282,rfl,threshold282,
   n540,804215,pos540,cp540,ivec75,dvec75,dpos75,vp75,ivec167,dvec167,dpos167,vp167⟩

private def bk283 : BoundKit true :=
  ⟨283,eb283,indexOk283.1,indexOk283.2,lookup283,rfl,threshold283,
   n541,4141,pos541,cp541,ivec12,dvec12,dpos12,vp12,ivec168,dvec168,dpos168,vp168⟩

private def bk286 : BoundKit true :=
  ⟨286,eb286,indexOk286.1,indexOk286.2,lookup286,rfl,threshold286,
   n542,50928131,pos542,cp542,ivec159,dvec159,dpos159,vp159,ivec169,dvec169,dpos169,vp169⟩

private def bk292 : BoundKit true :=
  ⟨292,eb292,indexOk292.1,indexOk292.2,lookup292,rfl,threshold292,
   n543,29542461,pos543,cp543,ivec160,dvec160,dpos160,vp160,ivec144,dvec144,dpos144,vp144⟩

private def bk296 : BoundKit true :=
  ⟨296,eb296,indexOk296.1,indexOk296.2,lookup296,rfl,threshold296,
   n544,57974,pos544,cp544,ivec12,dvec12,dpos12,vp12,ivec146,dvec146,dpos146,vp146⟩

private def bk297 : BoundKit false :=
  ⟨297,eb297,indexOk297.1,indexOk297.2,lookup297,rfl,threshold297,
   n304,4739,pos304,cp304,ivec13,dvec13,dpos13,vp13,ivec10,dvec10,dpos10,vp10⟩

private def bk298 : BoundKit false :=
  ⟨298,eb298,indexOk298.1,indexOk298.2,lookup298,rfl,threshold298,
   n545,209049862,pos545,cp545,ivec173,dvec173,dpos173,vp173,ivec80,dvec80,dpos80,vp80⟩

private def bk299 : BoundKit false :=
  ⟨299,eb299,indexOk299.1,indexOk299.2,lookup299,rfl,threshold299,
   n548,770972124,pos548,cp548,ivec176,dvec176,dpos176,vp176,ivec117,dvec117,dpos117,vp117⟩

private def bk300 : BoundKit false :=
  ⟨300,eb300,indexOk300.1,indexOk300.2,lookup300,rfl,threshold300,
   n546,1843390,pos546,cp546,ivec174,dvec174,dpos174,vp174,ivec10,dvec10,dpos10,vp10⟩

private def bk301 : BoundKit false :=
  ⟨301,eb301,indexOk301.1,indexOk301.2,lookup301,rfl,threshold301,
   n547,502670,pos547,cp547,ivec175,dvec175,dpos175,vp175,ivec10,dvec10,dpos10,vp10⟩

private def bk308 : BoundKit false :=
  ⟨308,eb308,indexOk308.1,indexOk308.2,lookup308,rfl,threshold308,
   n549,746606650,pos549,cp549,ivec173,dvec173,dpos173,vp173,ivec80,dvec80,dpos80,vp80⟩

private def bk312 : BoundKit true :=
  ⟨312,eb312,indexOk312.1,indexOk312.2,lookup312,rfl,threshold312,
   n550,312797329,pos550,cp550,ivec178,dvec178,dpos178,vp178,ivec144,dvec144,dpos144,vp144⟩

private def bk318 : BoundKit true :=
  ⟨318,eb318,indexOk318.1,indexOk318.2,lookup318,rfl,threshold318,
   n551,65710974,pos551,cp551,ivec84,dvec84,dpos84,vp84,ivec167,dvec167,dpos167,vp167⟩

private def bk320 : BoundKit true :=
  ⟨320,eb320,indexOk320.1,indexOk320.2,lookup320,rfl,threshold320,
   n552,46936410,pos552,cp552,ivec84,dvec84,dpos84,vp84,ivec167,dvec167,dpos167,vp167⟩

private def bk321 : BoundKit true :=
  ⟨321,eb321,indexOk321.1,indexOk321.2,lookup321,rfl,threshold321,
   n553,4062,pos553,cp553,ivec13,dvec13,dpos13,vp13,ivec168,dvec168,dpos168,vp168⟩

private def bk324 : BoundKit true :=
  ⟨324,eb324,indexOk324.1,indexOk324.2,lookup324,rfl,threshold324,
   n554,28434,pos554,cp554,ivec13,dvec13,dpos13,vp13,ivec146,dvec146,dpos146,vp146⟩

private def bk327 : BoundKit true :=
  ⟨327,eb327,indexOk327.1,indexOk327.2,lookup327,rfl,threshold327,
   n133,1160054,pos133,cp133,ivec54,dvec54,dpos54,vp54,ivec38,dvec38,dpos38,vp38⟩

private def bk329 : BoundKit true :=
  ⟨329,eb329,indexOk329.1,indexOk329.2,lookup329,rfl,threshold329,
   n136,828610,pos136,cp136,ivec54,dvec54,dpos54,vp54,ivec38,dvec38,dpos38,vp38⟩

private def bk346 : BoundKit false :=
  ⟨346,eb346,indexOk346.1,indexOk346.2,lookup346,rfl,threshold346,
   n186,1160054,pos186,cp186,ivec54,dvec54,dpos54,vp54,ivec49,dvec49,dpos49,vp49⟩

private def bk348 : BoundKit true :=
  ⟨348,eb348,indexOk348.1,indexOk348.2,lookup348,rfl,threshold348,
   n186,1160054,pos186,cp186,ivec54,dvec54,dpos54,vp54,ivec49,dvec49,dpos49,vp49⟩

private def bk349 : BoundKit true :=
  ⟨349,eb349,indexOk349.1,indexOk349.2,lookup349,rfl,threshold349,
   n178,165722,pos178,cp178,ivec54,dvec54,dpos54,vp54,ivec49,dvec49,dpos49,vp49⟩

private def bk355 : BoundKit true :=
  ⟨355,eb355,indexOk355.1,indexOk355.2,lookup355,rfl,threshold355,
   n168,1541891,pos168,cp168,ivec69,dvec69,dpos69,vp69,ivec30,dvec30,dpos30,vp30⟩

private def bk356 : BoundKit true :=
  ⟨356,eb356,indexOk356.1,indexOk356.2,lookup356,rfl,threshold356,
   n172,18621299,pos172,cp172,ivec69,dvec69,dpos69,vp69,ivec61,dvec61,dpos61,vp61⟩

private def bk357 : BoundKit true :=
  ⟨357,eb357,indexOk357.1,indexOk357.2,lookup357,rfl,threshold357,
   n173,34534643,pos173,cp173,ivec70,dvec70,dpos70,vp70,ivec30,dvec30,dpos30,vp30⟩

private def bk359 : BoundKit false :=
  ⟨359,eb359,indexOk359.1,indexOk359.2,lookup359,rfl,threshold359,
   n237,2251802,pos237,cp237,ivec75,dvec75,dpos75,vp75,ivec80,dvec80,dpos80,vp80⟩

private def bk375 : BoundKit false :=
  ⟨375,eb375,indexOk375.1,indexOk375.2,lookup375,rfl,threshold375,
   n303,10951829,pos303,cp303,ivec84,dvec84,dpos84,vp84,ivec80,dvec80,dpos80,vp80⟩

private def bk376 : BoundKit false :=
  ⟨376,eb376,indexOk376.1,indexOk376.2,lookup376,rfl,threshold376,
   n305,52684372,pos305,cp305,ivec85,dvec85,dpos85,vp85,ivec117,dvec117,dpos117,vp117⟩

private def bk380 : BoundKit false :=
  ⟨380,eb380,indexOk380.1,indexOk380.2,lookup380,rfl,threshold380,
   n306,7822735,pos306,cp306,ivec84,dvec84,dpos84,vp84,ivec80,dvec80,dpos80,vp80⟩

private def bk395 : BoundKit false :=
  ⟨395,eb395,indexOk395.1,indexOk395.2,lookup395,rfl,threshold395,
   n12,250,pos12,cp12,ivec5,dvec5,dpos5,vp5,ivec6,dvec6,dpos6,vp6⟩

private def bk396 : BoundKit false :=
  ⟨396,eb396,indexOk396.1,indexOk396.2,lookup396,rfl,threshold396,
   n52,15174291,pos52,cp52,ivec14,dvec14,dpos14,vp14,ivec15,dvec15,dpos15,vp15⟩

private def bk397 : BoundKit false :=
  ⟨397,eb397,indexOk397.1,indexOk397.2,lookup397,rfl,threshold397,
   n56,7968235,pos56,cp56,ivec14,dvec14,dpos14,vp14,ivec18,dvec18,dpos18,vp18⟩

private def bk398 : BoundKit false :=
  ⟨398,eb398,indexOk398.1,indexOk398.2,lookup398,rfl,threshold398,
   n62,197265783,pos62,cp62,ivec19,dvec19,dpos19,vp19,ivec15,dvec15,dpos15,vp15⟩

private def bk399 : BoundKit true :=
  ⟨399,eb399,indexOk399.1,indexOk399.2,lookup399,rfl,threshold399,
   n65,922502,pos65,cp65,ivec23,dvec23,dpos23,vp23,ivec22,dvec22,dpos22,vp22⟩

private def bk402 : BoundKit true :=
  ⟨402,eb402,indexOk402.1,indexOk402.2,lookup402,rfl,threshold402,
   n69,46454565,pos69,cp69,ivec23,dvec23,dpos23,vp23,ivec24,dvec24,dpos24,vp24⟩

private def bk403 : BoundKit true :=
  ⟨403,eb403,indexOk403.1,indexOk403.2,lookup403,rfl,threshold403,
   n78,1841406,pos78,cp78,ivec26,dvec26,dpos26,vp26,ivec25,dvec25,dpos25,vp25⟩

private def bk404 : BoundKit true :=
  ⟨404,eb404,indexOk404.1,indexOk404.2,lookup404,rfl,threshold404,
   n71,1315290,pos71,cp71,ivec26,dvec26,dpos26,vp26,ivec25,dvec25,dpos25,vp25⟩

private def bk405 : BoundKit true :=
  ⟨405,eb405,indexOk405.1,indexOk405.2,lookup405,rfl,threshold405,
   n79,510,pos79,cp79,ivec1,dvec1,dpos1,vp1,ivec4,dvec4,dpos4,vp4⟩

private def bk406 : BoundKit true :=
  ⟨406,eb406,indexOk406.1,indexOk406.2,lookup406,rfl,threshold406,
   n74,77757764,pos74,cp74,ivec27,dvec27,dpos27,vp27,ivec22,dvec22,dpos22,vp22⟩

private def bk408 : BoundKit true :=
  ⟨408,eb408,indexOk408.1,indexOk408.2,lookup408,rfl,threshold408,
   n76,10727197,pos76,cp76,ivec29,dvec29,dpos29,vp29,ivec28,dvec28,dpos28,vp28⟩

private def bk411 : BoundKit true :=
  ⟨411,eb411,indexOk411.1,indexOk411.2,lookup411,rfl,threshold411,
   n80,1064531,pos80,cp80,ivec31,dvec31,dpos31,vp31,ivec30,dvec30,dpos30,vp30⟩

private def bk412 : BoundKit false :=
  ⟨412,eb412,indexOk412.1,indexOk412.2,lookup412,rfl,threshold412,
   n81,85,pos81,cp81,ivec1,dvec1,dpos1,vp1,ivec9,dvec9,dpos9,vp9⟩

private def bk414 : BoundKit false :=
  ⟨414,eb414,indexOk414.1,indexOk414.2,lookup414,rfl,threshold414,
   n85,458430,pos85,cp85,ivec32,dvec32,dpos32,vp32,ivec33,dvec33,dpos33,vp33⟩

private def bk415 : BoundKit true :=
  ⟨415,eb415,indexOk415.1,indexOk415.2,lookup415,rfl,threshold415,
   n81,85,pos81,cp81,ivec1,dvec1,dpos1,vp1,ivec9,dvec9,dpos9,vp9⟩

private def bk416 : BoundKit true :=
  ⟨416,eb416,indexOk416.1,indexOk416.2,lookup416,rfl,threshold416,
   n88,167131367,pos88,cp88,ivec31,dvec31,dpos31,vp31,ivec34,dvec34,dpos34,vp34⟩

private def bk419 : BoundKit true :=
  ⟨419,eb419,indexOk419.1,indexOk419.2,lookup419,rfl,threshold419,
   n100,7770,pos100,cp100,ivec8,dvec8,dpos8,vp8,ivec7,dvec7,dpos7,vp7⟩

private def bk420 : BoundKit true :=
  ⟨420,eb420,indexOk420.1,indexOk420.2,lookup420,rfl,threshold420,
   n90,128644477,pos90,cp90,ivec35,dvec35,dpos35,vp35,ivec30,dvec30,dpos30,vp30⟩

private def bk422 : BoundKit false :=
  ⟨422,eb422,indexOk422.1,indexOk422.2,lookup422,rfl,threshold422,
   n92,867613,pos92,cp92,ivec36,dvec36,dpos36,vp36,ivec37,dvec37,dpos37,vp37⟩

private def bk424 : BoundKit true :=
  ⟨424,eb424,indexOk424.1,indexOk424.2,lookup424,rfl,threshold424,
   n94,4214,pos94,cp94,ivec39,dvec39,dpos39,vp39,ivec38,dvec38,dpos38,vp38⟩

private def bk425 : BoundKit false :=
  ⟨425,eb425,indexOk425.1,indexOk425.2,lookup425,rfl,threshold425,
   n95,22604836,pos95,cp95,ivec36,dvec36,dpos36,vp36,ivec40,dvec40,dpos40,vp40⟩

private def bk426 : BoundKit true :=
  ⟨426,eb426,indexOk426.1,indexOk426.2,lookup426,rfl,threshold426,
   n99,2150,pos99,cp99,ivec39,dvec39,dpos39,vp39,ivec38,dvec38,dpos38,vp38⟩

private def bk427 : BoundKit false :=
  ⟨427,eb427,indexOk427.1,indexOk427.2,lookup427,rfl,threshold427,
   n101,2796719,pos101,cp101,ivec41,dvec41,dpos41,vp41,ivec37,dvec37,dpos37,vp37⟩

private def bk431 : BoundKit true :=
  ⟨431,eb431,indexOk431.1,indexOk431.2,lookup431,rfl,threshold431,
   n103,1841406,pos103,cp103,ivec26,dvec26,dpos26,vp26,ivec42,dvec42,dpos42,vp42⟩

private def bk432 : BoundKit false :=
  ⟨432,eb432,indexOk432.1,indexOk432.2,lookup432,rfl,threshold432,
   n104,33907254,pos104,cp104,ivec36,dvec36,dpos36,vp36,ivec43,dvec43,dpos43,vp43⟩

private def bk433 : BoundKit false :=
  ⟨433,eb433,indexOk433.1,indexOk433.2,lookup433,rfl,threshold433,
   n107,465908181,pos107,cp107,ivec36,dvec36,dpos36,vp36,ivec44,dvec44,dpos44,vp44⟩

private def bk434 : BoundKit false :=
  ⟨434,eb434,indexOk434.1,indexOk434.2,lookup434,rfl,threshold434,
   n108,473628142,pos108,cp108,ivec41,dvec41,dpos41,vp41,ivec43,dvec43,dpos43,vp43⟩

private def bk435 : BoundKit true :=
  ⟨435,eb435,indexOk435.1,indexOk435.2,lookup435,rfl,threshold435,
   n109,6576450,pos109,cp109,ivec26,dvec26,dpos26,vp26,ivec42,dvec42,dpos42,vp42⟩

private def bk436 : BoundKit true :=
  ⟨436,eb436,indexOk436.1,indexOk436.2,lookup436,rfl,threshold436,
   n110,510,pos110,cp110,ivec1,dvec1,dpos1,vp1,ivec46,dvec46,dpos46,vp46⟩

private def bk437 : BoundKit false :=
  ⟨437,eb437,indexOk437.1,indexOk437.2,lookup437,rfl,threshold437,
   n111,36565583,pos111,cp111,ivec45,dvec45,dpos45,vp45,ivec37,dvec37,dpos37,vp37⟩

private def bk439 : BoundKit false :=
  ⟨439,eb439,indexOk439.1,indexOk439.2,lookup439,rfl,threshold439,
   n113,476340838,pos113,cp113,ivec45,dvec45,dpos45,vp45,ivec40,dvec40,dpos40,vp40⟩

private def bk440 : BoundKit false :=
  ⟨440,eb440,indexOk440.1,indexOk440.2,lookup440,rfl,threshold440,
   n114,117867829,pos114,cp114,ivec47,dvec47,dpos47,vp47,ivec37,dvec37,dpos37,vp37⟩

private def bk441 : BoundKit true :=
  ⟨441,eb441,indexOk441.1,indexOk441.2,lookup441,rfl,threshold441,
   n115,10727197,pos115,cp115,ivec29,dvec29,dpos29,vp29,ivec48,dvec48,dpos48,vp48⟩

private def bk443 : BoundKit true :=
  ⟨443,eb443,indexOk443.1,indexOk443.2,lookup443,rfl,threshold443,
   n117,170,pos117,cp117,ivec1,dvec1,dpos1,vp1,ivec10,dvec10,dpos10,vp10⟩

private def bk446 : BoundKit false :=
  ⟨446,eb446,indexOk446.1,indexOk446.2,lookup446,rfl,threshold446,
   n118,349762,pos118,cp118,ivec39,dvec39,dpos39,vp39,ivec49,dvec49,dpos49,vp49⟩

private def bk447 : BoundKit false :=
  ⟨447,eb447,indexOk447.1,indexOk447.2,lookup447,rfl,threshold447,
   n161,4690,pos161,cp161,ivec65,dvec65,dpos65,vp65,ivec9,dvec9,dpos9,vp9⟩

private def bk449 : BoundKit false :=
  ⟨449,eb449,indexOk449.1,indexOk449.2,lookup449,rfl,threshold449,
   n124,5135331,pos124,cp124,ivec36,dvec36,dpos36,vp36,ivec51,dvec51,dpos51,vp51⟩

private def bk450 : BoundKit false :=
  ⟨450,eb450,indexOk450.1,indexOk450.2,lookup450,rfl,threshold450,
   n120,32359620,pos120,cp120,ivec36,dvec36,dpos36,vp36,ivec50,dvec50,dpos50,vp50⟩

private def bk452 : BoundKit true :=
  ⟨452,eb452,indexOk452.1,indexOk452.2,lookup452,rfl,threshold452,
   n123,7138,pos123,cp123,ivec39,dvec39,dpos39,vp39,ivec49,dvec49,dpos49,vp49⟩

private def bk454 : BoundKit false :=
  ⟨454,eb454,indexOk454.1,indexOk454.2,lookup454,rfl,threshold454,
   n125,215196189,pos125,cp125,ivec41,dvec41,dpos41,vp41,ivec51,dvec51,dpos51,vp51⟩

private def bk455 : BoundKit false :=
  ⟨455,eb455,indexOk455.1,indexOk455.2,lookup455,rfl,threshold455,
   n123,7138,pos123,cp123,ivec39,dvec39,dpos39,vp39,ivec49,dvec49,dpos49,vp49⟩

private def bk456 : BoundKit true :=
  ⟨456,eb456,indexOk456.1,indexOk456.2,lookup456,rfl,threshold456,
   n126,2590,pos126,cp126,ivec8,dvec8,dpos8,vp8,ivec9,dvec9,dpos9,vp9⟩

private def bk457 : BoundKit true :=
  ⟨457,eb457,indexOk457.1,indexOk457.2,lookup457,rfl,threshold457,
   n127,163774,pos127,cp127,ivec31,dvec31,dpos31,vp31,ivec48,dvec48,dpos48,vp48⟩

private def bk460 : BoundKit true :=
  ⟨460,eb460,indexOk460.1,indexOk460.2,lookup460,rfl,threshold460,
   n128,167131367,pos128,cp128,ivec31,dvec31,dpos31,vp31,ivec52,dvec52,dpos52,vp52⟩

private def bk461 : BoundKit true :=
  ⟨461,eb461,indexOk461.1,indexOk461.2,lookup461,rfl,threshold461,
   n141,229215,pos141,cp141,ivec32,dvec32,dpos32,vp32,ivec42,dvec42,dpos42,vp42⟩

private def bk462 : BoundKit true :=
  ⟨462,eb462,indexOk462.1,indexOk462.2,lookup462,rfl,threshold462,
   n145,818625,pos145,cp145,ivec32,dvec32,dpos32,vp32,ivec42,dvec42,dpos42,vp42⟩

private def bk463 : BoundKit true :=
  ⟨463,eb463,indexOk463.1,indexOk463.2,lookup463,rfl,threshold463,
   n146,3885,pos146,cp146,ivec8,dvec8,dpos8,vp8,ivec46,dvec46,dpos46,vp46⟩

private def bk464 : BoundKit true :=
  ⟨464,eb464,indexOk464.1,indexOk464.2,lookup464,rfl,threshold464,
   n129,128644477,pos129,cp129,ivec35,dvec35,dpos35,vp35,ivec48,dvec48,dpos48,vp48⟩

private def bk466 : BoundKit false :=
  ⟨466,eb466,indexOk466.1,indexOk466.2,lookup466,rfl,threshold466,
   n130,39923,pos130,cp130,ivec53,dvec53,dpos53,vp53,ivec37,dvec37,dpos37,vp37⟩

private def bk468 : BoundKit false :=
  ⟨468,eb468,indexOk468.1,indexOk468.2,lookup468,rfl,threshold468,
   n134,520078,pos134,cp134,ivec53,dvec53,dpos53,vp53,ivec40,dvec40,dpos40,vp40⟩

private def bk469 : BoundKit true :=
  ⟨469,eb469,indexOk469.1,indexOk469.2,lookup469,rfl,threshold469,
   n137,12314,pos137,cp137,ivec11,dvec11,dpos11,vp11,ivec56,dvec56,dpos56,vp56⟩

private def bk470 : BoundKit false :=
  ⟨470,eb470,indexOk470.1,indexOk470.2,lookup470,rfl,threshold470,
   n138,68783,pos138,cp138,ivec55,dvec55,dpos55,vp55,ivec37,dvec37,dpos37,vp37⟩

private def bk471 : BoundKit false :=
  ⟨471,eb471,indexOk471.1,indexOk471.2,lookup471,rfl,threshold471,
   n142,10141521,pos142,cp142,ivec53,dvec53,dpos53,vp53,ivec43,dvec43,dpos43,vp43⟩

private def bk472 : BoundKit false :=
  ⟨472,eb472,indexOk472.1,indexOk472.2,lookup472,rfl,threshold472,
   n143,278702463,pos143,cp143,ivec53,dvec53,dpos53,vp53,ivec44,dvec44,dpos44,vp44⟩

private def bk473 : BoundKit false :=
  ⟨473,eb473,indexOk473.1,indexOk473.2,lookup473,rfl,threshold473,
   n144,896038,pos144,cp144,ivec55,dvec55,dpos55,vp55,ivec43,dvec43,dpos43,vp43⟩

private def bk474 : BoundKit false :=
  ⟨474,eb474,indexOk474.1,indexOk474.2,lookup474,rfl,threshold474,
   n147,4824541,pos147,cp147,ivec57,dvec57,dpos57,vp57,ivec37,dvec37,dpos37,vp37⟩

private def bk475 : BoundKit false :=
  ⟨475,eb475,indexOk475.1,indexOk475.2,lookup475,rfl,threshold475,
   n148,125698852,pos148,cp148,ivec57,dvec57,dpos57,vp57,ivec40,dvec40,dpos40,vp40⟩

private def bk476 : BoundKit false :=
  ⟨476,eb476,indexOk476.1,indexOk476.2,lookup476,rfl,threshold476,
   n149,108058093,pos149,cp149,ivec58,dvec58,dpos58,vp58,ivec37,dvec37,dpos37,vp37⟩

private def bk477 : BoundKit true :=
  ⟨477,eb477,indexOk477.1,indexOk477.2,lookup477,rfl,threshold477,
   n150,1510223,pos150,cp150,ivec60,dvec60,dpos60,vp60,ivec30,dvec30,dpos30,vp30⟩

private def bk478 : BoundKit true :=
  ⟨478,eb478,indexOk478.1,indexOk478.2,lookup478,rfl,threshold478,
   n154,18238847,pos154,cp154,ivec60,dvec60,dpos60,vp60,ivec61,dvec61,dpos61,vp61⟩

private def bk479 : BoundKit true :=
  ⟨479,eb479,indexOk479.1,indexOk479.2,lookup479,rfl,threshold479,
   n155,4868149,pos155,cp155,ivec62,dvec62,dpos62,vp62,ivec30,dvec30,dpos30,vp30⟩

private def bk480 : BoundKit true :=
  ⟨480,eb480,indexOk480.1,indexOk480.2,lookup480,rfl,threshold480,
   n156,54716541,pos156,cp156,ivec60,dvec60,dpos60,vp60,ivec34,dvec34,dpos34,vp34⟩

private def bk481 : BoundKit true :=
  ⟨481,eb481,indexOk481.1,indexOk481.2,lookup481,rfl,threshold481,
   n157,74581782,pos157,cp157,ivec60,dvec60,dpos60,vp60,ivec64,dvec64,dpos64,vp64⟩

private def bk482 : BoundKit true :=
  ⟨482,eb482,indexOk482.1,indexOk482.2,lookup482,rfl,threshold482,
   n160,764299393,pos160,cp160,ivec62,dvec62,dpos62,vp62,ivec34,dvec34,dpos34,vp34⟩

private def bk483 : BoundKit true :=
  ⟨483,eb483,indexOk483.1,indexOk483.2,lookup483,rfl,threshold483,
   n163,22704539,pos163,cp163,ivec66,dvec66,dpos66,vp66,ivec30,dvec30,dpos30,vp30⟩

private def bk484 : BoundKit true :=
  ⟨484,eb484,indexOk484.1,indexOk484.2,lookup484,rfl,threshold484,
   n165,274200971,pos165,cp165,ivec66,dvec66,dpos66,vp66,ivec61,dvec61,dpos61,vp61⟩

private def bk485 : BoundKit true :=
  ⟨485,eb485,indexOk485.1,indexOk485.2,lookup485,rfl,threshold485,
   n167,73187257,pos167,cp167,ivec67,dvec67,dpos67,vp67,ivec30,dvec30,dpos30,vp30⟩

private def bk486 : BoundKit false :=
  ⟨486,eb486,indexOk486.1,indexOk486.2,lookup486,rfl,threshold486,
   n169,2693670,pos169,cp169,ivec68,dvec68,dpos68,vp68,ivec33,dvec33,dpos33,vp33⟩

private def bk487 : BoundKit false :=
  ⟨487,eb487,indexOk487.1,indexOk487.2,lookup487,rfl,threshold487,
   n175,178770,pos175,cp175,ivec71,dvec71,dpos71,vp71,ivec7,dvec7,dpos7,vp7⟩

private def bk488 : BoundKit true :=
  ⟨488,eb488,indexOk488.1,indexOk488.2,lookup488,rfl,threshold488,
   n174,55863897,pos174,cp174,ivec69,dvec69,dpos69,vp69,ivec34,dvec34,dpos34,vp34⟩

private def bk490 : BoundKit true :=
  ⟨490,eb490,indexOk490.1,indexOk490.2,lookup490,rfl,threshold490,
   n177,76145694,pos177,cp177,ivec69,dvec69,dpos69,vp69,ivec64,dvec64,dpos64,vp64⟩

private def bk491 : BoundKit true :=
  ⟨491,eb491,indexOk491.1,indexOk491.2,lookup491,rfl,threshold491,
   n179,417072227,pos179,cp179,ivec70,dvec70,dpos70,vp70,ivec34,dvec34,dpos34,vp34⟩

private def bk494 : BoundKit true :=
  ⟨494,eb494,indexOk494.1,indexOk494.2,lookup494,rfl,threshold494,
   n181,50713,pos181,cp181,ivec72,dvec72,dpos72,vp72,ivec30,dvec30,dpos30,vp30⟩

private def bk495 : BoundKit false :=
  ⟨495,eb495,indexOk495.1,indexOk495.2,lookup495,rfl,threshold495,
   n182,9620250,pos182,cp182,ivec68,dvec68,dpos68,vp68,ivec33,dvec33,dpos33,vp33⟩

private def bk496 : BoundKit true :=
  ⟨496,eb496,indexOk496.1,indexOk496.2,lookup496,rfl,threshold496,
   n184,86968894,pos184,cp184,ivec72,dvec72,dpos72,vp72,ivec61,dvec61,dpos61,vp61⟩

private def bk497 : BoundKit true :=
  ⟨497,eb497,indexOk497.1,indexOk497.2,lookup497,rfl,threshold497,
   n185,1135849,pos185,cp185,ivec73,dvec73,dpos73,vp73,ivec30,dvec30,dpos30,vp30⟩

private def bk498 : BoundKit false :=
  ⟨498,eb498,indexOk498.1,indexOk498.2,lookup498,rfl,threshold498,
   n187,495541,pos187,cp187,ivec74,dvec74,dpos74,vp74,ivec37,dvec37,dpos37,vp37⟩

private def bk499 : BoundKit false :=
  ⟨499,eb499,indexOk499.1,indexOk499.2,lookup499,rfl,threshold499,
   n190,12910852,pos190,cp190,ivec74,dvec74,dpos74,vp74,ivec40,dvec40,dpos40,vp40⟩

private def bk500 : BoundKit false :=
  ⟨500,eb500,indexOk500.1,indexOk500.2,lookup500,rfl,threshold500,
   n194,18234599,pos194,cp194,ivec76,dvec76,dpos76,vp76,ivec37,dvec37,dpos37,vp37⟩

private def bk501 : BoundKit false :=
  ⟨501,eb501,indexOk501.1,indexOk501.2,lookup501,rfl,threshold501,
   n197,6455426,pos197,cp197,ivec74,dvec74,dpos74,vp74,ivec43,dvec43,dpos43,vp43⟩

private def bk502 : BoundKit false :=
  ⟨502,eb502,indexOk502.1,indexOk502.2,lookup502,rfl,threshold502,
   n198,266105517,pos198,cp198,ivec74,dvec74,dpos74,vp74,ivec44,dvec44,dpos44,vp44⟩

private def bk503 : BoundKit false :=
  ⟨503,eb503,indexOk503.1,indexOk503.2,lookup503,rfl,threshold503,
   n199,118771307,pos199,cp199,ivec76,dvec76,dpos76,vp76,ivec43,dvec43,dpos43,vp43⟩

private def bk504 : BoundKit false :=
  ⟨504,eb504,indexOk504.1,indexOk504.2,lookup504,rfl,threshold504,
   n202,7449913,pos202,cp202,ivec77,dvec77,dpos77,vp77,ivec37,dvec37,dpos37,vp37⟩

private def bk505 : BoundKit false :=
  ⟨505,eb505,indexOk505.1,indexOk505.2,lookup505,rfl,threshold505,
   n203,194100436,pos203,cp203,ivec77,dvec77,dpos77,vp77,ivec40,dvec40,dpos40,vp40⟩

private def bk506 : BoundKit false :=
  ⟨506,eb506,indexOk506.1,indexOk506.2,lookup506,rfl,threshold506,
   n204,274137107,pos204,cp204,ivec78,dvec78,dpos78,vp78,ivec37,dvec37,dpos37,vp37⟩

private def bk507 : BoundKit true :=
  ⟨507,eb507,indexOk507.1,indexOk507.2,lookup507,rfl,threshold507,
   n205,63661,pos205,cp205,ivec79,dvec79,dpos79,vp79,ivec48,dvec48,dpos48,vp48⟩

private def bk510 : BoundKit true :=
  ⟨510,eb510,indexOk510.1,indexOk510.2,lookup510,rfl,threshold510,
   n206,580027,pos206,cp206,ivec54,dvec54,dpos54,vp54,ivec80,dvec80,dpos80,vp80⟩

private def bk512 : BoundKit true :=
  ⟨512,eb512,indexOk512.1,indexOk512.2,lookup512,rfl,threshold512,
   n208,414305,pos208,cp208,ivec54,dvec54,dpos54,vp54,ivec80,dvec80,dpos80,vp80⟩

private def bk513 : BoundKit true :=
  ⟨513,eb513,indexOk513.1,indexOk513.2,lookup513,rfl,threshold513,
   n209,6157,pos209,cp209,ivec11,dvec11,dpos11,vp11,ivec10,dvec10,dpos10,vp10⟩

private def bk516 : BoundKit true :=
  ⟨516,eb516,indexOk516.1,indexOk516.2,lookup516,rfl,threshold516,
   n210,2306487,pos210,cp210,ivec79,dvec79,dpos79,vp79,ivec52,dvec52,dpos52,vp52⟩

private def bk519 : BoundKit true :=
  ⟨519,eb519,indexOk519.1,indexOk519.2,lookup519,rfl,threshold519,
   n211,957073,pos211,cp211,ivec81,dvec81,dpos81,vp81,ivec48,dvec48,dpos48,vp48⟩

private def bk522 : BoundKit false :=
  ⟨522,eb522,indexOk522.1,indexOk522.2,lookup522,rfl,threshold522,
   n212,32263737,pos212,cp212,ivec74,dvec74,dpos74,vp74,ivec51,dvec51,dpos51,vp51⟩

private def bk523 : BoundKit false :=
  ⟨523,eb523,indexOk523.1,indexOk523.2,lookup523,rfl,threshold523,
   n213,67768580,pos213,cp213,ivec74,dvec74,dpos74,vp74,ivec50,dvec50,dpos50,vp50⟩

private def bk524 : BoundKit false :=
  ⟨524,eb524,indexOk524.1,indexOk524.2,lookup524,rfl,threshold524,
   n214,1187220243,pos214,cp214,ivec76,dvec76,dpos76,vp76,ivec51,dvec51,dpos51,vp51⟩

private def bk525 : BoundKit true :=
  ⟨525,eb525,indexOk525.1,indexOk525.2,lookup525,rfl,threshold525,
   n215,1541891,pos215,cp215,ivec69,dvec69,dpos69,vp69,ivec48,dvec48,dpos48,vp48⟩

private def bk526 : BoundKit false :=
  ⟨526,eb526,indexOk526.1,indexOk526.2,lookup526,rfl,threshold526,
   n216,1346835,pos216,cp216,ivec68,dvec68,dpos68,vp68,ivec42,dvec42,dpos42,vp42⟩

private def bk527 : BoundKit true :=
  ⟨527,eb527,indexOk527.1,indexOk527.2,lookup527,rfl,threshold527,
   n217,18621299,pos217,cp217,ivec69,dvec69,dpos69,vp69,ivec82,dvec82,dpos82,vp82⟩

private def bk528 : BoundKit true :=
  ⟨528,eb528,indexOk528.1,indexOk528.2,lookup528,rfl,threshold528,
   n219,69069286,pos219,cp219,ivec70,dvec70,dpos70,vp70,ivec48,dvec48,dpos48,vp48⟩

private def bk529 : BoundKit true :=
  ⟨529,eb529,indexOk529.1,indexOk529.2,lookup529,rfl,threshold529,
   n220,55863897,pos220,cp220,ivec69,dvec69,dpos69,vp69,ivec52,dvec52,dpos52,vp52⟩

private def bk531 : BoundKit true :=
  ⟨531,eb531,indexOk531.1,indexOk531.2,lookup531,rfl,threshold531,
   n222,38072847,pos222,cp222,ivec69,dvec69,dpos69,vp69,ivec83,dvec83,dpos83,vp83⟩

private def bk532 : BoundKit true :=
  ⟨532,eb532,indexOk532.1,indexOk532.2,lookup532,rfl,threshold532,
   n223,417072227,pos223,cp223,ivec70,dvec70,dpos70,vp70,ivec52,dvec52,dpos52,vp52⟩

private def bk533 : BoundKit true :=
  ⟨533,eb533,indexOk533.1,indexOk533.2,lookup533,rfl,threshold533,
   n225,4810125,pos225,cp225,ivec68,dvec68,dpos68,vp68,ivec42,dvec42,dpos42,vp42⟩

private def bk534 : BoundKit true :=
  ⟨534,eb534,indexOk534.1,indexOk534.2,lookup534,rfl,threshold534,
   n224,7201246,pos224,cp224,ivec72,dvec72,dpos72,vp72,ivec48,dvec48,dpos48,vp48⟩

private def bk535 : BoundKit false :=
  ⟨535,eb535,indexOk535.1,indexOk535.2,lookup535,rfl,threshold535,
   n225,4810125,pos225,cp225,ivec68,dvec68,dpos68,vp68,ivec42,dvec42,dpos42,vp42⟩

private def bk536 : BoundKit true :=
  ⟨536,eb536,indexOk536.1,indexOk536.2,lookup536,rfl,threshold536,
   n226,43484447,pos226,cp226,ivec72,dvec72,dpos72,vp72,ivec82,dvec82,dpos82,vp82⟩

private def bk537 : BoundKit true :=
  ⟨537,eb537,indexOk537.1,indexOk537.2,lookup537,rfl,threshold537,
   n227,80645279,pos227,cp227,ivec73,dvec73,dpos73,vp73,ivec48,dvec48,dpos48,vp48⟩

private def bk538 : BoundKit false :=
  ⟨538,eb538,indexOk538.1,indexOk538.2,lookup538,rfl,threshold538,
   n228,21903658,pos228,cp228,ivec84,dvec84,dpos84,vp84,ivec49,dvec49,dpos49,vp49⟩

private def bk539 : BoundKit false :=
  ⟨539,eb539,indexOk539.1,indexOk539.2,lookup539,rfl,threshold539,
   n230,9478,pos230,cp230,ivec13,dvec13,dpos13,vp13,ivec9,dvec9,dpos9,vp9⟩

private def bk540 : BoundKit false :=
  ⟨540,eb540,indexOk540.1,indexOk540.2,lookup540,rfl,threshold540,
   n231,11144771,pos231,cp231,ivec85,dvec85,dpos85,vp85,ivec86,dvec86,dpos86,vp86⟩

private def bk545 : BoundKit false :=
  ⟨545,eb545,indexOk545.1,indexOk545.2,lookup545,rfl,threshold545,
   n234,3129094,pos234,cp234,ivec84,dvec84,dpos84,vp84,ivec49,dvec49,dpos49,vp49⟩

private def bk547 : BoundKit false :=
  ⟨547,eb547,indexOk547.1,indexOk547.2,lookup547,rfl,threshold547,
   n233,26342186,pos233,cp233,ivec85,dvec85,dpos85,vp85,ivec87,dvec87,dpos87,vp87⟩

private def bk550 : BoundKit false :=
  ⟨550,eb550,indexOk550.1,indexOk550.2,lookup550,rfl,threshold550,
   n235,366553,pos235,cp235,ivec88,dvec88,dpos88,vp88,ivec86,dvec86,dpos86,vp86⟩

private def bk553 : BoundKit true :=
  ⟨553,eb553,indexOk553.1,indexOk553.2,lookup553,rfl,threshold553,
   n236,200296174,pos236,cp236,ivec89,dvec89,dpos89,vp89,ivec48,dvec48,dpos48,vp48⟩

private def bk554 : BoundKit true :=
  ⟨554,eb554,indexOk554.1,indexOk554.2,lookup554,rfl,threshold554,
   n239,1209480743,pos239,cp239,ivec89,dvec89,dpos89,vp89,ivec82,dvec82,dpos82,vp82⟩

private def bk555 : BoundKit true :=
  ⟨555,eb555,indexOk555.1,indexOk555.2,lookup555,rfl,threshold555,
   n241,3685184893,pos241,cp241,ivec90,dvec90,dpos90,vp90,ivec48,dvec48,dpos48,vp48⟩

private def bk556 : BoundKit false :=
  ⟨556,eb556,indexOk556.1,indexOk556.2,lookup556,rfl,threshold556,
   n242,221882259,pos242,cp242,ivec85,dvec85,dpos85,vp85,ivec51,dvec51,dpos51,vp51⟩

private def bk557 : BoundKit false :=
  ⟨557,eb557,indexOk557.1,indexOk557.2,lookup557,rfl,threshold557,
   n243,466054060,pos243,cp243,ivec85,dvec85,dpos85,vp85,ivec50,dvec50,dpos50,vp50⟩

private def bk558 : BoundKit false :=
  ⟨558,eb558,indexOk558.1,indexOk558.2,lookup558,rfl,threshold558,
   n244,773927823,pos244,cp244,ivec91,dvec91,dpos91,vp91,ivec51,dvec51,dpos51,vp51⟩

private def bk559 : BoundKit false :=
  ⟨559,eb559,indexOk559.1,indexOk559.2,lookup559,rfl,threshold559,
   n248,29526,pos248,cp248,ivec92,dvec92,dpos92,vp92,ivec93,dvec93,dpos93,vp93⟩

private def bk560 : BoundKit false :=
  ⟨560,eb560,indexOk560.1,indexOk560.2,lookup560,rfl,threshold560,
   n249,539327,pos249,cp249,ivec36,dvec36,dpos36,vp36,ivec94,dvec94,dpos94,vp94⟩

private def bk564 : BoundKit true :=
  ⟨564,eb564,indexOk564.1,indexOk564.2,lookup564,rfl,threshold564,
   n250,2345,pos250,cp250,ivec65,dvec65,dpos65,vp65,ivec4,dvec4,dpos4,vp4⟩

private def bk567 : BoundKit true :=
  ⟨567,eb567,indexOk567.1,indexOk567.2,lookup567,rfl,threshold567,
   n251,349762,pos251,cp251,ivec39,dvec39,dpos39,vp39,ivec95,dvec95,dpos95,vp95⟩

private def bk568 : BoundKit false :=
  ⟨568,eb568,indexOk568.1,indexOk568.2,lookup568,rfl,threshold568,
   n252,3423554,pos252,cp252,ivec36,dvec36,dpos36,vp36,ivec96,dvec96,dpos96,vp96⟩

private def bk569 : BoundKit true :=
  ⟨569,eb569,indexOk569.1,indexOk569.2,lookup569,rfl,threshold569,
   n255,178450,pos255,cp255,ivec39,dvec39,dpos39,vp39,ivec95,dvec95,dpos95,vp95⟩

private def bk570 : BoundKit true :=
  ⟨570,eb570,indexOk570.1,indexOk570.2,lookup570,rfl,threshold570,
   n256,4690,pos256,cp256,ivec65,dvec65,dpos65,vp65,ivec97,dvec97,dpos97,vp97⟩

private def bk571 : BoundKit false :=
  ⟨571,eb571,indexOk571.1,indexOk571.2,lookup571,rfl,threshold571,
   n257,22600513,pos257,cp257,ivec41,dvec41,dpos41,vp41,ivec94,dvec94,dpos94,vp94⟩

private def bk573 : BoundKit false :=
  ⟨573,eb573,indexOk573.1,indexOk573.2,lookup573,rfl,threshold573,
   n259,16953627,pos259,cp259,ivec36,dvec36,dpos36,vp36,ivec98,dvec98,dpos98,vp98⟩

private def bk575 : BoundKit false :=
  ⟨575,eb575,indexOk575.1,indexOk575.2,lookup575,rfl,threshold575,
   n260,10786540,pos260,cp260,ivec36,dvec36,dpos36,vp36,ivec99,dvec99,dpos99,vp99⟩

private def bk576 : BoundKit false :=
  ⟨576,eb576,indexOk576.1,indexOk576.2,lookup576,rfl,threshold576,
   n261,236814071,pos261,cp261,ivec41,dvec41,dpos41,vp41,ivec98,dvec98,dpos98,vp98⟩

private def bk577 : BoundKit true :=
  ⟨577,eb577,indexOk577.1,indexOk577.2,lookup577,rfl,threshold577,
   n262,6576450,pos262,cp262,ivec26,dvec26,dpos26,vp26,ivec33,dvec33,dpos33,vp33⟩

private def bk578 : BoundKit true :=
  ⟨578,eb578,indexOk578.1,indexOk578.2,lookup578,rfl,threshold578,
   n263,510,pos263,cp263,ivec1,dvec1,dpos1,vp1,ivec7,dvec7,dpos7,vp7⟩

private def bk579 : BoundKit false :=
  ⟨579,eb579,indexOk579.1,indexOk579.2,lookup579,rfl,threshold579,
   n264,22729957,pos264,cp264,ivec45,dvec45,dpos45,vp45,ivec94,dvec94,dpos94,vp94⟩

private def bk581 : BoundKit false :=
  ⟨581,eb581,indexOk581.1,indexOk581.2,lookup581,rfl,threshold581,
   n265,72142907,pos265,cp265,ivec45,dvec45,dpos45,vp45,ivec96,dvec96,dpos96,vp96⟩

private def bk582 : BoundKit false :=
  ⟨582,eb582,indexOk582.1,indexOk582.2,lookup582,rfl,threshold582,
   n266,952499483,pos266,cp266,ivec47,dvec47,dpos47,vp47,ivec94,dvec94,dpos94,vp94⟩

private def bk583 : BoundKit true :=
  ⟨583,eb583,indexOk583.1,indexOk583.2,lookup583,rfl,threshold583,
   n267,53963533,pos267,cp267,ivec101,dvec101,dpos101,vp101,ivec28,dvec28,dpos28,vp28⟩

private def bk584 : BoundKit false :=
  ⟨584,eb584,indexOk584.1,indexOk584.2,lookup584,rfl,threshold584,
   n268,1807526,pos268,cp268,ivec100,dvec100,dpos100,vp100,ivec25,dvec25,dpos25,vp25⟩

private def bk585 : BoundKit false :=
  ⟨585,eb585,indexOk585.1,indexOk585.2,lookup585,rfl,threshold585,
   n272,84286,pos272,cp272,ivec102,dvec102,dpos102,vp102,ivec4,dvec4,dpos4,vp4⟩

private def bk586 : BoundKit true :=
  ⟨586,eb586,indexOk586.1,indexOk586.2,lookup586,rfl,threshold586,
   n271,651713437,pos271,cp271,ivec101,dvec101,dpos101,vp101,ivec103,dvec103,dpos103,vp103⟩

private def bk590 : BoundKit true :=
  ⟨590,eb590,indexOk590.1,indexOk590.2,lookup590,rfl,threshold590,
   n274,1666646111,pos274,cp274,ivec104,dvec104,dpos104,vp104,ivec28,dvec28,dpos28,vp28⟩

private def bk591 : BoundKit false :=
  ⟨591,eb591,indexOk591.1,indexOk591.2,lookup591,rfl,threshold591,
   n275,1291090,pos275,cp275,ivec100,dvec100,dpos100,vp100,ivec25,dvec25,dpos25,vp25⟩

private def bk592 : BoundKit true :=
  ⟨592,eb592,indexOk592.1,indexOk592.2,lookup592,rfl,threshold592,
   n277,4600479,pos277,cp277,ivec105,dvec105,dpos105,vp105,ivec28,dvec28,dpos28,vp28⟩

private def bk595 : BoundKit true :=
  ⟨595,eb595,indexOk595.1,indexOk595.2,lookup595,rfl,threshold595,
   n278,55559631,pos278,cp278,ivec105,dvec105,dpos105,vp105,ivec103,dvec103,dpos103,vp103⟩

private def bk598 : BoundKit true :=
  ⟨598,eb598,indexOk598.1,indexOk598.2,lookup598,rfl,threshold598,
   n279,142084293,pos279,cp279,ivec106,dvec106,dpos106,vp106,ivec28,dvec28,dpos28,vp28⟩

private def bk601 : BoundKit true :=
  ⟨601,eb601,indexOk601.1,indexOk601.2,lookup601,rfl,threshold601,
   n248,29526,pos248,cp248,ivec92,dvec92,dpos92,vp92,ivec93,dvec93,dpos93,vp93⟩

private def bk603 : BoundKit true :=
  ⟨603,eb603,indexOk603.1,indexOk603.2,lookup603,rfl,threshold603,
   n281,7770,pos281,cp281,ivec8,dvec8,dpos8,vp8,ivec4,dvec4,dpos4,vp4⟩

private def bk604 : BoundKit true :=
  ⟨604,eb604,indexOk604.1,indexOk604.2,lookup604,rfl,threshold604,
   n282,1064531,pos282,cp282,ivec31,dvec31,dpos31,vp31,ivec28,dvec28,dpos28,vp28⟩

private def bk606 : BoundKit true :=
  ⟨606,eb606,indexOk606.1,indexOk606.2,lookup606,rfl,threshold606,
   n283,167131367,pos283,cp283,ivec31,dvec31,dpos31,vp31,ivec103,dvec103,dpos103,vp103⟩

private def bk607 : BoundKit true :=
  ⟨607,eb607,indexOk607.1,indexOk607.2,lookup607,rfl,threshold607,
   n288,91686,pos288,cp288,ivec32,dvec32,dpos32,vp32,ivec25,dvec25,dpos25,vp25⟩

private def bk608 : BoundKit true :=
  ⟨608,eb608,indexOk608.1,indexOk608.2,lookup608,rfl,threshold608,
   n289,327450,pos289,cp289,ivec32,dvec32,dpos32,vp32,ivec25,dvec25,dpos25,vp25⟩

private def bk609 : BoundKit true :=
  ⟨609,eb609,indexOk609.1,indexOk609.2,lookup609,rfl,threshold609,
   n284,128644477,pos284,cp284,ivec35,dvec35,dpos35,vp35,ivec28,dvec28,dpos28,vp28⟩

private def bk611 : BoundKit true :=
  ⟨611,eb611,indexOk611.1,indexOk611.2,lookup611,rfl,threshold611,
   n285,90753,pos285,cp285,ivec107,dvec107,dpos107,vp107,ivec28,dvec28,dpos28,vp28⟩

private def bk612 : BoundKit true :=
  ⟨612,eb612,indexOk612.1,indexOk612.2,lookup612,rfl,threshold612,
   n286,14248221,pos286,cp286,ivec107,dvec107,dpos107,vp107,ivec108,dvec108,dpos108,vp108⟩

private def bk613 : BoundKit true :=
  ⟨613,eb613,indexOk613.1,indexOk613.2,lookup613,rfl,threshold613,
   n287,97513,pos287,cp287,ivec109,dvec109,dpos109,vp109,ivec28,dvec28,dpos28,vp28⟩

private def bk620 : BoundKit false :=
  ⟨620,eb620,indexOk620.1,indexOk620.2,lookup620,rfl,threshold620,
   n292,147323,pos292,cp292,ivec74,dvec74,dpos74,vp74,ivec110,dvec110,dpos110,vp110⟩

private def bk621 : BoundKit true :=
  ⟨621,eb621,indexOk621.1,indexOk621.2,lookup621,rfl,threshold621,
   n290,700271,pos290,cp290,ivec79,dvec79,dpos79,vp79,ivec30,dvec30,dpos30,vp30⟩

private def bk624 : BoundKit true :=
  ⟨624,eb624,indexOk624.1,indexOk624.2,lookup624,rfl,threshold624,
   n291,25371357,pos291,cp291,ivec79,dvec79,dpos79,vp79,ivec34,dvec34,dpos34,vp34⟩

private def bk627 : BoundKit true :=
  ⟨627,eb627,indexOk627.1,indexOk627.2,lookup627,rfl,threshold627,
   n293,10527803,pos293,cp293,ivec81,dvec81,dpos81,vp81,ivec30,dvec30,dpos30,vp30⟩

private def bk630 : BoundKit true :=
  ⟨630,eb630,indexOk630.1,indexOk630.2,lookup630,rfl,threshold630,
   n292,147323,pos292,cp292,ivec74,dvec74,dpos74,vp74,ivec110,dvec110,dpos110,vp110⟩

private def bk631 : BoundKit false :=
  ⟨631,eb631,indexOk631.1,indexOk631.2,lookup631,rfl,threshold631,
   n294,7660796,pos294,cp294,ivec74,dvec74,dpos74,vp74,ivec111,dvec111,dpos111,vp111⟩

private def bk632 : BoundKit false :=
  ⟨632,eb632,indexOk632.1,indexOk632.2,lookup632,rfl,threshold632,
   n295,5421097,pos295,cp295,ivec76,dvec76,dpos76,vp76,ivec110,dvec110,dpos110,vp110⟩

private def bk639 : BoundKit true :=
  ⟨639,eb639,indexOk639.1,indexOk639.2,lookup639,rfl,threshold639,
   n298,51991484,pos298,cp298,ivec113,dvec113,dpos113,vp113,ivec112,dvec112,dpos112,vp112⟩

private def bk642 : BoundKit true :=
  ⟨642,eb642,indexOk642.1,indexOk642.2,lookup642,rfl,threshold642,
   n302,547307,pos302,cp302,ivec116,dvec116,dpos116,vp116,ivec112,dvec112,dpos112,vp112⟩

private def bk645 : BoundKit false :=
  ⟨645,eb645,indexOk645.1,indexOk645.2,lookup645,rfl,threshold645,
   n307,72486589,pos307,cp307,ivec118,dvec118,dpos118,vp118,ivec25,dvec25,dpos25,vp25⟩

private def bk646 : BoundKit false :=
  ⟨646,eb646,indexOk646.1,indexOk646.2,lookup646,rfl,threshold646,
   n318,22549813,pos318,cp318,ivec122,dvec122,dpos122,vp122,ivec123,dvec123,dpos123,vp123⟩

private def bk647 : BoundKit false :=
  ⟨647,eb647,indexOk647.1,indexOk647.2,lookup647,rfl,threshold647,
   n315,637177,pos315,cp315,ivec121,dvec121,dpos121,vp121,ivec4,dvec4,dpos4,vp4⟩

private def bk648 : BoundKit false :=
  ⟨648,eb648,indexOk648.1,indexOk648.2,lookup648,rfl,threshold648,
   n317,1046054,pos317,cp317,ivec120,dvec120,dpos120,vp120,ivec4,dvec4,dpos4,vp4⟩

private def bk654 : BoundKit false :=
  ⟨654,eb654,indexOk654.1,indexOk654.2,lookup654,rfl,threshold654,
   n321,106599116,pos321,cp321,ivec122,dvec122,dpos122,vp122,ivec124,dvec124,dpos124,vp124⟩

private def bk655 : BoundKit true :=
  ⟨655,eb655,indexOk655.1,indexOk655.2,lookup655,rfl,threshold655,
   n310,10028555,pos310,cp310,ivec119,dvec119,dpos119,vp119,ivec95,dvec95,dpos95,vp95⟩

private def bk656 : BoundKit true :=
  ⟨656,eb656,indexOk656.1,indexOk656.2,lookup656,rfl,threshold656,
   n313,523027,pos313,cp313,ivec120,dvec120,dpos120,vp120,ivec97,dvec97,dpos97,vp97⟩

private def bk657 : BoundKit false :=
  ⟨657,eb657,indexOk657.1,indexOk657.2,lookup657,rfl,threshold657,
   n322,784259531,pos322,cp322,ivec125,dvec125,dpos125,vp125,ivec123,dvec123,dpos123,vp123⟩

private def bk666 : BoundKit false :=
  ⟨666,eb666,indexOk666.1,indexOk666.2,lookup666,rfl,threshold666,
   n324,10355227,pos324,cp324,ivec118,dvec118,dpos118,vp118,ivec25,dvec25,dpos25,vp25⟩

private def bk669 : BoundKit true :=
  ⟨669,eb669,indexOk669.1,indexOk669.2,lookup669,rfl,threshold669,
   n325,1258,pos325,cp325,ivec126,dvec126,dpos126,vp126,ivec4,dvec4,dpos4,vp4⟩

private def bk670 : BoundKit true :=
  ⟨670,eb670,indexOk670.1,indexOk670.2,lookup670,rfl,threshold670,
   n326,10727197,pos326,cp326,ivec29,dvec29,dpos29,vp29,ivec127,dvec127,dpos127,vp127⟩

private def bk673 : BoundKit true :=
  ⟨673,eb673,indexOk673.1,indexOk673.2,lookup673,rfl,threshold673,
   n329,510,pos329,cp329,ivec1,dvec1,dpos1,vp1,ivec128,dvec128,dpos128,vp128⟩

private def bk677 : BoundKit true :=
  ⟨677,eb677,indexOk677.1,indexOk677.2,lookup677,rfl,threshold677,
   n332,613802,pos332,cp332,ivec26,dvec26,dpos26,vp26,ivec129,dvec129,dpos129,vp129⟩

private def bk679 : BoundKit true :=
  ⟨679,eb679,indexOk679.1,indexOk679.2,lookup679,rfl,threshold679,
   n334,2192150,pos334,cp334,ivec26,dvec26,dpos26,vp26,ivec129,dvec129,dpos129,vp129⟩

private def bk680 : BoundKit true :=
  ⟨680,eb680,indexOk680.1,indexOk680.2,lookup680,rfl,threshold680,
   n335,170,pos335,cp335,ivec1,dvec1,dpos1,vp1,ivec130,dvec130,dpos130,vp130⟩

private def bk683 : BoundKit false :=
  ⟨683,eb683,indexOk683.1,indexOk683.2,lookup683,rfl,threshold683,
   n337,72486589,pos337,cp337,ivec118,dvec118,dpos118,vp118,ivec33,dvec33,dpos33,vp33⟩

private def bk684 : BoundKit false :=
  ⟨684,eb684,indexOk684.1,indexOk684.2,lookup684,rfl,threshold684,
   n340,22549813,pos340,cp340,ivec122,dvec122,dpos122,vp122,ivec110,dvec110,dpos110,vp110⟩

private def bk685 : BoundKit false :=
  ⟨685,eb685,indexOk685.1,indexOk685.2,lookup685,rfl,threshold685,
   n338,637177,pos338,cp338,ivec121,dvec121,dpos121,vp121,ivec7,dvec7,dpos7,vp7⟩

private def bk686 : BoundKit false :=
  ⟨686,eb686,indexOk686.1,indexOk686.2,lookup686,rfl,threshold686,
   n339,1046054,pos339,cp339,ivec120,dvec120,dpos120,vp120,ivec7,dvec7,dpos7,vp7⟩

private def bk692 : BoundKit false :=
  ⟨692,eb692,indexOk692.1,indexOk692.2,lookup692,rfl,threshold692,
   n341,106599116,pos341,cp341,ivec122,dvec122,dpos122,vp122,ivec111,dvec111,dpos111,vp111⟩

private def bk695 : BoundKit false :=
  ⟨695,eb695,indexOk695.1,indexOk695.2,lookup695,rfl,threshold695,
   n342,784259531,pos342,cp342,ivec125,dvec125,dpos125,vp125,ivec110,dvec110,dpos110,vp110⟩

private def bk704 : BoundKit false :=
  ⟨704,eb704,indexOk704.1,indexOk704.2,lookup704,rfl,threshold704,
   n343,51776135,pos343,cp343,ivec118,dvec118,dpos118,vp118,ivec33,dvec33,dpos33,vp33⟩

private def bk708 : BoundKit true :=
  ⟨708,eb708,indexOk708.1,indexOk708.2,lookup708,rfl,threshold708,
   n344,10727197,pos344,cp344,ivec29,dvec29,dpos29,vp29,ivec131,dvec131,dpos131,vp131⟩

private def bk711 : BoundKit true :=
  ⟨711,eb711,indexOk711.1,indexOk711.2,lookup711,rfl,threshold711,
   n347,170,pos347,cp347,ivec1,dvec1,dpos1,vp1,ivec132,dvec132,dpos132,vp132⟩

private def bk715 : BoundKit true :=
  ⟨715,eb715,indexOk715.1,indexOk715.2,lookup715,rfl,threshold715,
   n350,613802,pos350,cp350,ivec26,dvec26,dpos26,vp26,ivec133,dvec133,dpos133,vp133⟩

private def bk717 : BoundKit true :=
  ⟨717,eb717,indexOk717.1,indexOk717.2,lookup717,rfl,threshold717,
   n352,2192150,pos352,cp352,ivec26,dvec26,dpos26,vp26,ivec133,dvec133,dpos133,vp133⟩

private def bk718 : BoundKit true :=
  ⟨718,eb718,indexOk718.1,indexOk718.2,lookup718,rfl,threshold718,
   n353,170,pos353,cp353,ivec1,dvec1,dpos1,vp1,ivec134,dvec134,dpos134,vp134⟩

private def bk721 : BoundKit false :=
  ⟨721,eb721,indexOk721.1,indexOk721.2,lookup721,rfl,threshold721,
   n355,1807526,pos355,cp355,ivec100,dvec100,dpos100,vp100,ivec33,dvec33,dpos33,vp33⟩

private def bk722 : BoundKit false :=
  ⟨722,eb722,indexOk722.1,indexOk722.2,lookup722,rfl,threshold722,
   n362,7488217,pos362,cp362,ivec137,dvec137,dpos137,vp137,ivec110,dvec110,dpos110,vp110⟩

private def bk723 : BoundKit false :=
  ⟨723,eb723,indexOk723.1,indexOk723.2,lookup723,rfl,threshold723,
   n359,421430,pos359,cp359,ivec102,dvec102,dpos102,vp102,ivec7,dvec7,dpos7,vp7⟩

private def bk724 : BoundKit false :=
  ⟨724,eb724,indexOk724.1,indexOk724.2,lookup724,rfl,threshold724,
   n360,161581,pos360,cp360,ivec136,dvec136,dpos136,vp136,ivec7,dvec7,dpos7,vp7⟩

private def bk730 : BoundKit false :=
  ⟨730,eb730,indexOk730.1,indexOk730.2,lookup730,rfl,threshold730,
   n364,35398844,pos364,cp364,ivec137,dvec137,dpos137,vp137,ivec111,dvec111,dpos111,vp111⟩

private def bk731 : BoundKit true :=
  ⟨731,eb731,indexOk731.1,indexOk731.2,lookup731,rfl,threshold731,
   n356,48468670,pos356,cp356,ivec135,dvec135,dpos135,vp135,ivec38,dvec38,dpos38,vp38⟩

private def bk733 : BoundKit false :=
  ⟨733,eb733,indexOk733.1,indexOk733.2,lookup733,rfl,threshold733,
   n365,132663949,pos365,cp365,ivec138,dvec138,dpos138,vp138,ivec110,dvec110,dpos110,vp110⟩

private def bk742 : BoundKit false :=
  ⟨742,eb742,indexOk742.1,indexOk742.2,lookup742,rfl,threshold742,
   n367,6455450,pos367,cp367,ivec100,dvec100,dpos100,vp100,ivec33,dvec33,dpos33,vp33⟩

private def bk746 : BoundKit true :=
  ⟨746,eb746,indexOk746.1,indexOk746.2,lookup746,rfl,threshold746,
   n368,90753,pos368,cp368,ivec107,dvec107,dpos107,vp107,ivec131,dvec131,dpos131,vp131⟩

private def bk751 : BoundKit true :=
  ⟨751,eb751,indexOk751.1,indexOk751.2,lookup751,rfl,threshold751,
   n369,4749407,pos369,cp369,ivec107,dvec107,dpos107,vp107,ivec139,dvec139,dpos139,vp139⟩

private def bk755 : BoundKit true :=
  ⟨755,eb755,indexOk755.1,indexOk755.2,lookup755,rfl,threshold755,
   n371,97513,pos371,cp371,ivec109,dvec109,dpos109,vp109,ivec131,dvec131,dpos131,vp131⟩

private def bk757 : BoundKit true :=
  ⟨757,eb757,indexOk757.1,indexOk757.2,lookup757,rfl,threshold757,
   n372,1295,pos372,cp372,ivec8,dvec8,dpos8,vp8,ivec132,dvec132,dpos132,vp132⟩

private def bk761 : BoundKit true :=
  ⟨761,eb761,indexOk761.1,indexOk761.2,lookup761,rfl,threshold761,
   n373,76405,pos373,cp373,ivec32,dvec32,dpos32,vp32,ivec133,dvec133,dpos133,vp133⟩

private def bk765 : BoundKit true :=
  ⟨765,eb765,indexOk765.1,indexOk765.2,lookup765,rfl,threshold765,
   n374,272875,pos374,cp374,ivec32,dvec32,dpos32,vp32,ivec133,dvec133,dpos133,vp133⟩

private def bk766 : BoundKit true :=
  ⟨766,eb766,indexOk766.1,indexOk766.2,lookup766,rfl,threshold766,
   n375,1295,pos375,cp375,ivec8,dvec8,dpos8,vp8,ivec134,dvec134,dpos134,vp134⟩

private def bk771 : BoundKit false :=
  ⟨771,eb771,indexOk771.1,indexOk771.2,lookup771,rfl,threshold771,
   n376,98279839,pos376,cp376,ivec119,dvec119,dpos119,vp119,ivec49,dvec49,dpos49,vp49⟩

private def bk772 : BoundKit false :=
  ⟨772,eb772,indexOk772.1,indexOk772.2,lookup772,rfl,threshold772,
   n378,1734601,pos378,cp378,ivec122,dvec122,dpos122,vp122,ivec86,dvec86,dpos86,vp86⟩

private def bk773 : BoundKit false :=
  ⟨773,eb773,indexOk773.1,indexOk773.2,lookup773,rfl,threshold773,
   n377,523027,pos377,cp377,ivec120,dvec120,dpos120,vp120,ivec9,dvec9,dpos9,vp9⟩

private def bk780 : BoundKit false :=
  ⟨780,eb780,indexOk780.1,indexOk780.2,lookup780,rfl,threshold780,
   n379,2005711,pos379,cp379,ivec119,dvec119,dpos119,vp119,ivec49,dvec49,dpos49,vp49⟩

private def bk783 : BoundKit false :=
  ⟨783,eb783,indexOk783.1,indexOk783.2,lookup783,rfl,threshold783,
   n380,53299558,pos380,cp380,ivec122,dvec122,dpos122,vp122,ivec87,dvec87,dpos87,vp87⟩

private def bk788 : BoundKit false :=
  ⟨788,eb788,indexOk788.1,indexOk788.2,lookup788,rfl,threshold788,
   n381,27179581,pos381,cp381,ivec140,dvec140,dpos140,vp140,ivec86,dvec86,dpos86,vp86⟩

private def bk792 : BoundKit true :=
  ⟨792,eb792,indexOk792.1,indexOk792.2,lookup792,rfl,threshold792,
   n383,10727197,pos383,cp383,ivec29,dvec29,dpos29,vp29,ivec141,dvec141,dpos141,vp141⟩

private def bk795 : BoundKit true :=
  ⟨795,eb795,indexOk795.1,indexOk795.2,lookup795,rfl,threshold795,
   n386,920703,pos386,cp386,ivec26,dvec26,dpos26,vp26,ivec142,dvec142,dpos142,vp142⟩

private def bk797 : BoundKit true :=
  ⟨797,eb797,indexOk797.1,indexOk797.2,lookup797,rfl,threshold797,
   n389,3288225,pos389,cp389,ivec26,dvec26,dpos26,vp26,ivec142,dvec142,dpos142,vp142⟩

private def bk798 : BoundKit true :=
  ⟨798,eb798,indexOk798.1,indexOk798.2,lookup798,rfl,threshold798,
   n390,255,pos390,cp390,ivec1,dvec1,dpos1,vp1,ivec143,dvec143,dpos143,vp143⟩

private def bk801 : BoundKit false :=
  ⟨801,eb801,indexOk801.1,indexOk801.2,lookup801,rfl,threshold801,
   n392,28079954,pos392,cp392,ivec119,dvec119,dpos119,vp119,ivec80,dvec80,dpos80,vp80⟩

private def bk802 : BoundKit false :=
  ⟨802,eb802,indexOk802.1,indexOk802.2,lookup802,rfl,threshold802,
   n394,106599116,pos394,cp394,ivec122,dvec122,dpos122,vp122,ivec117,dvec117,dpos117,vp117⟩

private def bk803 : BoundKit false :=
  ⟨803,eb803,indexOk803.1,indexOk803.2,lookup803,rfl,threshold803,
   n393,1046054,pos393,cp393,ivec120,dvec120,dpos120,vp120,ivec10,dvec10,dpos10,vp10⟩

private def bk808 : BoundKit false :=
  ⟨808,eb808,indexOk808.1,indexOk808.2,lookup808,rfl,threshold808,
   n395,20057110,pos395,cp395,ivec119,dvec119,dpos119,vp119,ivec80,dvec80,dpos80,vp80⟩

private def bk810 : BoundKit true :=
  ⟨810,eb810,indexOk810.1,indexOk810.2,lookup810,rfl,threshold810,
   n396,10727197,pos396,cp396,ivec29,dvec29,dpos29,vp29,ivec144,dvec144,dpos144,vp144⟩

private def bk813 : BoundKit true :=
  ⟨813,eb813,indexOk813.1,indexOk813.2,lookup813,rfl,threshold813,
   n399,1841406,pos399,cp399,ivec26,dvec26,dpos26,vp26,ivec145,dvec145,dpos145,vp145⟩

private def bk815 : BoundKit true :=
  ⟨815,eb815,indexOk815.1,indexOk815.2,lookup815,rfl,threshold815,
   n402,6576450,pos402,cp402,ivec26,dvec26,dpos26,vp26,ivec145,dvec145,dpos145,vp145⟩

private def bk816 : BoundKit true :=
  ⟨816,eb816,indexOk816.1,indexOk816.2,lookup816,rfl,threshold816,
   n403,510,pos403,cp403,ivec1,dvec1,dpos1,vp1,ivec146,dvec146,dpos146,vp146⟩

private def bk819 : BoundKit false :=
  ⟨819,eb819,indexOk819.1,indexOk819.2,lookup819,rfl,threshold819,
   n405,67856138,pos405,cp405,ivec135,dvec135,dpos135,vp135,ivec49,dvec49,dpos49,vp49⟩

private def bk820 : BoundKit false :=
  ⟨820,eb820,indexOk820.1,indexOk820.2,lookup820,rfl,threshold820,
   n407,7488217,pos407,cp407,ivec137,dvec137,dpos137,vp137,ivec86,dvec86,dpos86,vp86⟩

private def bk821 : BoundKit false :=
  ⟨821,eb821,indexOk821.1,indexOk821.2,lookup821,rfl,threshold821,
   n406,323162,pos406,cp406,ivec136,dvec136,dpos136,vp136,ivec9,dvec9,dpos9,vp9⟩

private def bk827 : BoundKit false :=
  ⟨827,eb827,indexOk827.1,indexOk827.2,lookup827,rfl,threshold827,
   n408,9693734,pos408,cp408,ivec135,dvec135,dpos135,vp135,ivec49,dvec49,dpos49,vp49⟩

private def bk830 : BoundKit false :=
  ⟨830,eb830,indexOk830.1,indexOk830.2,lookup830,rfl,threshold830,
   n409,17699422,pos409,cp409,ivec137,dvec137,dpos137,vp137,ivec87,dvec87,dpos87,vp87⟩

private def bk833 : BoundKit true :=
  ⟨833,eb833,indexOk833.1,indexOk833.2,lookup833,rfl,threshold833,
   n410,6455450,pos410,cp410,ivec100,dvec100,dpos100,vp100,ivec42,dvec42,dpos42,vp42⟩

private def bk834 : BoundKit false :=
  ⟨834,eb834,indexOk834.1,indexOk834.2,lookup834,rfl,threshold834,
   n411,231271139,pos411,cp411,ivec147,dvec147,dpos147,vp147,ivec86,dvec86,dpos86,vp86⟩

private def bk838 : BoundKit true :=
  ⟨838,eb838,indexOk838.1,indexOk838.2,lookup838,rfl,threshold838,
   n412,90753,pos412,cp412,ivec107,dvec107,dpos107,vp107,ivec141,dvec141,dpos141,vp141⟩

private def bk842 : BoundKit true :=
  ⟨842,eb842,indexOk842.1,indexOk842.2,lookup842,rfl,threshold842,
   n413,84309,pos413,cp413,ivec107,dvec107,dpos107,vp107,ivec148,dvec148,dpos148,vp148⟩

private def bk845 : BoundKit true :=
  ⟨845,eb845,indexOk845.1,indexOk845.2,lookup845,rfl,threshold845,
   n415,97513,pos415,cp415,ivec109,dvec109,dpos109,vp109,ivec141,dvec141,dpos141,vp141⟩

private def bk847 : BoundKit true :=
  ⟨847,eb847,indexOk847.1,indexOk847.2,lookup847,rfl,threshold847,
   n416,91686,pos416,cp416,ivec32,dvec32,dpos32,vp32,ivec142,dvec142,dpos142,vp142⟩

private def bk851 : BoundKit true :=
  ⟨851,eb851,indexOk851.1,indexOk851.2,lookup851,rfl,threshold851,
   n417,327450,pos417,cp417,ivec32,dvec32,dpos32,vp32,ivec142,dvec142,dpos142,vp142⟩

private def bk852 : BoundKit true :=
  ⟨852,eb852,indexOk852.1,indexOk852.2,lookup852,rfl,threshold852,
   n418,1554,pos418,cp418,ivec8,dvec8,dpos8,vp8,ivec143,dvec143,dpos143,vp143⟩

private def bk857 : BoundKit false :=
  ⟨857,eb857,indexOk857.1,indexOk857.2,lookup857,rfl,threshold857,
   n419,10790913,pos419,cp419,ivec149,dvec149,dpos149,vp149,ivec33,dvec33,dpos33,vp33⟩

private def bk858 : BoundKit false :=
  ⟨858,eb858,indexOk858.1,indexOk858.2,lookup858,rfl,threshold858,
   n424,11017897,pos424,cp424,ivec151,dvec151,dpos151,vp151,ivec110,dvec110,dpos110,vp110⟩

private def bk859 : BoundKit false :=
  ⟨859,eb859,indexOk859.1,indexOk859.2,lookup859,rfl,threshold859,
   n422,38505,pos422,cp422,ivec150,dvec150,dpos150,vp150,ivec7,dvec7,dpos7,vp7⟩

private def bk862 : BoundKit false :=
  ⟨862,eb862,indexOk862.1,indexOk862.2,lookup862,rfl,threshold862,
   n427,52084604,pos427,cp427,ivec151,dvec151,dpos151,vp151,ivec111,dvec111,dpos111,vp111⟩

private def bk864 : BoundKit false :=
  ⟨864,eb864,indexOk864.1,indexOk864.2,lookup864,rfl,threshold864,
   n428,110140129,pos428,cp428,ivec152,dvec152,dpos152,vp152,ivec110,dvec110,dpos110,vp110⟩

private def bk872 : BoundKit false :=
  ⟨872,eb872,indexOk872.1,indexOk872.2,lookup872,rfl,threshold872,
   n430,38538975,pos430,cp430,ivec149,dvec149,dpos149,vp149,ivec33,dvec33,dpos33,vp33⟩

private def bk876 : BoundKit true :=
  ⟨876,eb876,indexOk876.1,indexOk876.2,lookup876,rfl,threshold876,
   n431,2100813,pos431,cp431,ivec79,dvec79,dpos79,vp79,ivec131,dvec131,dpos131,vp131⟩

private def bk880 : BoundKit true :=
  ⟨880,eb880,indexOk880.1,indexOk880.2,lookup880,rfl,threshold880,
   n436,8457119,pos436,cp436,ivec79,dvec79,dpos79,vp79,ivec154,dvec154,dpos154,vp154⟩

private def bk885 : BoundKit true :=
  ⟨885,eb885,indexOk885.1,indexOk885.2,lookup885,rfl,threshold885,
   n438,31583409,pos438,cp438,ivec81,dvec81,dpos81,vp81,ivec131,dvec131,dpos131,vp131⟩

private def bk889 : BoundKit false :=
  ⟨889,eb889,indexOk889.1,indexOk889.2,lookup889,rfl,threshold889,
   n439,96454246,pos439,cp439,ivec155,dvec155,dpos155,vp155,ivec33,dvec33,dpos33,vp33⟩

private def bk890 : BoundKit false :=
  ⟨890,eb890,indexOk890.1,indexOk890.2,lookup890,rfl,threshold890,
   n444,17679959,pos444,cp444,ivec157,dvec157,dpos157,vp157,ivec110,dvec110,dpos110,vp110⟩

private def bk891 : BoundKit false :=
  ⟨891,eb891,indexOk891.1,indexOk891.2,lookup891,rfl,threshold891,
   n442,454510,pos442,cp442,ivec156,dvec156,dpos156,vp156,ivec7,dvec7,dpos7,vp7⟩

private def bk894 : BoundKit false :=
  ⟨894,eb894,indexOk894.1,indexOk894.2,lookup894,rfl,threshold894,
   n447,83577988,pos447,cp447,ivec157,dvec157,dpos157,vp157,ivec111,dvec111,dpos111,vp111⟩

private def bk896 : BoundKit false :=
  ⟨896,eb896,indexOk896.1,indexOk896.2,lookup896,rfl,threshold896,
   n448,272669507,pos448,cp448,ivec158,dvec158,dpos158,vp158,ivec110,dvec110,dpos110,vp110⟩

private def bk904 : BoundKit false :=
  ⟨904,eb904,indexOk904.1,indexOk904.2,lookup904,rfl,threshold904,
   n450,49211350,pos450,cp450,ivec155,dvec155,dpos155,vp155,ivec33,dvec33,dpos33,vp33⟩

private def bk908 : BoundKit true :=
  ⟨908,eb908,indexOk908.1,indexOk908.2,lookup908,rfl,threshold908,
   n451,8433958,pos451,cp451,ivec159,dvec159,dpos159,vp159,ivec131,dvec131,dpos131,vp131⟩

private def bk912 : BoundKit true :=
  ⟨912,eb912,indexOk912.1,indexOk912.2,lookup912,rfl,threshold912,
   n452,15762614,pos452,cp452,ivec75,dvec75,dpos75,vp75,ivec153,dvec153,dpos153,vp153⟩

private def bk914 : BoundKit true :=
  ⟨914,eb914,indexOk914.1,indexOk914.2,lookup914,rfl,threshold914,
   n453,321686,pos453,cp453,ivec75,dvec75,dpos75,vp75,ivec153,dvec153,dpos153,vp153⟩

private def bk915 : BoundKit true :=
  ⟨915,eb915,indexOk915.1,indexOk915.2,lookup915,rfl,threshold915,
   n454,57974,pos454,cp454,ivec12,dvec12,dpos12,vp12,ivec132,dvec132,dpos132,vp132⟩

private def bk918 : BoundKit true :=
  ⟨918,eb918,indexOk918.1,indexOk918.2,lookup918,rfl,threshold918,
   n455,50928131,pos455,cp455,ivec159,dvec159,dpos159,vp159,ivec154,dvec154,dpos154,vp154⟩

private def bk923 : BoundKit true :=
  ⟨923,eb923,indexOk923.1,indexOk923.2,lookup923,rfl,threshold923,
   n456,29542461,pos456,cp456,ivec160,dvec160,dpos160,vp160,ivec131,dvec131,dpos131,vp131⟩

private def bk927 : BoundKit false :=
  ⟨927,eb927,indexOk927.1,indexOk927.2,lookup927,rfl,threshold927,
   n457,1891477,pos457,cp457,ivec161,dvec161,dpos161,vp161,ivec49,dvec49,dpos49,vp49⟩

private def bk928 : BoundKit false :=
  ⟨928,eb928,indexOk928.1,indexOk928.2,lookup928,rfl,threshold928,
   n462,11017897,pos462,cp462,ivec151,dvec151,dpos151,vp151,ivec86,dvec86,dpos86,vp86⟩

private def bk929 : BoundKit false :=
  ⟨929,eb929,indexOk929.1,indexOk929.2,lookup929,rfl,threshold929,
   n459,19765,pos459,cp459,ivec162,dvec162,dpos162,vp162,ivec9,dvec9,dpos9,vp9⟩

private def bk930 : BoundKit false :=
  ⟨930,eb930,indexOk930.1,indexOk930.2,lookup930,rfl,threshold930,
   n461,25670,pos461,cp461,ivec150,dvec150,dpos150,vp150,ivec9,dvec9,dpos9,vp9⟩

private def bk937 : BoundKit false :=
  ⟨937,eb937,indexOk937.1,indexOk937.2,lookup937,rfl,threshold937,
   n463,270211,pos463,cp463,ivec161,dvec161,dpos161,vp161,ivec49,dvec49,dpos49,vp49⟩

private def bk943 : BoundKit false :=
  ⟨943,eb943,indexOk943.1,indexOk943.2,lookup943,rfl,threshold943,
   n464,26042302,pos464,cp464,ivec151,dvec151,dpos151,vp151,ivec87,dvec87,dpos87,vp87⟩

private def bk948 : BoundKit false :=
  ⟨948,eb948,indexOk948.1,indexOk948.2,lookup948,rfl,threshold948,
   n465,67839167,pos465,cp465,ivec163,dvec163,dpos163,vp163,ivec86,dvec86,dpos86,vp86⟩

private def bk952 : BoundKit true :=
  ⟨952,eb952,indexOk952.1,indexOk952.2,lookup952,rfl,threshold952,
   n467,2100813,pos467,cp467,ivec79,dvec79,dpos79,vp79,ivec141,dvec141,dpos141,vp141⟩

private def bk960 : BoundKit true :=
  ⟨960,eb960,indexOk960.1,indexOk960.2,lookup960,rfl,threshold960,
   n471,12314,pos471,cp471,ivec11,dvec11,dpos11,vp11,ivec165,dvec165,dpos165,vp165⟩

private def bk962 : BoundKit true :=
  ⟨962,eb962,indexOk962.1,indexOk962.2,lookup962,rfl,threshold962,
   n473,25371357,pos473,cp473,ivec79,dvec79,dpos79,vp79,ivec166,dvec166,dpos166,vp166⟩

private def bk968 : BoundKit true :=
  ⟨968,eb968,indexOk968.1,indexOk968.2,lookup968,rfl,threshold968,
   n475,31583409,pos475,cp475,ivec81,dvec81,dpos81,vp81,ivec141,dvec141,dpos141,vp141⟩

private def bk972 : BoundKit true :=
  ⟨972,eb972,indexOk972.1,indexOk972.2,lookup972,rfl,threshold972,
   n476,12314,pos476,cp476,ivec11,dvec11,dpos11,vp11,ivec143,dvec143,dpos143,vp143⟩

private def bk973 : BoundKit false :=
  ⟨973,eb973,indexOk973.1,indexOk973.2,lookup973,rfl,threshold973,
   n477,56462,pos477,cp477,ivec161,dvec161,dpos161,vp161,ivec80,dvec80,dpos80,vp80⟩

private def bk974 : BoundKit false :=
  ⟨974,eb974,indexOk974.1,indexOk974.2,lookup974,rfl,threshold974,
   n481,52084604,pos481,cp481,ivec151,dvec151,dpos151,vp151,ivec117,dvec117,dpos117,vp117⟩

private def bk975 : BoundKit false :=
  ⟨975,eb975,indexOk975.1,indexOk975.2,lookup975,rfl,threshold975,
   n478,590,pos478,cp478,ivec162,dvec162,dpos162,vp162,ivec10,dvec10,dpos10,vp10⟩

private def bk976 : BoundKit false :=
  ⟨976,eb976,indexOk976.1,indexOk976.2,lookup976,rfl,threshold976,
   n479,1510,pos479,cp479,ivec150,dvec150,dpos150,vp150,ivec10,dvec10,dpos10,vp10⟩

private def bk983 : BoundKit false :=
  ⟨983,eb983,indexOk983.1,indexOk983.2,lookup983,rfl,threshold983,
   n482,201650,pos482,cp482,ivec161,dvec161,dpos161,vp161,ivec80,dvec80,dpos80,vp80⟩

private def bk984 : BoundKit true :=
  ⟨984,eb984,indexOk984.1,indexOk984.2,lookup984,rfl,threshold984,
   n480,1310,pos480,cp480,ivec63,dvec63,dpos63,vp63,ivec10,dvec10,dpos10,vp10⟩

private def bk986 : BoundKit true :=
  ⟨986,eb986,indexOk986.1,indexOk986.2,lookup986,rfl,threshold986,
   n483,2100813,pos483,cp483,ivec79,dvec79,dpos79,vp79,ivec144,dvec144,dpos144,vp144⟩

private def bk994 : BoundKit true :=
  ⟨994,eb994,indexOk994.1,indexOk994.2,lookup994,rfl,threshold994,
   n484,1160054,pos484,cp484,ivec54,dvec54,dpos54,vp54,ivec167,dvec167,dpos167,vp167⟩

private def bk996 : BoundKit true :=
  ⟨996,eb996,indexOk996.1,indexOk996.2,lookup996,rfl,threshold996,
   n487,828610,pos487,cp487,ivec54,dvec54,dpos54,vp54,ivec167,dvec167,dpos167,vp167⟩

private def bk997 : BoundKit true :=
  ⟨997,eb997,indexOk997.1,indexOk997.2,lookup997,rfl,threshold997,
   n488,12314,pos488,cp488,ivec11,dvec11,dpos11,vp11,ivec168,dvec168,dpos168,vp168⟩

private def bk1000 : BoundKit true :=
  ⟨1000,eb1000,indexOk1000.1,indexOk1000.2,lookup1000,rfl,threshold1000,
   n490,25371357,pos490,cp490,ivec79,dvec79,dpos79,vp79,ivec169,dvec169,dpos169,vp169⟩

private def bk1006 : BoundKit true :=
  ⟨1006,eb1006,indexOk1006.1,indexOk1006.2,lookup1006,rfl,threshold1006,
   n492,31583409,pos492,cp492,ivec81,dvec81,dpos81,vp81,ivec144,dvec144,dpos144,vp144⟩

private def bk1010 : BoundKit true :=
  ⟨1010,eb1010,indexOk1010.1,indexOk1010.2,lookup1010,rfl,threshold1010,
   n493,12314,pos493,cp493,ivec11,dvec11,dpos11,vp11,ivec146,dvec146,dpos146,vp146⟩

private def bk1011 : BoundKit false :=
  ⟨1011,eb1011,indexOk1011.1,indexOk1011.2,lookup1011,rfl,threshold1011,
   n494,21210854,pos494,cp494,ivec170,dvec170,dpos170,vp170,ivec49,dvec49,dpos49,vp49⟩

private def bk1012 : BoundKit false :=
  ⟨1012,eb1012,indexOk1012.1,indexOk1012.2,lookup1012,rfl,threshold1012,
   n499,17679959,pos499,cp499,ivec157,dvec157,dpos157,vp157,ivec86,dvec86,dpos86,vp86⟩

private def bk1013 : BoundKit false :=
  ⟨1013,eb1013,indexOk1013.1,indexOk1013.2,lookup1013,rfl,threshold1013,
   n496,198830,pos496,cp496,ivec171,dvec171,dpos171,vp171,ivec9,dvec9,dpos9,vp9⟩

private def bk1014 : BoundKit false :=
  ⟨1014,eb1014,indexOk1014.1,indexOk1014.2,lookup1014,rfl,threshold1014,
   n498,227255,pos498,cp498,ivec156,dvec156,dpos156,vp156,ivec9,dvec9,dpos9,vp9⟩

private def bk1021 : BoundKit false :=
  ⟨1021,eb1021,indexOk1021.1,indexOk1021.2,lookup1021,rfl,threshold1021,
   n500,3030122,pos500,cp500,ivec170,dvec170,dpos170,vp170,ivec49,dvec49,dpos49,vp49⟩

private def bk1027 : BoundKit false :=
  ⟨1027,eb1027,indexOk1027.1,indexOk1027.2,lookup1027,rfl,threshold1027,
   n501,125366982,pos501,cp501,ivec157,dvec157,dpos157,vp157,ivec87,dvec87,dpos87,vp87⟩

private def bk1032 : BoundKit false :=
  ⟨1032,eb1032,indexOk1032.1,indexOk1032.2,lookup1032,rfl,threshold1032,
   n502,1882548107,pos502,cp502,ivec172,dvec172,dpos172,vp172,ivec86,dvec86,dpos86,vp86⟩

private def bk1036 : BoundKit true :=
  ⟨1036,eb1036,indexOk1036.1,indexOk1036.2,lookup1036,rfl,threshold1036,
   n504,4216979,pos504,cp504,ivec159,dvec159,dpos159,vp159,ivec141,dvec141,dpos141,vp141⟩

private def bk1037 : BoundKit false :=
  ⟨1037,eb1037,indexOk1037.1,indexOk1037.2,lookup1037,rfl,threshold1037,
   n505,538734,pos505,cp505,ivec68,dvec68,dpos68,vp68,ivec142,dvec142,dpos142,vp142⟩

private def bk1044 : BoundKit true :=
  ⟨1044,eb1044,indexOk1044.1,indexOk1044.2,lookup1044,rfl,threshold1044,
   n506,2251802,pos506,cp506,ivec75,dvec75,dpos75,vp75,ivec164,dvec164,dpos164,vp164⟩

private def bk1046 : BoundKit true :=
  ⟨1046,eb1046,indexOk1046.1,indexOk1046.2,lookup1046,rfl,threshold1046,
   n507,1608430,pos507,cp507,ivec75,dvec75,dpos75,vp75,ivec164,dvec164,dpos164,vp164⟩

private def bk1047 : BoundKit true :=
  ⟨1047,eb1047,indexOk1047.1,indexOk1047.2,lookup1047,rfl,threshold1047,
   n508,57974,pos508,cp508,ivec12,dvec12,dpos12,vp12,ivec165,dvec165,dpos165,vp165⟩

private def bk1050 : BoundKit true :=
  ⟨1050,eb1050,indexOk1050.1,indexOk1050.2,lookup1050,rfl,threshold1050,
   n509,101856262,pos509,cp509,ivec159,dvec159,dpos159,vp159,ivec166,dvec166,dpos166,vp166⟩

private def bk1056 : BoundKit true :=
  ⟨1056,eb1056,indexOk1056.1,indexOk1056.2,lookup1056,rfl,threshold1056,
   n510,29542461,pos510,cp510,ivec160,dvec160,dpos160,vp160,ivec141,dvec141,dpos141,vp141⟩

private def bk1060 : BoundKit true :=
  ⟨1060,eb1060,indexOk1060.1,indexOk1060.2,lookup1060,rfl,threshold1060,
   n511,28987,pos511,cp511,ivec12,dvec12,dpos12,vp12,ivec143,dvec143,dpos143,vp143⟩

private def bk1061 : BoundKit false :=
  ⟨1061,eb1061,indexOk1061.1,indexOk1061.2,lookup1061,rfl,threshold1061,
   n512,104524931,pos512,cp512,ivec173,dvec173,dpos173,vp173,ivec49,dvec49,dpos49,vp49⟩

private def bk1062 : BoundKit false :=
  ⟨1062,eb1062,indexOk1062.1,indexOk1062.2,lookup1062,rfl,threshold1062,
   n520,54363419,pos520,cp520,ivec176,dvec176,dpos176,vp176,ivec86,dvec86,dpos86,vp86⟩

private def bk1063 : BoundKit false :=
  ⟨1063,eb1063,indexOk1063.1,indexOk1063.2,lookup1063,rfl,threshold1063,
   n515,921695,pos515,cp515,ivec174,dvec174,dpos174,vp174,ivec9,dvec9,dpos9,vp9⟩

private def bk1064 : BoundKit false :=
  ⟨1064,eb1064,indexOk1064.1,indexOk1064.2,lookup1064,rfl,threshold1064,
   n517,502670,pos517,cp517,ivec175,dvec175,dpos175,vp175,ivec9,dvec9,dpos9,vp9⟩

private def bk1071 : BoundKit false :=
  ⟨1071,eb1071,indexOk1071.1,indexOk1071.2,lookup1071,rfl,threshold1071,
   n523,14932133,pos523,cp523,ivec173,dvec173,dpos173,vp173,ivec49,dvec49,dpos49,vp49⟩

private def bk1077 : BoundKit false :=
  ⟨1077,eb1077,indexOk1077.1,indexOk1077.2,lookup1077,rfl,threshold1077,
   n524,385486062,pos524,cp524,ivec176,dvec176,dpos176,vp176,ivec87,dvec87,dpos87,vp87⟩

private def bk1082 : BoundKit false :=
  ⟨1082,eb1082,indexOk1082.1,indexOk1082.2,lookup1082,rfl,threshold1082,
   n525,72787979,pos525,cp525,ivec177,dvec177,dpos177,vp177,ivec86,dvec86,dpos86,vp86⟩

private def bk1086 : BoundKit true :=
  ⟨1086,eb1086,indexOk1086.1,indexOk1086.2,lookup1086,rfl,threshold1086,
   n527,312797329,pos527,cp527,ivec178,dvec178,dpos178,vp178,ivec141,dvec141,dpos141,vp141⟩

private def bk1087 : BoundKit false :=
  ⟨1087,eb1087,indexOk1087.1,indexOk1087.2,lookup1087,rfl,threshold1087,
   n528,14217,pos528,cp528,ivec13,dvec13,dpos13,vp13,ivec46,dvec46,dpos46,vp46⟩

private def bk1092 : BoundKit true :=
  ⟨1092,eb1092,indexOk1092.1,indexOk1092.2,lookup1092,rfl,threshold1092,
   n529,65710974,pos529,cp529,ivec84,dvec84,dpos84,vp84,ivec164,dvec164,dpos164,vp164⟩

private def bk1094 : BoundKit true :=
  ⟨1094,eb1094,indexOk1094.1,indexOk1094.2,lookup1094,rfl,threshold1094,
   n530,46936410,pos530,cp530,ivec84,dvec84,dpos84,vp84,ivec164,dvec164,dpos164,vp164⟩

private def bk1095 : BoundKit true :=
  ⟨1095,eb1095,indexOk1095.1,indexOk1095.2,lookup1095,rfl,threshold1095,
   n531,28434,pos531,cp531,ivec13,dvec13,dpos13,vp13,ivec165,dvec165,dpos165,vp165⟩

private def bk1098 : BoundKit true :=
  ⟨1098,eb1098,indexOk1098.1,indexOk1098.2,lookup1098,rfl,threshold1098,
   n532,28434,pos532,cp532,ivec13,dvec13,dpos13,vp13,ivec143,dvec143,dpos143,vp143⟩

private def bk1099 : BoundKit false :=
  ⟨1099,eb1099,indexOk1099.1,indexOk1099.2,lookup1099,rfl,threshold1099,
   n559,7488217,pos559,cp559,ivec137,dvec137,dpos137,vp137,ivec123,dvec123,dpos123,vp123⟩

private def bk1100 : BoundKit false :=
  ⟨1100,eb1100,indexOk1100.1,indexOk1100.2,lookup1100,rfl,threshold1100,
   n558,161581,pos558,cp558,ivec136,dvec136,dpos136,vp136,ivec4,dvec4,dpos4,vp4⟩

private def bk1104 : BoundKit true :=
  ⟨1104,eb1104,indexOk1104.1,indexOk1104.2,lookup1104,rfl,threshold1104,
   n555,67856138,pos555,cp555,ivec135,dvec135,dpos135,vp135,ivec95,dvec95,dpos95,vp95⟩

private def bk1105 : BoundKit false :=
  ⟨1105,eb1105,indexOk1105.1,indexOk1105.2,lookup1105,rfl,threshold1105,
   n560,35398844,pos560,cp560,ivec137,dvec137,dpos137,vp137,ivec124,dvec124,dpos124,vp124⟩

private def bk1106 : BoundKit true :=
  ⟨1106,eb1106,indexOk1106.1,indexOk1106.2,lookup1106,rfl,threshold1106,
   n556,48468670,pos556,cp556,ivec135,dvec135,dpos135,vp135,ivec95,dvec95,dpos95,vp95⟩

private def bk1107 : BoundKit true :=
  ⟨1107,eb1107,indexOk1107.1,indexOk1107.2,lookup1107,rfl,threshold1107,
   n557,323162,pos557,cp557,ivec136,dvec136,dpos136,vp136,ivec97,dvec97,dpos97,vp97⟩

private def bk1108 : BoundKit false :=
  ⟨1108,eb1108,indexOk1108.1,indexOk1108.2,lookup1108,rfl,threshold1108,
   n561,132663949,pos561,cp561,ivec138,dvec138,dpos138,vp138,ivec123,dvec123,dpos123,vp123⟩

private def bk1116 : BoundKit true :=
  ⟨1116,eb1116,indexOk1116.1,indexOk1116.2,lookup1116,rfl,threshold1116,
   n562,30251,pos562,cp562,ivec107,dvec107,dpos107,vp107,ivec127,dvec127,dpos127,vp127⟩

private def bk1121 : BoundKit true :=
  ⟨1121,eb1121,indexOk1121.1,indexOk1121.2,lookup1121,rfl,threshold1121,
   n563,14248221,pos563,cp563,ivec107,dvec107,dpos107,vp107,ivec179,dvec179,dpos179,vp179⟩

private def bk1122 : BoundKit true :=
  ⟨1122,eb1122,indexOk1122.1,indexOk1122.2,lookup1122,rfl,threshold1122,
   n585,349762,pos585,cp585,ivec39,dvec39,dpos39,vp39,ivec185,dvec185,dpos185,vp185⟩

private def bk1123 : BoundKit true :=
  ⟨1123,eb1123,indexOk1123.1,indexOk1123.2,lookup1123,rfl,threshold1123,
   n588,4690,pos588,cp588,ivec65,dvec65,dpos65,vp65,ivec128,dvec128,dpos128,vp128⟩

private def bk1124 : BoundKit true :=
  ⟨1124,eb1124,indexOk1124.1,indexOk1124.2,lookup1124,rfl,threshold1124,
   n587,178450,pos587,cp587,ivec39,dvec39,dpos39,vp39,ivec185,dvec185,dpos185,vp185⟩

private def bk1125 : BoundKit true :=
  ⟨1125,eb1125,indexOk1125.1,indexOk1125.2,lookup1125,rfl,threshold1125,
   n565,97513,pos565,cp565,ivec109,dvec109,dpos109,vp109,ivec127,dvec127,dpos127,vp127⟩

private def bk1127 : BoundKit true :=
  ⟨1127,eb1127,indexOk1127.1,indexOk1127.2,lookup1127,rfl,threshold1127,
   n566,777,pos566,cp566,ivec8,dvec8,dpos8,vp8,ivec128,dvec128,dpos128,vp128⟩

private def bk1131 : BoundKit true :=
  ⟨1131,eb1131,indexOk1131.1,indexOk1131.2,lookup1131,rfl,threshold1131,
   n567,76405,pos567,cp567,ivec32,dvec32,dpos32,vp32,ivec129,dvec129,dpos129,vp129⟩

private def bk1135 : BoundKit true :=
  ⟨1135,eb1135,indexOk1135.1,indexOk1135.2,lookup1135,rfl,threshold1135,
   n568,272875,pos568,cp568,ivec32,dvec32,dpos32,vp32,ivec129,dvec129,dpos129,vp129⟩

private def bk1136 : BoundKit true :=
  ⟨1136,eb1136,indexOk1136.1,indexOk1136.2,lookup1136,rfl,threshold1136,
   n569,185,pos569,cp569,ivec8,dvec8,dpos8,vp8,ivec130,dvec130,dpos130,vp130⟩

private def bk1141 : BoundKit false :=
  ⟨1141,eb1141,indexOk1141.1,indexOk1141.2,lookup1141,rfl,threshold1141,
   n570,65508114,pos570,cp570,ivec180,dvec180,dpos180,vp180,ivec25,dvec25,dpos25,vp25⟩

private def bk1142 : BoundKit false :=
  ⟨1142,eb1142,indexOk1142.1,indexOk1142.2,lookup1142,rfl,threshold1142,
   n575,91184291,pos575,cp575,ivec182,dvec182,dpos182,vp182,ivec123,dvec123,dpos123,vp123⟩

private def bk1143 : BoundKit false :=
  ⟨1143,eb1143,indexOk1143.1,indexOk1143.2,lookup1143,rfl,threshold1143,
   n573,1439634,pos573,cp573,ivec181,dvec181,dpos181,vp181,ivec4,dvec4,dpos4,vp4⟩

private def bk1144 : BoundKit false :=
  ⟨1144,eb1144,indexOk1144.1,indexOk1144.2,lookup1144,rfl,threshold1144,
   n581,73186666,pos581,cp581,ivec184,dvec184,dpos184,vp184,ivec95,dvec95,dpos95,vp95⟩

private def bk1146 : BoundKit false :=
  ⟨1146,eb1146,indexOk1146.1,indexOk1146.2,lookup1146,rfl,threshold1146,
   n578,431053012,pos578,cp578,ivec182,dvec182,dpos182,vp182,ivec124,dvec124,dpos124,vp124⟩

private def bk1148 : BoundKit false :=
  ⟨1148,eb1148,indexOk1148.1,indexOk1148.2,lookup1148,rfl,threshold1148,
   n579,676813533,pos579,cp579,ivec183,dvec183,dpos183,vp183,ivec123,dvec123,dpos123,vp123⟩

private def bk1157 : BoundKit false :=
  ⟨1157,eb1157,indexOk1157.1,indexOk1157.2,lookup1157,rfl,threshold1157,
   n583,9358302,pos583,cp583,ivec180,dvec180,dpos180,vp180,ivec25,dvec25,dpos25,vp25⟩

private def bk1160 : BoundKit true :=
  ⟨1160,eb1160,indexOk1160.1,indexOk1160.2,lookup1160,rfl,threshold1160,
   n584,3066986,pos584,cp584,ivec105,dvec105,dpos105,vp105,ivec127,dvec127,dpos127,vp127⟩

private def bk1164 : BoundKit true :=
  ⟨1164,eb1164,indexOk1164.1,indexOk1164.2,lookup1164,rfl,threshold1164,
   n589,18519877,pos589,cp589,ivec105,dvec105,dpos105,vp105,ivec186,dvec186,dpos186,vp186⟩

private def bk1169 : BoundKit true :=
  ⟨1169,eb1169,indexOk1169.1,indexOk1169.2,lookup1169,rfl,threshold1169,
   n591,47361431,pos591,cp591,ivec106,dvec106,dpos106,vp106,ivec127,dvec127,dpos127,vp127⟩

private def bk1174 : BoundKit false :=
  ⟨1174,eb1174,indexOk1174.1,indexOk1174.2,lookup1174,rfl,threshold1174,
   n166,3029375,pos166,cp166,ivec187,dvec187,dpos187,vp187,ivec188,dvec188,dpos188,vp188⟩

private def bk1176 : BoundKit false :=
  ⟨1176,eb1176,indexOk1176.1,indexOk1176.2,lookup1176,rfl,threshold1176,
   n2,1938,pos2,cp2,ivec1,dvec1,dpos1,vp1,ivec4,dvec4,dpos4,vp4⟩

private def bk1178 : BoundKit true :=
  ⟨1178,eb1178,indexOk1178.1,indexOk1178.2,lookup1178,rfl,threshold1178,
   n11,2550,pos11,cp11,ivec1,dvec1,dpos1,vp1,ivec4,dvec4,dpos4,vp4⟩

private def bk1180 : BoundKit false :=
  ⟨1180,eb1180,indexOk1180.1,indexOk1180.2,lookup1180,rfl,threshold1180,
   n14,1938,pos14,cp14,ivec1,dvec1,dpos1,vp1,ivec7,dvec7,dpos7,vp7⟩

private def bk1182 : BoundKit true :=
  ⟨1182,eb1182,indexOk1182.1,indexOk1182.2,lookup1182,rfl,threshold1182,
   n17,2550,pos17,cp17,ivec1,dvec1,dpos1,vp1,ivec7,dvec7,dpos7,vp7⟩

private def bk1184 : BoundKit false :=
  ⟨1184,eb1184,indexOk1184.1,indexOk1184.2,lookup1184,rfl,threshold1184,
   n18,29526,pos18,cp18,ivec8,dvec8,dpos8,vp8,ivec7,dvec7,dpos7,vp7⟩

private def bk1186 : BoundKit true :=
  ⟨1186,eb1186,indexOk1186.1,indexOk1186.2,lookup1186,rfl,threshold1186,
   n21,38850,pos21,cp21,ivec8,dvec8,dpos8,vp8,ivec7,dvec7,dpos7,vp7⟩

private def bk1188 : BoundKit false :=
  ⟨1188,eb1188,indexOk1188.1,indexOk1188.2,lookup1188,rfl,threshold1188,
   n22,323,pos22,cp22,ivec1,dvec1,dpos1,vp1,ivec9,dvec9,dpos9,vp9⟩

private def bk1190 : BoundKit true :=
  ⟨1190,eb1190,indexOk1190.1,indexOk1190.2,lookup1190,rfl,threshold1190,
   n25,425,pos25,cp25,ivec1,dvec1,dpos1,vp1,ivec9,dvec9,dpos9,vp9⟩

private def bk1192 : BoundKit false :=
  ⟨1192,eb1192,indexOk1192.1,indexOk1192.2,lookup1192,rfl,threshold1192,
   n26,646,pos26,cp26,ivec1,dvec1,dpos1,vp1,ivec10,dvec10,dpos10,vp10⟩

private def bk1194 : BoundKit true :=
  ⟨1194,eb1194,indexOk1194.1,indexOk1194.2,lookup1194,rfl,threshold1194,
   n29,850,pos29,cp29,ivec1,dvec1,dpos1,vp1,ivec10,dvec10,dpos10,vp10⟩

private def bk1196 : BoundKit false :=
  ⟨1196,eb1196,indexOk1196.1,indexOk1196.2,lookup1196,rfl,threshold1196,
   n30,9842,pos30,cp30,ivec8,dvec8,dpos8,vp8,ivec9,dvec9,dpos9,vp9⟩

private def bk1198 : BoundKit true :=
  ⟨1198,eb1198,indexOk1198.1,indexOk1198.2,lookup1198,rfl,threshold1198,
   n31,12950,pos31,cp31,ivec8,dvec8,dpos8,vp8,ivec9,dvec9,dpos9,vp9⟩

private def bk1200 : BoundKit false :=
  ⟨1200,eb1200,indexOk1200.1,indexOk1200.2,lookup1200,rfl,threshold1200,
   n32,233966,pos32,cp32,ivec11,dvec11,dpos11,vp11,ivec7,dvec7,dpos7,vp7⟩

private def bk1202 : BoundKit true :=
  ⟨1202,eb1202,indexOk1202.1,indexOk1202.2,lookup1202,rfl,threshold1202,
   n35,61570,pos35,cp35,ivec11,dvec11,dpos11,vp11,ivec7,dvec7,dpos7,vp7⟩

private def bk1204 : BoundKit false :=
  ⟨1204,eb1204,indexOk1204.1,indexOk1204.2,lookup1204,rfl,threshold1204,
   n36,1101506,pos36,cp36,ivec12,dvec12,dpos12,vp12,ivec7,dvec7,dpos7,vp7⟩

private def bk1206 : BoundKit true :=
  ⟨1206,eb1206,indexOk1206.1,indexOk1206.2,lookup1206,rfl,threshold1206,
   n39,289870,pos39,cp39,ivec12,dvec12,dpos12,vp12,ivec7,dvec7,dpos7,vp7⟩

private def bk1208 : BoundKit false :=
  ⟨1208,eb1208,indexOk1208.1,indexOk1208.2,lookup1208,rfl,threshold1208,
   n40,233966,pos40,cp40,ivec11,dvec11,dpos11,vp11,ivec9,dvec9,dpos9,vp9⟩

private def bk1210 : BoundKit true :=
  ⟨1210,eb1210,indexOk1210.1,indexOk1210.2,lookup1210,rfl,threshold1210,
   n41,61570,pos41,cp41,ivec11,dvec11,dpos11,vp11,ivec9,dvec9,dpos9,vp9⟩

private def bk1212 : BoundKit false :=
  ⟨1212,eb1212,indexOk1212.1,indexOk1212.2,lookup1212,rfl,threshold1212,
   n42,116983,pos42,cp42,ivec11,dvec11,dpos11,vp11,ivec10,dvec10,dpos10,vp10⟩

private def bk1214 : BoundKit true :=
  ⟨1214,eb1214,indexOk1214.1,indexOk1214.2,lookup1214,rfl,threshold1214,
   n43,30785,pos43,cp43,ivec11,dvec11,dpos11,vp11,ivec10,dvec10,dpos10,vp10⟩

private def bk1216 : BoundKit false :=
  ⟨1216,eb1216,indexOk1216.1,indexOk1216.2,lookup1216,rfl,threshold1216,
   n44,13433,pos44,cp44,ivec12,dvec12,dpos12,vp12,ivec9,dvec9,dpos9,vp9⟩

private def bk1218 : BoundKit true :=
  ⟨1218,eb1218,indexOk1218.1,indexOk1218.2,lookup1218,rfl,threshold1218,
   n45,3535,pos45,cp45,ivec12,dvec12,dpos12,vp12,ivec9,dvec9,dpos9,vp9⟩

private def bk1220 : BoundKit false :=
  ⟨1220,eb1220,indexOk1220.1,indexOk1220.2,lookup1220,rfl,threshold1220,
   n46,180082,pos46,cp46,ivec13,dvec13,dpos13,vp13,ivec9,dvec9,dpos9,vp9⟩

private def bk1222 : BoundKit true :=
  ⟨1222,eb1222,indexOk1222.1,indexOk1222.2,lookup1222,rfl,threshold1222,
   n49,47390,pos49,cp49,ivec13,dvec13,dpos13,vp13,ivec9,dvec9,dpos9,vp9⟩

private def bk1224 : BoundKit false :=
  ⟨1224,eb1224,indexOk1224.1,indexOk1224.2,lookup1224,rfl,threshold1224,
   n50,1101506,pos50,cp50,ivec12,dvec12,dpos12,vp12,ivec10,dvec10,dpos10,vp10⟩

private def bk1226 : BoundKit true :=
  ⟨1226,eb1226,indexOk1226.1,indexOk1226.2,lookup1226,rfl,threshold1226,
   n51,289870,pos51,cp51,ivec12,dvec12,dpos12,vp12,ivec10,dvec10,dpos10,vp10⟩

private def bk1228 : BoundKit false :=
  ⟨1228,eb1228,indexOk1228.1,indexOk1228.2,lookup1228,rfl,threshold1228,
   n246,8911,pos246,cp246,ivec65,dvec65,dpos65,vp65,ivec4,dvec4,dpos4,vp4⟩

private def bk1230 : BoundKit true :=
  ⟨1230,eb1230,indexOk1230.1,indexOk1230.2,lookup1230,rfl,threshold1230,
   n247,11725,pos247,cp247,ivec65,dvec65,dpos65,vp65,ivec4,dvec4,dpos4,vp4⟩

private def bk1232 : BoundKit false :=
  ⟨1232,eb1232,indexOk1232.1,indexOk1232.2,lookup1232,rfl,threshold1232,
   n248,29526,pos248,cp248,ivec8,dvec8,dpos8,vp8,ivec4,dvec4,dpos4,vp4⟩

private def bk1234 : BoundKit true :=
  ⟨1234,eb1234,indexOk1234.1,indexOk1234.2,lookup1234,rfl,threshold1234,
   n280,38850,pos280,cp280,ivec8,dvec8,dpos8,vp8,ivec4,dvec4,dpos4,vp4⟩

private def bk1236 : BoundKit false :=
  ⟨1236,eb1236,indexOk1236.1,indexOk1236.2,lookup1236,rfl,threshold1236,
   n296,90041,pos296,cp296,ivec13,dvec13,dpos13,vp13,ivec10,dvec10,dpos10,vp10⟩

private def bk1238 : BoundKit true :=
  ⟨1238,eb1238,indexOk1238.1,indexOk1238.2,lookup1238,rfl,threshold1238,
   n297,23695,pos297,cp297,ivec13,dvec13,dpos13,vp13,ivec10,dvec10,dpos10,vp10⟩

private def integerPair (l : BoundKit true) (u : BoundKit false) (qn qd : ℤ)
    (h : 0 < qn ∧ 0 < qd ∧ ∀ i j,
      qn * ((l.cd*(u.xd i*l.yd j)*(u.cd*(l.xd i*u.yd j))) * 10^30) <
        numerator (crossN l.cn (u.xn i) (l.yn j) u.cn (l.xn i) (u.yn j)
          l.cd (u.xd i) (l.yd j) u.cd (l.xd i) (u.yd j)) * qd) :
    {p : LowerEarlyTerminalPair // lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p} := by
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
    {p : LowerEarlyTerminalPair // lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p} := by
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
private def pv001 := integerPair bk1 bk1176 34244109790744315933724393114736569756279 307433984000000000000000000000000000000000 (by decide +kernel)
private def pv002 := integerPair bk1178 bk395 168047138870237066775213536331828378706699 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv003 := integerPair bk1 bk1180 71698054322341395164759742482781204567529 307433984000000000000000000000000000000000 (by decide +kernel)
private def pv004 := integerPair bk1182 bk395 65010411237769891687665500979369642051899 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv005 := integerPair bk1 bk1184 2122011577754360571013270345488416242432001 14051541504000000000000000000000000000000000 (by decide +kernel)
private def pv006 := integerPair bk1186 bk395 826026889501101511897097935996507426582317 342791680000000000000000000000000000000000 (by decide +kernel)
private def pv007 := integerPair bk1 bk1188 74863086269137740493508018509038621977529 307433984000000000000000000000000000000000 (by decide +kernel)
private def pv008 := integerPair bk1190 bk395 56303330081738541250599757884968435253099 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv009 := integerPair bk1 bk1192 47564818208346711856373443427179830996279 307433984000000000000000000000000000000000 (by decide +kernel)
private def pv010 := integerPair bk1194 bk395 131401540595851921196504915499147921591099 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv011 := integerPair bk1 bk1196 338878150747114114825357006704840321453143 2007363072000000000000000000000000000000000 (by decide +kernel)
private def pv012 := integerPair bk1198 bk395 734276371591971827416536409728286431529917 342791680000000000000000000000000000000000 (by decide +kernel)
private def pv013 := integerPair bk1 bk1200 89540795739139932840502359334409301830657 473810022400000000000000000000000000000000 (by decide +kernel)
private def pv014 := integerPair bk1202 bk395 3801083773918095383809211214850293257964717 2037228160000000000000000000000000000000000 (by decide +kernel)
private def pv015 := integerPair bk1 bk1204 29117531193400074319940410698453217550113147 104842222284800000000000000000000000000000000 (by decide +kernel)
private def pv016 := integerPair bk1206 bk395 20900982756871005903158940398868824436611913 38364874240000000000000000000000000000000000 (by decide +kernel)
private def pv017 := integerPair bk1 bk1208 238573392421328714503715418461597376497941 1172056371200000000000000000000000000000000 (by decide +kernel)
private def pv018 := integerPair bk1210 bk395 3354761570909204294201702631024909844967817 2037228160000000000000000000000000000000000 (by decide +kernel)
private def pv019 := integerPair bk1 bk1212 91278601448027156643667554841196030561733 1172056371200000000000000000000000000000000 (by decide +kernel)
private def pv020 := integerPair bk1214 bk395 7204271889928891563702855398505894798170223 2037228160000000000000000000000000000000000 (by decide +kernel)
private def pv021 := integerPair bk1 bk1216 29818564890782895178300982306585359633183147 104842222284800000000000000000000000000000000 (by decide +kernel)
private def pv022 := integerPair bk1218 bk395 17043860681118571679199805113689677909562313 38364874240000000000000000000000000000000000 (by decide +kernel)
private def pv023 := integerPair bk1 bk1220 18445917175756010668046051340065465751053 58766910259200000000000000000000000000000 (by decide +kernel)
private def pv024 := integerPair bk1222 bk395 47631509373154528105812744602359324367299 8268962625000000000000000000000000000000000 (by decide +kernel)
private def pv025 := integerPair bk1 bk1224 23772178594374659658469033866706045622393111 104842222284800000000000000000000000000000000 (by decide +kernel)
private def pv026 := integerPair bk1226 bk395 2286880778863304354973395503182425733528291 1743857920000000000000000000000000000000000 (by decide +kernel)
private def pv027 := integerPair bk1 bk396 31282693081762777138135138545901263390448569 481433718937600000000000000000000000000000000 (by decide +kernel)
private def pv028 := integerPair bk110 bk397 19301789934607122063393225097494535882584127 390332852152320000000000000000000000000000000 (by decide +kernel)
private def pv029 := integerPair bk114 bk396 14873376167596911456530439303614187577612759 35396643735552000000000000000000000000000000 (by decide +kernel)
private def pv030 := integerPair bk115 bk398 188559414416846697631845702668494922834941 1030200825139200000000000000000000000000000 (by decide +kernel)
private def pv031 := integerPair bk399 bk395 46641926525018375921299515869578116038885523 110995440640000000000000000000000000000000000 (by decide +kernel)
private def pv032 := integerPair bk402 bk395 6551789336957096569027284804933583496179589 15856491520000000000000000000000000000000000 (by decide +kernel)
private def pv033 := integerPair bk404 bk395 10197684386973629725686389419632901989280047 14506771840000000000000000000000000000000000 (by decide +kernel)
private def pv034 := integerPair bk406 bk395 967601967912442699219035683785046573580114927 2338953541120000000000000000000000000000000000 (by decide +kernel)
private def pv035 := integerPair bk408 bk395 2815337537484161392143908407449377217497350347 28395319546880000000000000000000000000000000000 (by decide +kernel)
private def pv036 := integerPair bk403 bk395 1590511058901309324637576790859145810839417 19833477125000000000000000000000000000000000 (by decide +kernel)
private def pv037 := integerPair bk405 bk395 20719023658800093349875345195590897040693 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv038 := integerPair bk411 bk412 68152972576978293897872188616161472359457 92656778240000000000000000000000000000000 (by decide +kernel)
private def pv039 := integerPair bk411 bk414 390781098872761698437224556280586081090865809 624656571302400000000000000000000000000000000 (by decide +kernel)
private def pv040 := integerPair bk416 bk412 4332766309083329005914002375109780759069611 7273557091840000000000000000000000000000000 (by decide +kernel)
private def pv041 := integerPair bk416 bk395 19681586120211472113695574827439159832340550873 44240341370368000000000000000000000000000000000 (by decide +kernel)
private def pv042 := integerPair bk411 bk395 165033005658651159199618251055093044078435489 281785613824000000000000000000000000000000000 (by decide +kernel)
private def pv043 := integerPair bk420 bk412 7083827330718320247288958877368289302522737 11197215278080000000000000000000000000000000 (by decide +kernel)
private def pv044 := integerPair bk420 bk395 164175071161004655022081886592400743955189052811 340527076398080000000000000000000000000000000000 (by decide +kernel)
private def pv045 := integerPair bk1 bk422 19519940910944451487260766517184389708669 95284730112000000000000000000000000000000 (by decide +kernel)
private def pv046 := integerPair bk424 bk425 26695597384411278784487184589389809485771379239 60720481144565760000000000000000000000000000000 (by decide +kernel)
private def pv047 := integerPair bk426 bk422 673466925668878077084892451412306352301358971 665873681786880000000000000000000000000000000 (by decide +kernel)
private def pv048 := integerPair bk419 bk427 11805918148008677587052646518322813337745193 19285100283904000000000000000000000000000000 (by decide +kernel)
private def pv049 := integerPair bk415 bk422 29693727722162085854043778447062478421981 113275553280000000000000000000000000000000 (by decide +kernel)
private def pv050 := integerPair bk431 bk432 53116924806187906837948922097924522467505649147 106559182436904960000000000000000000000000000000 (by decide +kernel)
private def pv051 := integerPair bk431 bk433 120749483382647029207696978021892723458895019821 244032318561418240000000000000000000000000000000 (by decide +kernel)
private def pv052 := integerPair bk426 bk432 8738783371409088841131264065504166296105247769 8674354449223680000000000000000000000000000000 (by decide +kernel)
private def pv053 := integerPair bk419 bk434 327147685628690207172614912278243835486435831 538344691322880000000000000000000000000000000 (by decide +kernel)
private def pv054 := integerPair bk435 bk422 1646763553602273600806015468494603855535924783 1460688259545600000000000000000000000000000000 (by decide +kernel)
private def pv055 := integerPair bk435 bk425 85545336931917203593747858050653298977213211337 76113701740646400000000000000000000000000000000 (by decide +kernel)
private def pv056 := integerPair bk435 bk427 90483019954272691869839124235498451193714237807 81613576423475200000000000000000000000000000000 (by decide +kernel)
private def pv057 := integerPair bk436 bk437 412918040957731294298628228145196863403417 477400251648000000000000000000000000000000 (by decide +kernel)
private def pv058 := integerPair bk436 bk439 53540013699989386125370685390278347916653589 62191059809280000000000000000000000000000000 (by decide +kernel)
private def pv059 := integerPair bk426 bk437 184669855875363213338482123755209788133690739 187088478226227200000000000000000000000000000 (by decide +kernel)
private def pv060 := integerPair bk436 bk440 56429018004998560816596400348916897373658763 66684902935040000000000000000000000000000000 (by decide +kernel)
private def pv061 := integerPair bk441 bk412 8525642634181368296691840072923259083421 54923248640000000000000000000000000000000 (by decide +kernel)
private def pv062 := integerPair bk443 bk412 1008626017482169555667049281028633 2890000000000000000000000000000000 (by decide +kernel)
private def pv063 := integerPair bk441 bk395 7471583963865106670169218219207659327460229 11091921698000000000000000000000000000000000000 (by decide +kernel)
private def pv064 := integerPair bk443 bk395 11075445165540844513373076555411582351693 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv065 := integerPair bk431 bk395 8812262243260020876854663948905328729724129 101547402880000000000000000000000000000000000 (by decide +kernel)
private def pv066 := integerPair bk435 bk395 10370419668293079092687211611950892520378447 14506771840000000000000000000000000000000000 (by decide +kernel)
private def pv067 := integerPair bk436 bk395 26760995777509086109557687276943370388693 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv068 := integerPair bk1 bk446 22589453016037959283448408415450746274993827 166453134848000000000000000000000000000000000 (by decide +kernel)
private def pv069 := integerPair bk1 bk450 4611240135264812035270220491454709712171 43077126144000000000000000000000000000000 (by decide +kernel)
private def pv070 := integerPair bk452 bk449 1351894895990337316391862413663831700688461329 6568753887897600000000000000000000000000000000 (by decide +kernel)
private def pv071 := integerPair bk1 bk454 97448252926528796311325925317334088874769 954897222656000000000000000000000000000000 (by decide +kernel)
private def pv072 := integerPair bk456 bk449 9866436596943132010637887510346704356152549 20429579197440000000000000000000000000000000 (by decide +kernel)
private def pv073 := integerPair bk443 bk446 5877432379445691329178123291879831556921 10872601600000000000000000000000000000000 (by decide +kernel)
private def pv074 := integerPair bk443 bk450 179749665837453372045942063083634710964193 352072665600000000000000000000000000000000 (by decide +kernel)
private def pv075 := integerPair bk443 bk449 47741415960135445988893359151824627555563 89395842048000000000000000000000000000000 (by decide +kernel)
private def pv076 := integerPair bk443 bk454 197228537352564569014695911199428156545509 390222422720000000000000000000000000000000 (by decide +kernel)
private def pv077 := integerPair bk457 bk395 513973730032447119850552324749217930395730989 281785613824000000000000000000000000000000000 (by decide +kernel)
private def pv078 := integerPair bk460 bk395 68580915312026546117751660299977146021887201373 44240341370368000000000000000000000000000000000 (by decide +kernel)
private def pv079 := integerPair bk464 bk395 547966500488075408344383798478182920198706002811 340527076398080000000000000000000000000000000000 (by decide +kernel)
private def pv080 := integerPair bk1 bk466 1392623604546591627122344789084129640297 17538014208000000000000000000000000000000 (by decide +kernel)
private def pv081 := integerPair bk186 bk466 704847984104152812810572035841121768638369 1963300972339200000000000000000000000000000 (by decide +kernel)
private def pv082 := integerPair bk327 bk468 413403171057277334290787930717004088061702749 463348657314816000000000000000000000000000000 (by decide +kernel)
private def pv083 := integerPair bk329 bk466 671413856397538292530471138047973179830471653 330276680747520000000000000000000000000000000 (by decide +kernel)
private def pv084 := integerPair bk469 bk470 581507990931051178056494779545495528468351 433660857344000000000000000000000000000000 (by decide +kernel)
private def pv085 := integerPair bk456 bk466 59528775529884259898500718657017906897413 137646838784000000000000000000000000000000 (by decide +kernel)
private def pv086 := integerPair bk461 bk471 2337730129622041217518275645664745322851335581 2644865406310400000000000000000000000000000000 (by decide +kernel)
private def pv087 := integerPair bk327 bk472 24397004060876700963544255312906538744181949891 27589112065109504000000000000000000000000000000 (by decide +kernel)
private def pv088 := integerPair bk329 bk471 8714054318170736805143968356760277797787008963 4302523246494720000000000000000000000000000000 (by decide +kernel)
private def pv089 := integerPair bk469 bk473 7526919324243370874446847555971739950463113 5649311709184000000000000000000000000000000 (by decide +kernel)
private def pv090 := integerPair bk462 bk466 1581413905114161056295443958854064602780707 783896089600000000000000000000000000000000 (by decide +kernel)
private def pv091 := integerPair bk462 bk468 151950845847288879326405399199215100820801463 75567583037440000000000000000000000000000000 (by decide +kernel)
private def pv092 := integerPair bk462 bk470 1234304399916970750752246111217739337896807 623339059200000000000000000000000000000000 (by decide +kernel)
private def pv093 := integerPair bk463 bk474 28381621454127506654382319813253886210500759 19193181987840000000000000000000000000000000 (by decide +kernel)
private def pv094 := integerPair bk463 bk475 13136851898459369555823217866957089372155591 8929646446080000000000000000000000000000000 (by decide +kernel)
private def pv095 := integerPair bk329 bk474 3053192389512031087432259738939929188104090219 1535102560515840000000000000000000000000000000 (by decide +kernel)
private def pv096 := integerPair bk463 bk476 309823841095346073159929169727007722412516653 214940513948160000000000000000000000000000000 (by decide +kernel)
private def pv097 := integerPair bk477 bk162 28582664517915244540490263313223499635988632647 19676296768128000000000000000000000000000000000 (by decide +kernel)
private def pv098 := integerPair bk478 bk162 73806615523093627173187902427646020743317457503 59407280626848000000000000000000000000000000000 (by decide +kernel)
private def pv099 := integerPair bk479 bk162 9152769556220762488848592484313395089405481 6505213141504000000000000000000000000000000 (by decide +kernel)
private def pv100 := integerPair bk480 bk446 222350754939359992045865067488776597507348737 185578344855680000000000000000000000000000000 (by decide +kernel)
private def pv101 := integerPair bk481 bk164 285294833165931663970891815263145651544835211 279297834928640000000000000000000000000000000 (by decide +kernel)
private def pv102 := integerPair bk480 bk164 1544721667758049240997682214832372650133341 1302364963680000000000000000000000000000000 (by decide +kernel)
private def pv103 := integerPair bk482 bk164 19680577540898594517361377788967938525771029947 17173134777244160000000000000000000000000000000 (by decide +kernel)
private def pv104 := integerPair bk477 bk446 42885854559688139993928170332853856325917233 30732719530240000000000000000000000000000000 (by decide +kernel)
private def pv105 := integerPair bk478 bk447 6147492588439146426522182224110481676793793 5474572315520000000000000000000000000000000 (by decide +kernel)
private def pv106 := integerPair bk477 bk395 1052338875383856146340107063670349017750333861 999405172480000000000000000000000000000000000 (by decide +kernel)
private def pv107 := integerPair bk479 bk455 40236059375363825476518082914218511021870177 35380644790400000000000000000000000000000000 (by decide +kernel)
private def pv108 := integerPair bk483 bk446 62888502232086665667425057407066201045966971 46203258005632000000000000000000000000000000 (by decide +kernel)
private def pv109 := integerPair bk484 bk447 22489989208029831327081350249705754881355377 20576040863840000000000000000000000000000000 (by decide +kernel)
private def pv110 := integerPair bk483 bk183 8786552567171378901715236449106476123072682959 7043129634112000000000000000000000000000000000 (by decide +kernel)
private def pv111 := integerPair bk485 bk183 54572368813607891525834084619459549678321245091 45406545238912000000000000000000000000000000000 (by decide +kernel)
private def pv112 := integerPair bk355 bk486 201387649696246042100741158638944746114184683 253156298969600000000000000000000000000000000 (by decide +kernel)
private def pv113 := integerPair bk356 bk486 833442307808191727388184705941185852420003331 1222939659637760000000000000000000000000000000 (by decide +kernel)
private def pv114 := integerPair bk357 bk486 335464798431961669217398323480487008877789292767 476287650866227200000000000000000000000000000000 (by decide +kernel)
private def pv115 := integerPair bk488 bk487 224131262891381858402043998987353447073704771 340882393316352000000000000000000000000000000 (by decide +kernel)
private def pv116 := integerPair bk490 bk487 44004179253998967899304795916624031393658853 77440373853184000000000000000000000000000000 (by decide +kernel)
private def pv117 := integerPair bk349 bk487 711063003059975497420658102595145618041047 948035902080000000000000000000000000000000 (by decide +kernel)
private def pv118 := integerPair bk491 bk487 4408847900534596309909445502524684743816205261 7634944206928896000000000000000000000000000000 (by decide +kernel)
private def pv119 := integerPair bk355 bk165 80708979367877456850319758250229301858526951 137302408449024000000000000000000000000000000 (by decide +kernel)
private def pv120 := integerPair bk356 bk165 78577232965042079410003685384392520631045217 165819062511513600000000000000000000000000000 (by decide +kernel)
private def pv121 := integerPair bk357 bk165 1018193782435771415173592305630302881221908971 2050162066720768000000000000000000000000000000 (by decide +kernel)
private def pv122 := integerPair bk494 bk495 14759742497482122873726539633666959736657212441 21282136114636800000000000000000000000000000000 (by decide +kernel)
private def pv123 := integerPair bk496 bk495 14951940109526129169602474805585069410205022303 25702272076907520000000000000000000000000000000 (by decide +kernel)
private def pv124 := integerPair bk349 bk495 70962597276136820918722957709224706980411633 102034372512000000000000000000000000000000000 (by decide +kernel)
private def pv125 := integerPair bk497 bk495 99692132339987716831215138156260714176810621 165509918997280000000000000000000000000000000 (by decide +kernel)
private def pv126 := integerPair bk355 bk346 200581394283085025247179191485568933714131303 457901266461184000000000000000000000000000000 (by decide +kernel)
private def pv127 := integerPair bk356 bk395 2364898128233265597828853911083443011835286979 12322830826240000000000000000000000000000000000 (by decide +kernel)
private def pv128 := integerPair bk355 bk395 155708336982576933091434311666650797654465693 510180894080000000000000000000000000000000000 (by decide +kernel)
private def pv129 := integerPair bk357 bk395 891230007892375346822679363263335875078992649 4155208245760000000000000000000000000000000000 (by decide +kernel)
private def pv130 := integerPair bk1 bk498 30604079528059921054380919264111390228341 122799024128000000000000000000000000000000 (by decide +kernel)
private def pv131 := integerPair bk170 bk499 113671148704023875559773643307895372862780567717 286540357293876224000000000000000000000000000000 (by decide +kernel)
private def pv132 := integerPair bk172 bk498 53715302916921386614811378893992081935953341 60661435619840000000000000000000000000000000 (by decide +kernel)
private def pv133 := integerPair bk173 bk500 546096767619328468403921901193852562406972859 850538720306176000000000000000000000000000000 (by decide +kernel)
private def pv134 := integerPair bk225 bk501 176170983360298912885551405245305323510385852641 616777634891264000000000000000000000000000000000 (by decide +kernel)
private def pv135 := integerPair bk170 bk502 41894214326088083392480906732654857176946100509 106412290364323328000000000000000000000000000000 (by decide +kernel)
private def pv136 := integerPair bk172 bk501 25806937676302353780472942234980776302931750977 29238811968762880000000000000000000000000000000 (by decide +kernel)
private def pv137 := integerPair bk173 bk503 49541655428667629992654836477486164038919819277 77559936278730752000000000000000000000000000000 (by decide +kernel)
private def pv138 := integerPair bk229 bk498 4520521718674205354768339764831381625009410889 6763714431232000000000000000000000000000000000 (by decide +kernel)
private def pv139 := integerPair bk229 bk499 11733620709713531045831528762173637418367734851 17622218139750400000000000000000000000000000000 (by decide +kernel)
private def pv140 := integerPair bk229 bk500 40572133928373463872533809102175918244466011377 62221703352512000000000000000000000000000000000 (by decide +kernel)
private def pv141 := integerPair bk230 bk504 480690708432725046377892440626391138324308763 1033339407874048000000000000000000000000000000 (by decide +kernel)
private def pv142 := integerPair bk230 bk505 1244744218785453205894245663843032242775798087 2692268078893465600000000000000000000000000000 (by decide +kernel)
private def pv143 := integerPair bk172 bk504 198569727439596618950112886338156890832236983 227994463537280000000000000000000000000000000 (by decide +kernel)
private def pv144 := integerPair bk173 bk506 278061118753289142815471296102943700854379171 443110833561088000000000000000000000000000000 (by decide +kernel)
private def pv145 := integerPair bk507 bk218 2249349691125990224661101444106863974570710439 4561822993728000000000000000000000000000000000 (by decide +kernel)
private def pv146 := integerPair bk510 bk218 33236522008711924649700425110340950251915997 71971606246400000000000000000000000000000000 (by decide +kernel)
private def pv147 := integerPair bk512 bk218 2310227094439910329818413087868885267467877253 1799290156160000000000000000000000000000000000 (by decide +kernel)
private def pv148 := integerPair bk513 bk218 144262619626475332414836786375835632112837 208900853000000000000000000000000000000000 (by decide +kernel)
private def pv149 := integerPair bk516 bk395 589810966835684757279699855294403742328700259 2798291534720000000000000000000000000000000000 (by decide +kernel)
private def pv150 := integerPair bk510 bk395 107870180914226804999415050659997335943583927 383838667520000000000000000000000000000000000 (by decide +kernel)
private def pv151 := integerPair bk512 bk395 60313942520780787236560521513742591754503161 54834095360000000000000000000000000000000000 (by decide +kernel)
private def pv152 := integerPair bk513 bk395 1036394615153076074705962215210939525173673 2037228160000000000000000000000000000000000 (by decide +kernel)
private def pv153 := integerPair bk507 bk395 217755675439621850596629907134352492013133 697908640000000000000000000000000000000000 (by decide +kernel)
private def pv154 := integerPair bk519 bk395 3352272936280883734381207856048252241000368661 13933757826560000000000000000000000000000000000 (by decide +kernel)
private def pv155 := integerPair bk1 bk522 10768743700068329646137351860541451762667 55063444480000000000000000000000000000000 (by decide +kernel)
private def pv156 := integerPair bk1 bk523 311131129812121458236895222803110960869 1734875648000000000000000000000000000000 (by decide +kernel)
private def pv157 := integerPair bk1 bk524 11310306752320285305308600779927398906810459 65851149478400000000000000000000000000000000 (by decide +kernel)
private def pv158 := integerPair bk525 bk526 2899806802260961790715101483641253814441237001 1772094092787200000000000000000000000000000000 (by decide +kernel)
private def pv159 := integerPair bk527 bk526 11851750647724118394742439257806987076973049567 8560577617464320000000000000000000000000000000 (by decide +kernel)
private def pv160 := integerPair bk528 bk526 344680278102557607001097116212828139039238943341 238143825433113600000000000000000000000000000000 (by decide +kernel)
private def pv161 := integerPair bk529 bk216 53408840114655735107026879375043977464551177 39480729169408000000000000000000000000000000 (by decide +kernel)
private def pv162 := integerPair bk531 bk216 2604136297816064000329303904473514756474401157 2260208877545472000000000000000000000000000000 (by decide +kernel)
private def pv163 := integerPair bk512 bk216 620624228680489847648138415462158560244681 439203073280000000000000000000000000000000 (by decide +kernel)
private def pv164 := integerPair bk532 bk216 564453818208912946816648473362789958244443393 476147107211776000000000000000000000000000000 (by decide +kernel)
private def pv165 := integerPair bk525 bk395 1273162976511250186411664307310476762898282011 1020361788160000000000000000000000000000000000 (by decide +kernel)
private def pv166 := integerPair bk527 bk395 6145447429614379970931677459973033207469611927 6161415413120000000000000000000000000000000000 (by decide +kernel)
private def pv167 := integerPair bk528 bk395 4403839777058236926439504526182503563795368899 4155208245760000000000000000000000000000000000 (by decide +kernel)
private def pv168 := integerPair bk534 bk535 30066080638014390403136187001194372084105226501 21282136114636800000000000000000000000000000000 (by decide +kernel)
private def pv169 := integerPair bk536 bk535 14980602726901347196862358330828251722229407337 12851136038453760000000000000000000000000000000 (by decide +kernel)
private def pv170 := integerPair bk537 bk535 12962040017571609956681697664481583796815840457 10592634815825920000000000000000000000000000000 (by decide +kernel)
private def pv171 := integerPair bk1 bk538 1582513964254050571662356464592314435895833199 6254423074099200000000000000000000000000000000 (by decide +kernel)
private def pv172 := integerPair bk1 bk539 127013435986992075076586565556002644539 618599055360000000000000000000000000000 (by decide +kernel)
private def pv173 := integerPair bk1 bk540 77482642299817336709208578030207654802327 438333975040000000000000000000000000000000 (by decide +kernel)
private def pv174 := integerPair bk1 bk526 6404020981767790832123443967299869622356793 38846312960000000000000000000000000000000000 (by decide +kernel)
private def pv175 := integerPair bk1 bk547 140604012659969947857205524349600291285239 876667950080000000000000000000000000000000 (by decide +kernel)
private def pv176 := integerPair bk1 bk545 140693402222580202820597200222112814676524857 893489010585600000000000000000000000000000000 (by decide +kernel)
private def pv177 := integerPair bk533 bk538 303113487156296080911514303605984948289171501 1078879569277440000000000000000000000000000000 (by decide +kernel)
private def pv178 := integerPair bk533 bk539 702025195096737211169906230908189839607 3039357650000000000000000000000000000000 (by decide +kernel)
private def pv179 := integerPair bk533 bk540 735751470444482018825120095652662469048141503 3659621826995200000000000000000000000000000000 (by decide +kernel)
private def pv180 := integerPair bk533 bk545 696756046541909029627164991789510115104771423 3853141318848000000000000000000000000000000000 (by decide +kernel)
private def pv181 := integerPair bk1 bk550 1580322849299539721292478179527587107775103 10235972531200000000000000000000000000000000 (by decide +kernel)
private def pv182 := integerPair bk553 bk359 430893134507142415202050976662885590263002161871 808240966768342016000000000000000000000000000000 (by decide +kernel)
private def pv183 := integerPair bk554 bk257 48491318903300977438711763394825973124385223 175125070909644800000000000000000000000000000 (by decide +kernel)
private def pv184 := integerPair bk553 bk395 5306934640395061209353729242782063680809866693 16568499513280000000000000000000000000000000000 (by decide +kernel)
private def pv185 := integerPair bk555 bk395 1167049943275665082224210249147979935919546653807 4877415909583360000000000000000000000000000000000 (by decide +kernel)
private def pv186 := integerPair bk1 bk556 4332710100264181677640908416228603602272993 15999190088960000000000000000000000000000000 (by decide +kernel)
private def pv187 := integerPair bk1 bk557 3254987634438371804408056686319103999243 12408223293440000000000000000000000000000 (by decide +kernel)
private def pv188 := integerPair bk1 bk558 57504359438249975033569759134846040442818847 223221422228480000000000000000000000000000000 (by decide +kernel)
private def pv189 := integerPair bk1 bk1228 1567220850523264095313259879112299899591249 8481561088000000000000000000000000000000000 (by decide +kernel)
private def pv190 := integerPair bk1230 bk559 3687601823545405048673809774127976672796853 1814707328000000000000000000000000000000000 (by decide +kernel)
private def pv191 := integerPair bk1 bk560 16469803192756227567143076227039940533437 160417422880000000000000000000000000000000 (by decide +kernel)
private def pv192 := integerPair bk564 bk560 63310396201274921111336338632312058870091 161884392320000000000000000000000000000000 (by decide +kernel)
private def pv193 := integerPair bk567 bk568 193283243366319743099764128817020457946054611 218958462929920000000000000000000000000000000 (by decide +kernel)
private def pv194 := integerPair bk569 bk560 68471943440075731455260890302756824404176603 34493456488960000000000000000000000000000000 (by decide +kernel)
private def pv195 := integerPair bk570 bk571 408222201891377805822569818715056435978653 310115199180800000000000000000000000000000 (by decide +kernel)
private def pv196 := integerPair bk1 bk573 5863774902819796029567038169157177407169 77579797152000000000000000000000000000000 (by decide +kernel)
private def pv197 := integerPair bk564 bk573 29554372163937005359877133486405936987441491 81420810885120000000000000000000000000000000 (by decide +kernel)
private def pv198 := integerPair bk567 bk575 342293593172310834136315007688166253270579 401086703360000000000000000000000000000000 (by decide +kernel)
private def pv199 := integerPair bk569 bk573 8521869220623744813801497712650777559515039 4354595607040000000000000000000000000000000 (by decide +kernel)
private def pv200 := integerPair bk570 bk576 45659174403606652236485574509947337314801387 35541055775680000000000000000000000000000000 (by decide +kernel)
private def pv201 := integerPair bk577 bk560 194413702969299140569353799721837586162923213 605330269721600000000000000000000000000000000 (by decide +kernel)
private def pv202 := integerPair bk578 bk579 14434015230842914261243101521275432023179 92738224560000000000000000000000000000000 (by decide +kernel)
private def pv203 := integerPair bk564 bk579 238521063535893481158631868856084155499113 682262389312000000000000000000000000000000 (by decide +kernel)
private def pv204 := integerPair bk567 bk581 484674370579424425937194441867764493613028401 576750798585920000000000000000000000000000000 (by decide +kernel)
private def pv205 := integerPair bk569 bk579 2825141581609407392983949394753073029348998931 1453728040271360000000000000000000000000000000 (by decide +kernel)
private def pv206 := integerPair bk570 bk582 728899847821733346398496905883095950005583797 571804489634560000000000000000000000000000000 (by decide +kernel)
private def pv207 := integerPair bk583 bk584 462477333853974183961726982898220385995958476019 249703651710356480000000000000000000000000000000 (by decide +kernel)
private def pv208 := integerPair bk586 bk585 213984083103482394490735492160585644597897947879 140621616002513920000000000000000000000000000000 (by decide +kernel)
private def pv209 := integerPair bk583 bk559 22070648957848093100826139508500729306642577203 13702614568078800000000000000000000000000000000 (by decide +kernel)
private def pv210 := integerPair bk590 bk591 4502504589641298567397997298115328777724769514201 2754291363137267200000000000000000000000000000000 (by decide +kernel)
private def pv211 := integerPair bk592 bk584 1366980932229382229692176015545220698580479707 4257528527336448000000000000000000000000000000 (by decide +kernel)
private def pv212 := integerPair bk424 bk584 673664992767104052349840377178927785765177 1651471435264000000000000000000000000000000 (by decide +kernel)
private def pv213 := integerPair bk426 bk584 40349233480510834196647450487757965326833261 41286785881600000000000000000000000000000000 (by decide +kernel)
private def pv214 := integerPair bk419 bk584 153090194510969526651070090994219635482127 256813294080000000000000000000000000000000 (by decide +kernel)
private def pv215 := integerPair bk595 bk585 2351046926065537586802336301772697796858901921 11988221589672960000000000000000000000000000000 (by decide +kernel)
private def pv216 := integerPair bk424 bk585 189138711228135972813644260844673256311091 539063587328000000000000000000000000000000 (by decide +kernel)
private def pv217 := integerPair bk426 bk585 1771472648158331377292334901554312128134369 1925227097600000000000000000000000000000000 (by decide +kernel)
private def pv218 := integerPair bk419 bk585 174437541402764485791876037867209422419 323658240000000000000000000000000000000 (by decide +kernel)
private def pv219 := integerPair bk592 bk559 4030942649613899918577506911903878889456538533 49841928081254400000000000000000000000000000000 (by decide +kernel)
private def pv220 := integerPair bk424 bk559 283766737802820818354445148958991820267733 1691672879680000000000000000000000000000000 (by decide +kernel)
private def pv221 := integerPair bk426 bk559 8899686695653271063030600873402818300709857 12083377712000000000000000000000000000000000 (by decide +kernel)
private def pv222 := integerPair bk419 bk559 7632946284977606558960929675383561572659 21474681600000000000000000000000000000000 (by decide +kernel)
private def pv223 := integerPair bk598 bk591 12140801812174392382130010219702402278108586871 117403910303596800000000000000000000000000000000 (by decide +kernel)
private def pv224 := integerPair bk424 bk591 9501975984254865677240737423482690819789837 41286785881600000000000000000000000000000000 (by decide +kernel)
private def pv225 := integerPair bk426 bk591 4715654949369728366448882640252494500356239 5898112268800000000000000000000000000000000 (by decide +kernel)
private def pv226 := integerPair bk419 bk591 599207206640799253765007114716408847309 1433109900000000000000000000000000000000 (by decide +kernel)
private def pv227 := integerPair bk564 bk559 80442879943957818597621325485163598686077 362941465600000000000000000000000000000000 (by decide +kernel)
private def pv228 := integerPair bk601 bk1232 83019858976511189793447186957458912993 60129108480000000000000000000000000000000 (by decide +kernel)
private def pv229 := integerPair bk1234 bk395 382354453567036296624956779626012046438963 68558336000000000000000000000000000000000 (by decide +kernel)
private def pv230 := integerPair bk601 bk560 92877354931465293630250409886144402430963259 547791413668800000000000000000000000000000000 (by decide +kernel)
private def pv231 := integerPair bk603 bk571 5660239912613876123400841585559461431285173 4281441182720000000000000000000000000000000 (by decide +kernel)
private def pv232 := integerPair bk601 bk573 25983425573425503727813906610131027042014557069 183676842704947200000000000000000000000000000000 (by decide +kernel)
private def pv233 := integerPair bk603 bk576 303910068087485076136743111330792724770592073 235525802453760000000000000000000000000000000 (by decide +kernel)
private def pv234 := integerPair bk603 bk582 404311050327402437278797776127189062897271957 315772628604160000000000000000000000000000000 (by decide +kernel)
private def pv235 := integerPair bk604 bk395 629303545024659650997311899082330001826095789 281785613824000000000000000000000000000000000 (by decide +kernel)
private def pv236 := integerPair bk606 bk395 82177626046559375841136652837135326137443563173 44240341370368000000000000000000000000000000000 (by decide +kernel)
private def pv237 := integerPair bk609 bk395 168703740854082586221341994643774653390370130967 85131769099520000000000000000000000000000000000 (by decide +kernel)
private def pv238 := integerPair bk611 bk395 558050443915231816722663779407524777097381 800756070400000000000000000000000000000000 (by decide +kernel)
private def pv239 := integerPair bk612 bk395 68938732818072624055901345199496539794568767 125718703052800000000000000000000000000000000 (by decide +kernel)
private def pv240 := integerPair bk613 bk395 7569305450853002422709370153505184542058931 12906040576000000000000000000000000000000000 (by decide +kernel)
private def pv241 := integerPair bk607 bk395 299239841480596525445349941243331231458033019 505617728000000000000000000000000000000000000 (by decide +kernel)
private def pv242 := integerPair bk426 bk395 19756831277186433593522406325187941860840843 33065500160000000000000000000000000000000000 (by decide +kernel)
private def pv243 := integerPair bk608 bk395 61654621783265609088700793351303756833499259 36115552000000000000000000000000000000000000 (by decide +kernel)
private def pv244 := integerPair bk603 bk395 179654086059519812721150652834194531184791 171395840000000000000000000000000000000000 (by decide +kernel)
private def pv245 := integerPair bk621 bk162 2283097495249337198400010985932808479942802021 9123645987456000000000000000000000000000000000 (by decide +kernel)
private def pv246 := integerPair bk348 bk162 19004479799529745091292980538145404109408507 71971606246400000000000000000000000000000000 (by decide +kernel)
private def pv247 := integerPair bk349 bk162 176951528228510257650342408825615768022917949 257041450880000000000000000000000000000000000 (by decide +kernel)
private def pv248 := integerPair bk230 bk162 1559229581372378791355945847889809381590609 3819901312000000000000000000000000000000000 (by decide +kernel)
private def pv249 := integerPair bk624 bk164 37197114964663215916710633589539624537583063 285036032497920000000000000000000000000000000 (by decide +kernel)
private def pv250 := integerPair bk348 bk164 204999784495081946052088570489649285461093 1042615701299200000000000000000000000000000 (by decide +kernel)
private def pv251 := integerPair bk349 bk164 11558596841137613013500004381415314729114527 18618137523200000000000000000000000000000000 (by decide +kernel)
private def pv252 := integerPair bk230 bk164 94247798199279517785527528386949046583927 276684743680000000000000000000000000000000 (by decide +kernel)
private def pv253 := integerPair bk621 bk620 17446960550955090958223556976389974821697 406315419699200000000000000000000000000000 (by decide +kernel)
private def pv254 := integerPair bk348 bk620 9969498787439803373575339181014236005443097 175004298692608000000000000000000000000000000 (by decide +kernel)
private def pv255 := integerPair bk349 bk620 12040628573485274044357011546194127654599711 25000614098944000000000000000000000000000000 (by decide +kernel)
private def pv256 := integerPair bk230 bk620 373379973417255511581182266188034918482877 1857674672128000000000000000000000000000000 (by decide +kernel)
private def pv257 := integerPair bk627 bk183 72858338467840599363940674542742034989390233 1632904356512000000000000000000000000000000000 (by decide +kernel)
private def pv258 := integerPair bk348 bk183 1341366460525034665626269584347596223486431 14394321249280000000000000000000000000000000 (by decide +kernel)
private def pv259 := integerPair bk349 bk183 133031358596708215639050863767017828765859549 257041450880000000000000000000000000000000000 (by decide +kernel)
private def pv260 := integerPair bk230 bk183 905896362489341897082165877022804163011489 3819901312000000000000000000000000000000000 (by decide +kernel)
private def pv261 := integerPair bk186 bk620 480979948174585877501803721655873712182781 1857674672128000000000000000000000000000000 (by decide +kernel)
private def pv262 := zeroPair bk630 bk620 (by rfl) (Or.inr rfl)
private def pv263 := integerPair bk170 bk162 2503039415228675125627250515364356332417209 7640139005800000000000000000000000000000000 (by decide +kernel)
private def pv264 := integerPair bk173 bk162 16482915052240381208380023561598388344251 28099997800000000000000000000000000000000 (by decide +kernel)
private def pv265 := integerPair bk630 bk164 1854887335945007609627002932100075415236727 13240872663040000000000000000000000000000000 (by decide +kernel)
private def pv266 := integerPair bk170 bk164 143845001921042325280523458199828650369407 553393852312000000000000000000000000000000 (by decide +kernel)
private def pv267 := integerPair bk172 bk164 42109173548821473587589714796953833121771 56468760440000000000000000000000000000000 (by decide +kernel)
private def pv268 := integerPair bk173 bk164 1055878813758829678641788113829467759189 2035351192000000000000000000000000000000 (by decide +kernel)
private def pv269 := integerPair bk170 bk631 202571642670832952515220069470860856291909211 2377928276297728000000000000000000000000000000 (by decide +kernel)
private def pv270 := integerPair bk173 bk632 51479900006511563799573496769936419197952089 160912730868736000000000000000000000000000000 (by decide +kernel)
private def pv271 := integerPair bk630 bk165 159183489172667249158772051393466311685667 1749177057689600000000000000000000000000000 (by decide +kernel)
private def pv272 := integerPair bk630 bk183 6645923697519378465777392090153457376998259 182803092736000000000000000000000000000000000 (by decide +kernel)
private def pv273 := integerPair bk170 bk183 1193193533465388363250169619814869263617649 7640139005800000000000000000000000000000000 (by decide +kernel)
private def pv274 := integerPair bk172 bk183 2503039415228675125627250515364356332417209 3898030105000000000000000000000000000000000 (by decide +kernel)
private def pv275 := integerPair bk173 bk183 93305719118476933910342277505906720191 224799982400000000000000000000000000000 (by decide +kernel)
private def pv276 := integerPair bk186 bk631 2708534895607341338979347507394357470932871 12074885368832000000000000000000000000000000 (by decide +kernel)
private def pv277 := integerPair bk1 bk1236 115541728938981450231380431388253764209721 411368371814400000000000000000000000000000 (by decide +kernel)
private def pv278 := integerPair bk1238 bk395 31630302816194022566256019305199520772519 62721612800000000000000000000000000000000 (by decide +kernel)
private def pv279 := integerPair bk639 bk395 48007584541804630248273411041809162480680507 159127215589760000000000000000000000000000000000 (by decide +kernel)
private def pv280 := integerPair bk145 bk395 23979613993931460898757378826242356858077 196873600000000000000000000000000000000000 (by decide +kernel)
private def pv281 := integerPair bk146 bk395 22025408884037388259484161715104134368811 28124800000000000000000000000000000000000 (by decide +kernel)
private def pv282 := integerPair bk147 bk395 4065845521289464991577458165995244607 9400000000000000000000000000000000000 (by decide +kernel)
private def pv283 := integerPair bk642 bk375 55935264188168631550742875726025724500737743577 170325864158677248000000000000000000000000000000 (by decide +kernel)
private def pv284 := integerPair bk145 bk375 441663632408793026867882397504742845833 893669246400000000000000000000000000000 (by decide +kernel)
private def pv285 := integerPair bk146 bk375 129599177281473617004198626168886549169453 111708655800000000000000000000000000000000 (by decide +kernel)
private def pv286 := integerPair bk147 bk375 213939632610931513781799605015432668063 262843896000000000000000000000000000000 (by decide +kernel)
private def pv287 := integerPair bk642 bk297 3616733723952235564694637711292552305034927 14740446919833600000000000000000000000000000 (by decide +kernel)
private def pv288 := integerPair bk145 bk297 27862721161196671358500143158213867087 67672920000000000000000000000000000000 (by decide +kernel)
private def pv289 := integerPair bk146 bk297 10420058512862493021725320453429652081 9667560000000000000000000000000000000 (by decide +kernel)
private def pv290 := integerPair bk147 bk297 415147058769519684504666001926650867 568680000000000000000000000000000000 (by decide +kernel)
private def pv291 := integerPair bk642 bk376 10744380710484479150078769219102909166446213137 68280156588131072000000000000000000000000000000 (by decide +kernel)
private def pv292 := integerPair bk145 bk376 2601344997835782592593979894828380077360277 8024883543040000000000000000000000000000000 (by decide +kernel)
private def pv293 := integerPair bk146 bk376 5673958769244768518894576572100867213939103 5732059673600000000000000000000000000000000 (by decide +kernel)
private def pv294 := integerPair bk147 bk376 8640620298969423341917105986191230308983 13487199232000000000000000000000000000000 (by decide +kernel)
private def pv295 := integerPair bk642 bk380 3302487630514485583344239431078667617361072983 24332266308382464000000000000000000000000000000 (by decide +kernel)
private def pv296 := integerPair bk145 bk380 4830909529968543276702551558266900541251 15958379400000000000000000000000000000000 (by decide +kernel)
private def pv297 := integerPair bk146 bk380 3091645426861551188075176782533199920831 3191675880000000000000000000000000000000 (by decide +kernel)
private def pv298 := integerPair bk147 bk380 581005963942763327660240786746016408737 938728200000000000000000000000000000000 (by decide +kernel)
private def pv299 := integerPair bk1 bk645 134477383635974984884875572601061632484685091 551946522423296000000000000000000000000000000 (by decide +kernel)
private def pv300 := integerPair bk655 bk645 37394156566766802792909050792373390481703717 95784474575854400000000000000000000000000000 (by decide +kernel)
private def pv301 := integerPair bk656 bk645 16923535272725238691587219544980372433183611 60659909095844800000000000000000000000000000 (by decide +kernel)
private def pv302 := integerPair bk1 bk647 25575540353696254102609541068094651644624351 121294033203200000000000000000000000000000000 (by decide +kernel)
private def pv303 := integerPair bk655 bk647 214380809905838640966229226217868387818321 601408431928000000000000000000000000000000 (by decide +kernel)
private def pv304 := integerPair bk656 bk647 653361458633016620758965634479834852254809 2666086198232000000000000000000000000000000 (by decide +kernel)
private def pv305 := integerPair bk1 bk648 19640717844391852210432533759585643923917489 99564256563200000000000000000000000000000000 (by decide +kernel)
private def pv306 := integerPair bk1 bk646 16385924701107302808162902543830339051083 115455042560000000000000000000000000000000 (by decide +kernel)
private def pv307 := integerPair bk1 bk654 45834003459624588243056053564606968155751 375228888320000000000000000000000000000000 (by decide +kernel)
private def pv308 := integerPair bk655 bk646 46228976247200551391466130568050051017033795577 162098614207642112000000000000000000000000000000 (by decide +kernel)
private def pv309 := integerPair bk656 bk657 7465905506965432755728678848692433013634348247 52504180444203136000000000000000000000000000000 (by decide +kernel)
private def pv310 := integerPair bk1 bk666 11330942773192599740020515912577607858203221 78849503203328000000000000000000000000000000 (by decide +kernel)
private def pv311 := integerPair bk655 bk666 14025844983897487087948397516677687493671277 48869629885640000000000000000000000000000000 (by decide +kernel)
private def pv312 := integerPair bk656 bk666 38039143900985000186544419697206933564999877 216642532485160000000000000000000000000000000 (by decide +kernel)
private def pv313 := integerPair bk669 bk648 2381719885380335182566501459316726919157 10527487456000000000000000000000000000000 (by decide +kernel)
private def pv314 := integerPair bk669 bk646 144400569420343026030295088507430078895607 854367314944000000000000000000000000000000 (by decide +kernel)
private def pv315 := integerPair bk669 bk654 2550196309379637469845837408172110130646307 17165016054784000000000000000000000000000000 (by decide +kernel)
private def pv316 := integerPair bk670 bk395 89216071903372845214609816881441374081963566347 28395319546880000000000000000000000000000000000 (by decide +kernel)
private def pv317 := integerPair bk673 bk395 277409692291205681411854630031213576484199 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv318 := integerPair bk677 bk395 2948166706616366128010658381150354009130791 853339520000000000000000000000000000000000 (by decide +kernel)
private def pv319 := integerPair bk679 bk395 499463063080647494741096672782057215553209 68267161600000000000000000000000000000000 (by decide +kernel)
private def pv320 := integerPair bk680 bk395 317423852015614460993958228810630887140449 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv321 := integerPair bk1 bk683 82888824037794616295964821141658541761905219 275973261211648000000000000000000000000000000 (by decide +kernel)
private def pv322 := integerPair bk1 bk685 17064806905585681404991941046599339955656593 60647016601600000000000000000000000000000000 (by decide +kernel)
private def pv323 := integerPair bk1 bk686 27370040927540464160334178177115402752415953 99564256563200000000000000000000000000000000 (by decide +kernel)
private def pv324 := integerPair bk1 bk684 28630925530468423261315061555995703131113 115455042560000000000000000000000000000000 (by decide +kernel)
private def pv325 := integerPair bk1 bk692 10105959239889384547718103563601144830973 42279311360000000000000000000000000000000 (by decide +kernel)
private def pv326 := integerPair bk1 bk695 30433009432435989413136557482038306794163099 130500785958400000000000000000000000000000000 (by decide +kernel)
private def pv327 := integerPair bk1 bk704 20095016816284589097995655423609137776883637 78849503203328000000000000000000000000000000 (by decide +kernel)
private def pv328 := integerPair bk708 bk395 34897452052123743156900500269648443979913614347 28395319546880000000000000000000000000000000000 (by decide +kernel)
private def pv329 := integerPair bk711 bk395 113831807337822590480215118220955610521449 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv330 := integerPair bk715 bk395 143465052102536472321107017995900548343399129 101547402880000000000000000000000000000000000 (by decide +kernel)
private def pv331 := integerPair bk717 bk395 48073200828890485497077870745109554012207447 14506771840000000000000000000000000000000000 (by decide +kernel)
private def pv332 := integerPair bk718 bk395 141681662506011101069359222971430058738199 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv333 := integerPair bk1 bk721 230320520452602933593587577421027839463369563 860208853504000000000000000000000000000000000 (by decide +kernel)
private def pv334 := integerPair bk731 bk721 32262183728895728996412370441125798645286429 87608381210420000000000000000000000000000000 (by decide +kernel)
private def pv335 := integerPair bk1 bk723 9459202185431064480004274787116029751486857 40112044544000000000000000000000000000000000 (by decide +kernel)
private def pv336 := integerPair bk731 bk723 855529551377590810150142626307053231940241 2553268949762500000000000000000000000000000 (by decide +kernel)
private def pv337 := integerPair bk1 bk724 6795541848997154749099739405302317426018333 30758817689600000000000000000000000000000000 (by decide +kernel)
private def pv338 := integerPair bk1 bk722 6759345119201647823636017961928963370941 38339671040000000000000000000000000000000 (by decide +kernel)
private def pv339 := integerPair bk1 bk730 160286269235948813849814017164401935512101 996831447040000000000000000000000000000000 (by decide +kernel)
private def pv340 := integerPair bk731 bk722 50785636372224654479364596964548029959658607697 185827286354631680000000000000000000000000000000 (by decide +kernel)
private def pv341 := integerPair bk1 bk733 6642086070839835208770714272675925602278573 44150562227200000000000000000000000000000000 (by decide +kernel)
private def pv342 := integerPair bk1 bk742 23312492819355336639096371629370924058494909 122886979072000000000000000000000000000000000 (by decide +kernel)
private def pv343 := integerPair bk731 bk742 17971639475119870152799028171468795109374291 62577415150300000000000000000000000000000000 (by decide +kernel)
private def pv344 := integerPair bk746 bk395 2277393492653338109712549690636244488678761 800756070400000000000000000000000000000000 (by decide +kernel)
private def pv345 := integerPair bk751 bk395 300872196223211233988157091559128221495900147 125718703052800000000000000000000000000000000 (by decide +kernel)
private def pv346 := integerPair bk755 bk395 32865495684261475304834028868927470147030531 12906040576000000000000000000000000000000000 (by decide +kernel)
private def pv347 := integerPair bk757 bk395 670240194849448704690829413685335592048041 171395840000000000000000000000000000000000 (by decide +kernel)
private def pv348 := integerPair bk761 bk395 753226749563784181210628479185800152039768413 252808864000000000000000000000000000000000000 (by decide +kernel)
private def pv349 := integerPair bk765 bk395 461329067707683332530655551498521473569682721 72231104000000000000000000000000000000000000 (by decide +kernel)
private def pv350 := integerPair bk766 bk395 326789423955178618271985094778070046828863 68558336000000000000000000000000000000000 (by decide +kernel)
private def pv351 := integerPair bk1 bk771 702564821228404524055698424590800625532783559 2338588424972800000000000000000000000000000000 (by decide +kernel)
private def pv352 := integerPair bk1 bk773 1751450285041851173574705667933412173405019 6222766035200000000000000000000000000000000 (by decide +kernel)
private def pv353 := integerPair bk1 bk772 2697165715199219170638446073359088498843 10495912960000000000000000000000000000000 (by decide +kernel)
private def pv354 := integerPair bk1 bk780 681186834230664865671015759428716502150308883 2672672485683200000000000000000000000000000000 (by decide +kernel)
private def pv355 := integerPair bk1 bk783 67814751971355527840168877359955289158873 272893736960000000000000000000000000000000 (by decide +kernel)
private def pv356 := integerPair bk1 bk788 50232830264889233455445243245234114670087 205576467200000000000000000000000000000000 (by decide +kernel)
private def pv357 := integerPair bk792 bk395 30325264175157490140338299144305776772656710347 28395319546880000000000000000000000000000000000 (by decide +kernel)
private def pv358 := integerPair bk795 bk395 108096213065210219306843911513706917838469129 101547402880000000000000000000000000000000000 (by decide +kernel)
private def pv359 := integerPair bk797 bk395 38169925898439134653084200930095337470827047 14506771840000000000000000000000000000000000 (by decide +kernel)
private def pv360 := integerPair bk798 bk395 102853351514165483018403784795447609449449 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv361 := integerPair bk1 bk801 4788353107934124285708416658799080994891284457 18708707399782400000000000000000000000000000000 (by decide +kernel)
private def pv362 := integerPair bk1 bk803 22389695564727998699335334698130622503007089 99564256563200000000000000000000000000000000 (by decide +kernel)
private def pv363 := integerPair bk1 bk802 61238267891368403986346030985524628948141 375228888320000000000000000000000000000000 (by decide +kernel)
private def pv364 := integerPair bk1 bk808 448180504900593531784607952809065797445507951 2672672485683200000000000000000000000000000000 (by decide +kernel)
private def pv365 := integerPair bk810 bk395 1488764322403847167354835617654793484651524901 604155735040000000000000000000000000000000000 (by decide +kernel)
private def pv366 := integerPair bk813 bk395 253317433302128798088688741352040018689244129 101547402880000000000000000000000000000000000 (by decide +kernel)
private def pv367 := integerPair bk815 bk395 78831867564776336712000753284828605709044047 14506771840000000000000000000000000000000000 (by decide +kernel)
private def pv368 := integerPair bk816 bk395 222895830687391821764714581133699541418199 56249600000000000000000000000000000000000 (by decide +kernel)
private def pv369 := integerPair bk1 bk819 1720065697528583975204959071410811876924405673 6458601499750400000000000000000000000000000000 (by decide +kernel)
private def pv370 := integerPair bk1 bk821 7150409897230509487508554055683326438708333 30758817689600000000000000000000000000000000 (by decide +kernel)
private def pv371 := integerPair bk1 bk820 668740181920210821511006238886354438711 3485424640000000000000000000000000000000 (by decide +kernel)
private def pv372 := integerPair bk1 bk827 172256552119851645334954022887495232098268959 922657357107200000000000000000000000000000000 (by decide +kernel)
private def pv373 := integerPair bk1 bk830 16058086501389114823556254101635063926551 90621040640000000000000000000000000000000 (by decide +kernel)
private def pv374 := integerPair bk833 bk819 246046522454585949160552579237806478805454961 876083812104200000000000000000000000000000000 (by decide +kernel)
private def pv375 := integerPair bk833 bk821 146451722788938217159877046703409387642539 596044609400000000000000000000000000000000 (by decide +kernel)
private def pv376 := integerPair bk833 bk820 10076177319150580062009926896691376191466211341 49499965883033600000000000000000000000000000000 (by decide +kernel)
private def pv377 := integerPair bk833 bk827 4960946032549240943612966121487339982116259 25030966060120000000000000000000000000000000 (by decide +kernel)
private def pv378 := integerPair bk1 bk834 595563139530362530396050746034117556682451 3498501593600000000000000000000000000000000 (by decide +kernel)
private def pv379 := integerPair bk838 bk395 156335464044831458201464295196746894449237 61596620800000000000000000000000000000000 (by decide +kernel)
private def pv380 := integerPair bk842 bk395 136063866930863307331465567929295009567829521 62859351526400000000000000000000000000000000 (by decide +kernel)
private def pv381 := integerPair bk845 bk395 29260404932969339334027666536483300112692931 12906040576000000000000000000000000000000000 (by decide +kernel)
private def pv382 := integerPair bk847 bk395 16091952740114405186029157479105816859740599 6832672000000000000000000000000000000000000 (by decide +kernel)
private def pv383 := integerPair bk851 bk395 10079658073706342338033182327609349878140461 1952192000000000000000000000000000000000000 (by decide +kernel)
private def pv384 := integerPair bk852 bk395 612397676236577873714511179689438531216041 171395840000000000000000000000000000000000 (by decide +kernel)
private def pv385 := integerPair bk1 bk857 2850918744270165888873505968584578065343950821 10270877320704000000000000000000000000000000000 (by decide +kernel)
private def pv386 := integerPair bk1 bk859 161453043380583285590127483283673798987233 666352128000000000000000000000000000000000 (by decide +kernel)
private def pv387 := integerPair bk1 bk858 45413789208196064060592286819603750595121 216671952640000000000000000000000000000000 (by decide +kernel)
private def pv388 := integerPair bk1 bk862 341298841697945759156297096650606828769613 1733375621120000000000000000000000000000000 (by decide +kernel)
private def pv389 := integerPair bk1 bk864 515945608775693515747998628639969738778509 2707444625600000000000000000000000000000000 (by decide +kernel)
private def pv390 := integerPair bk1 bk872 303755060593127349599978309324275947503765123 1467268188672000000000000000000000000000000000 (by decide +kernel)
private def pv391 := integerPair bk876 bk395 257192279820867550343869991221271090128746953 115852834240000000000000000000000000000000000 (by decide +kernel)
private def pv392 := integerPair bk194 bk395 429476768340740643305682193004962918019972901 191919333760000000000000000000000000000000000 (by decide +kernel)
private def pv393 := integerPair bk196 bk395 270617282135612042087906335411722131414482293 54834095360000000000000000000000000000000000 (by decide +kernel)
private def pv394 := integerPair bk195 bk395 787956620854860795018439465357010954878881 254653520000000000000000000000000000000000 (by decide +kernel)
private def pv395 := integerPair bk880 bk395 127259876453140788707231716904546782237727571 67428711680000000000000000000000000000000000 (by decide +kernel)
private def pv396 := integerPair bk885 bk395 27789457890572857605638631702187388831341932661 13933757826560000000000000000000000000000000000 (by decide +kernel)
private def pv397 := integerPair bk1 bk889 2092075878379536629746272456344792942170341937 6557565926912000000000000000000000000000000000 (by decide +kernel)
private def pv398 := integerPair bk1 bk891 13141305075972168751594207864511166073239253 43260625408000000000000000000000000000000000 (by decide +kernel)
private def pv399 := integerPair bk1 bk890 4393774324083128655736903069167350784213239 15298114923520000000000000000000000000000000 (by decide +kernel)
private def pv400 := integerPair bk1 bk894 8609329871732002386354836806948093116008893 30596229847040000000000000000000000000000000 (by decide +kernel)
private def pv401 := integerPair bk1 bk896 29845677279376683890550726707911661603336649 107243395916800000000000000000000000000000000 (by decide +kernel)
private def pv402 := integerPair bk1 bk904 1883896576567363685953863035248689456659137057 6557565926912000000000000000000000000000000000 (by decide +kernel)
private def pv403 := integerPair bk908 bk395 31608635453120943745786791572718367782076077 44650048368640000000000000000000000000000000 (by decide +kernel)
private def pv404 := integerPair bk912 bk395 186430574658580946722630488322486729189035099 298030498304000000000000000000000000000000000 (by decide +kernel)
private def pv405 := integerPair bk914 bk395 3439010919522097128317299729176620942027181 1935262976000000000000000000000000000000000 (by decide +kernel)
private def pv406 := integerPair bk915 bk395 1933100777588220414840849052275367451822691 1743857920000000000000000000000000000000000 (by decide +kernel)
private def pv407 := integerPair bk918 bk395 299376625325019497401404746860319095824762579 539235199528960000000000000000000000000000000 (by decide +kernel)
private def pv408 := integerPair bk923 bk395 330861799339718647475216275624259873758494541 554610467840000000000000000000000000000000000 (by decide +kernel)
private def pv409 := integerPair bk1 bk927 74508795983455862209147730766055864114183761 257188991488000000000000000000000000000000000 (by decide +kernel)
private def pv410 := integerPair bk1 bk929 1014110597902955238759854705118460935380087 3762497024000000000000000000000000000000000 (by decide +kernel)
private def pv411 := integerPair bk1 bk930 1847577726470335041784982557305835264005563 7329873408000000000000000000000000000000000 (by decide +kernel)
private def pv412 := integerPair bk1 bk928 48175906432351541067664864492787305206441 216671952640000000000000000000000000000000 (by decide +kernel)
private def pv413 := integerPair bk1 bk937 59313997574183039289286117075931861653484961 257188991488000000000000000000000000000000000 (by decide +kernel)
private def pv414 := integerPair bk1 bk943 364586252181479221022849591083526434439733 1733375621120000000000000000000000000000000 (by decide +kernel)
private def pv415 := integerPair bk1 bk948 1081270522222330412523060430679090167854133 5336352220160000000000000000000000000000000 (by decide +kernel)
private def pv416 := integerPair bk952 bk395 228188628831648206212853513761876569055388203 115852834240000000000000000000000000000000000 (by decide +kernel)
private def pv417 := integerPair bk242 bk395 21098986621653552550256450023568764441567047 9361918720000000000000000000000000000000000 (by decide +kernel)
private def pv418 := integerPair bk244 bk395 272326658281380065113668353599512663551990043 54834095360000000000000000000000000000000000 (by decide +kernel)
private def pv419 := integerPair bk960 bk395 6816115882296246027203387097021235202027673 2037228160000000000000000000000000000000000 (by decide +kernel)
private def pv420 := integerPair bk962 bk395 4580362445772174548874596832693945076628870509 2798291534720000000000000000000000000000000000 (by decide +kernel)
private def pv421 := integerPair bk968 bk395 24583015292976510126677680256874939985443196661 13933757826560000000000000000000000000000000000 (by decide +kernel)
private def pv422 := integerPair bk972 bk395 717612602850384708856753643788209216580881 254653520000000000000000000000000000000000 (by decide +kernel)
private def pv423 := integerPair bk1 bk973 417699813379580877547133921391568540839242577 1800322940416000000000000000000000000000000000 (by decide +kernel)
private def pv424 := integerPair bk1 bk975 752173742165581208458887714691772696088531 3762497024000000000000000000000000000000000 (by decide +kernel)
private def pv425 := integerPair bk1 bk976 1230080323152885835758467260513796486913769 7329873408000000000000000000000000000000000 (by decide +kernel)
private def pv426 := integerPair bk984 bk976 200141366141165429223574447906881793191 901222360000000000000000000000000000000 (by decide +kernel)
private def pv427 := integerPair bk1 bk974 77457347058647552154145862599307966106879 866687810560000000000000000000000000000000 (by decide +kernel)
private def pv428 := integerPair bk1 bk983 30232705192892195072554062764101559424672711 257188991488000000000000000000000000000000000 (by decide +kernel)
private def pv429 := integerPair bk984 bk974 163982381977936989487367203077956449151573777 1170295217428480000000000000000000000000000000 (by decide +kernel)
private def pv430 := integerPair bk986 bk395 20412213288531330526642052464814186634865123 4929907840000000000000000000000000000000000 (by decide +kernel)
private def pv431 := integerPair bk994 bk395 1767361143385622908543631597613934712085901251 383838667520000000000000000000000000000000000 (by decide +kernel)
private def pv432 := integerPair bk996 bk395 524971412012771696228941154660844452513794293 54834095360000000000000000000000000000000000 (by decide +kernel)
private def pv433 := integerPair bk997 bk395 834880439212830150763785310349488091019687 127326760000000000000000000000000000000000 (by decide +kernel)
private def pv434 := integerPair bk1000 bk395 19758502654998452886840972014375908381583364143 5596583069440000000000000000000000000000000000 (by decide +kernel)
private def pv435 := integerPair bk1006 bk395 1114615599126125628654501942324401443399557163 296462932480000000000000000000000000000000000 (by decide +kernel)
private def pv436 := integerPair bk1010 bk395 506137873136073015097067133640226625362247 86690560000000000000000000000000000000000 (by decide +kernel)
private def pv437 := integerPair bk1 bk1011 1958769555805063336196853736402241629039718783 6056598157209600000000000000000000000000000000 (by decide +kernel)
private def pv438 := integerPair bk1 bk1013 17802698598345041515458939268827132473229851 56774395392000000000000000000000000000000000 (by decide +kernel)
private def pv439 := integerPair bk1 bk1014 13329058042115822807048340231646037922885253 43260625408000000000000000000000000000000000 (by decide +kernel)
private def pv440 := integerPair bk1 bk1012 407566336813321336286623218683856687624709 1390737720320000000000000000000000000000000 (by decide +kernel)
private def pv441 := integerPair bk1 bk1021 255923923277755363500051001722425341881072089 865228308172800000000000000000000000000000000 (by decide +kernel)
private def pv442 := integerPair bk1 bk1027 799807222917852905104542657262411827595103 2781475440640000000000000000000000000000000 (by decide +kernel)
private def pv443 := integerPair bk1 bk1032 52606818288682585187172450136105440889601187 185105821139200000000000000000000000000000000 (by decide +kernel)
private def pv444 := integerPair bk1036 bk1037 19912496072990579763399848373402978219655005787 29079423546700800000000000000000000000000000000 (by decide +kernel)
private def pv445 := integerPair bk1044 bk1037 2928962864256221820181913673762755528017389 4043740995560000000000000000000000000000000 (by decide +kernel)
private def pv446 := integerPair bk1046 bk1037 27289102256952041612562918342006051183318363 14441932127000000000000000000000000000000000 (by decide +kernel)
private def pv447 := integerPair bk1047 bk1037 19627285452426642711659066429538466269667 14872649960000000000000000000000000000000 (by decide +kernel)
private def pv448 := integerPair bk1050 bk395 237364589372057191733400944384049351510718077 539235199528960000000000000000000000000000000 (by decide +kernel)
private def pv449 := integerPair bk1044 bk395 59962660422897337139399793711903963870579789 94827885824000000000000000000000000000000000 (by decide +kernel)
private def pv450 := integerPair bk1046 bk395 3464764568056051291968903444457480987686381 1935262976000000000000000000000000000000000 (by decide +kernel)
private def pv451 := integerPair bk1047 bk395 46956928049147009690917064959845504004067763 38364874240000000000000000000000000000000000 (by decide +kernel)
private def pv452 := integerPair bk1036 bk395 26476611198957563261056652841635773591887837 44650048368640000000000000000000000000000000 (by decide +kernel)
private def pv453 := integerPair bk1056 bk395 272653250980689899682091530489977679740470541 554610467840000000000000000000000000000000000 (by decide +kernel)
private def pv454 := integerPair bk1060 bk395 37664906020679941949374643462074533752177763 38364874240000000000000000000000000000000000 (by decide +kernel)
private def pv455 := integerPair bk1 bk1061 33434221794153393200794345966191123460263828629 99487665525248000000000000000000000000000000000 (by decide +kernel)
private def pv456 := integerPair bk1 bk1063 2228675345310449741361609489967814747870711 6748282112000000000000000000000000000000000 (by decide +kernel)
private def pv457 := integerPair bk1 bk1064 15687384108968784535100792684455437047803481 47844532736000000000000000000000000000000000 (by decide +kernel)
private def pv458 := integerPair bk1 bk1062 1363618044347011707112477427882361734249571 4276325381120000000000000000000000000000000 (by decide +kernel)
private def pv459 := integerPair bk1 bk1071 4549704023138956997232947424951249987139714547 14212523646464000000000000000000000000000000000 (by decide +kernel)
private def pv460 := integerPair bk1 bk1077 2700300475131832326038877837756129935113527 8552650762240000000000000000000000000000000 (by decide +kernel)
private def pv461 := integerPair bk1 bk1082 8985414743952749038637492769276861975275477 28628173849600000000000000000000000000000000 (by decide +kernel)
private def pv462 := integerPair bk1086 bk1087 72173361781397719765315170261070410366655301 325269184101888000000000000000000000000000000 (by decide +kernel)
private def pv463 := integerPair bk1086 bk395 130817428138232414072345743250743328481226953 4042905477325000000000000000000000000000000000 (by decide +kernel)
private def pv464 := integerPair bk1092 bk395 5845318507303683969495217515276499017450081 64709663920000000000000000000000000000000000 (by decide +kernel)
private def pv465 := integerPair bk1094 bk395 11791874036047954277470032291802458756818589 16177415980000000000000000000000000000000000 (by decide +kernel)
private def pv466 := integerPair bk1095 bk395 14245605677076950922490590409983431195109 31360806400000000000000000000000000000000 (by decide +kernel)
private def pv467 := integerPair bk1098 bk1087 24962784402735059968997785653175692109 49279534080000000000000000000000000000 (by decide +kernel)
private def pv468 := integerPair bk1098 bk395 39591485318482398870966997035179453397711 125443225600000000000000000000000000000000 (by decide +kernel)
private def pv469 := integerPair bk1 bk258 1795402657870742674583755794252354411987698783 6056598157209600000000000000000000000000000000 (by decide +kernel)
private def pv470 := integerPair bk1 bk260 15934874834667165164636416104409758031137313 56774395392000000000000000000000000000000000 (by decide +kernel)
private def pv471 := integerPair bk1 bk261 11709696567996749286281434015282416095010089 43260625408000000000000000000000000000000000 (by decide +kernel)
private def pv472 := integerPair bk1 bk259 443765382413337207942100103155742586353113 1912264365440000000000000000000000000000000 (by decide +kernel)
private def pv473 := integerPair bk1 bk268 210181191856145578248383577920456921106506489 865228308172800000000000000000000000000000000 (by decide +kernel)
private def pv474 := integerPair bk272 bk395 1510165117605019561688721773865896490453171 950001029120000000000000000000000000000000 (by decide +kernel)
private def pv475 := integerPair bk280 bk395 22160285686581653537785021313192360626312827 13546840832000000000000000000000000000000000 (by decide +kernel)
private def pv476 := integerPair bk282 bk395 7271138143383020796972717663675183408230781 1935262976000000000000000000000000000000000 (by decide +kernel)
private def pv477 := integerPair bk283 bk395 103492724728374349564157099373994178428217763 38364874240000000000000000000000000000000000 (by decide +kernel)
private def pv478 := integerPair bk286 bk395 706168090545890810083954263527665821449820507 539235199528960000000000000000000000000000000 (by decide +kernel)
private def pv479 := integerPair bk292 bk395 777395078850591294441863889574994721436630541 554610467840000000000000000000000000000000000 (by decide +kernel)
private def pv480 := integerPair bk296 bk395 90842140520943281434105368901125267121427763 38364874240000000000000000000000000000000000 (by decide +kernel)
private def pv481 := integerPair bk1 bk298 31885240155782724303875578594117036180399072379 99487665525248000000000000000000000000000000000 (by decide +kernel)
private def pv482 := integerPair bk1 bk300 4199613568431339456827965001059989717073541 13496564224000000000000000000000000000000000 (by decide +kernel)
private def pv483 := integerPair bk1 bk301 14680060384555002014632974849867490965859803 47844532736000000000000000000000000000000000 (by decide +kernel)
private def pv484 := integerPair bk1 bk299 6679897258425299785102941442044164682487743 23519789596160000000000000000000000000000000 (by decide +kernel)
private def pv485 := integerPair bk1 bk308 4115989164395169706095692560770505548777582797 14212523646464000000000000000000000000000000000 (by decide +kernel)
private def pv486 := integerPair bk312 bk395 4863676157415940837985865183160016460288918537 8808372784640000000000000000000000000000000000 (by decide +kernel)
private def pv487 := integerPair bk318 bk395 2332629631050991248527472237186611070561426411 3623741179520000000000000000000000000000000000 (by decide +kernel)
private def pv488 := integerPair bk320 bk395 938821671653290321825048249110394275381776973 517677311360000000000000000000000000000000000 (by decide +kernel)
private def pv489 := integerPair bk321 bk395 162794752610257555901922110138739357682033 125443225600000000000000000000000000000000 (by decide +kernel)
private def pv490 := integerPair bk324 bk395 139117934236157908377265770375640377103483 125443225600000000000000000000000000000000 (by decide +kernel)
private def pv491 := integerPair bk601 bk584 13699922382521948686845988391030232670211 57086257340000000000000000000000000000000 (by decide +kernel)
private def pv492 := integerPair bk1104 bk584 1140715209647699544597284478497289529572531 4380419060521000000000000000000000000000000 (by decide +kernel)
private def pv493 := integerPair bk1106 bk584 1884864015714420463514381924217033070352367 2737761912825625000000000000000000000000000 (by decide +kernel)
private def pv494 := integerPair bk1107 bk584 1451839934852194124899410650518731403724661 2920618586060000000000000000000000000000000 (by decide +kernel)
private def pv495 := integerPair bk601 bk585 1301108015516115648749308268454855009 7111168000000000000000000000000000000 (by decide +kernel)
private def pv496 := integerPair bk1104 bk585 1964023097673433377994380482978271207627 9661017647750000000000000000000000000000 (by decide +kernel)
private def pv497 := integerPair bk1106 bk585 17424984296148246003614328783242796975219 27602907565000000000000000000000000000000 (by decide +kernel)
private def pv498 := integerPair bk1107 bk585 46265464873833060821474520286999438269 105166148000000000000000000000000000000 (by decide +kernel)
private def pv499 := integerPair bk601 bk1100 353515510591746380604960705625581748978963 2344527383520000000000000000000000000000000 (by decide +kernel)
private def pv500 := integerPair bk601 bk1099 1127875204348920018615790929798441461789989141 20281973527692800000000000000000000000000000000 (by decide +kernel)
private def pv501 := integerPair bk1104 bk1105 3087289621647934456312264928749409990496661071 76864922992143104000000000000000000000000000000 (by decide +kernel)
private def pv502 := integerPair bk1106 bk1099 9364291909001798072300746413776565276094821543 18582728635463168000000000000000000000000000000 (by decide +kernel)
private def pv503 := integerPair bk1107 bk1108 11284454465521721444016586713556175353288611851 43900873816819712000000000000000000000000000000 (by decide +kernel)
private def pv504 := integerPair bk601 bk591 121424728708357036103607134000096588821757 1951417980500000000000000000000000000000000 (by decide +kernel)
private def pv505 := integerPair bk1104 bk591 644168920382353411401698174294150169590901 7822176893787500000000000000000000000000000 (by decide +kernel)
private def pv506 := integerPair bk1106 bk591 7985006467533896812180991349481026707007717 15644353787575000000000000000000000000000000 (by decide +kernel)
private def pv507 := integerPair bk1107 bk591 95070024508598663288570551956087749296869 298022304700000000000000000000000000000000 (by decide +kernel)
private def pv508 := integerPair bk564 bk1100 118117747607359289791036143724176126531 316735692800000000000000000000000000000 (by decide +kernel)
private def pv509 := integerPair bk564 bk1099 453753755417774744081767044455631991662731 1634664156160000000000000000000000000000000 (by decide +kernel)
private def pv510 := integerPair bk564 bk1105 10287658456026405477462050685023601872213487 42501268060160000000000000000000000000000000 (by decide +kernel)
private def pv511 := integerPair bk1116 bk395 5188434204002848266331464715258276144949151 800756070400000000000000000000000000000000 (by decide +kernel)
private def pv512 := integerPair bk1121 bk395 87420341307921913748143530572612511616443779 15714837881600000000000000000000000000000000 (by decide +kernel)
private def pv513 := integerPair bk1125 bk395 94618480336922803125399213678460682805800331 16132550720000000000000000000000000000000000 (by decide +kernel)
private def pv514 := integerPair bk1127 bk395 612835156260112340476088676673113080280463 68558336000000000000000000000000000000000 (by decide +kernel)
private def pv515 := integerPair bk1131 bk395 812856456010018123390306170116855943206559 122425600000000000000000000000000000000000 (by decide +kernel)
private def pv516 := integerPair bk1135 bk395 1660185243528727371086870607250177404411759 122425600000000000000000000000000000000000 (by decide +kernel)
private def pv517 := integerPair bk1136 bk395 69716467639718006518248713831669871439419 6855833600000000000000000000000000000000 (by decide +kernel)
private def pv518 := integerPair bk1 bk1141 3915642890516452449172384681903509871588301097 14548600959692800000000000000000000000000000000 (by decide +kernel)
private def pv519 := integerPair bk1 bk1143 2170005026161265514842067608711062185262351 9135034388480000000000000000000000000000000 (by decide +kernel)
private def pv520 := integerPair bk1 bk1142 8118117269183597604709999316113431047814981 39449971658240000000000000000000000000000000 (by decide +kernel)
private def pv521 := integerPair bk1 bk1146 7575928429196778352273628320730461505557131 39449971658240000000000000000000000000000000 (by decide +kernel)
private def pv522 := integerPair bk1 bk1148 182216264959964186581170180991394687720099729 976055356390400000000000000000000000000000000 (by decide +kernel)
private def pv523 := integerPair bk1 bk1144 4050440652325898636927876734490720854512008033 20897896257638400000000000000000000000000000000 (by decide +kernel)
private def pv524 := integerPair bk1 bk1157 400389260882229950607865309293560246949530271 2078371565670400000000000000000000000000000000 (by decide +kernel)
private def pv525 := integerPair bk1160 bk559 354661093719599983582849767371852427069240849 148339071670400000000000000000000000000000000 (by decide +kernel)
private def pv526 := integerPair bk1122 bk559 343024531217261239351204208969100323584928011 135333830374400000000000000000000000000000000 (by decide +kernel)
private def pv527 := integerPair bk1124 bk559 2598249813177379859701164214302779577772959877 483335108480000000000000000000000000000000000 (by decide +kernel)
private def pv528 := integerPair bk1123 bk559 6126364833111248678856447097354853797021041 1814707328000000000000000000000000000000000 (by decide +kernel)
private def pv529 := integerPair bk1164 bk559 1234052870932622433275737268684065128776721302537 601937131442841600000000000000000000000000000000 (by decide +kernel)
private def pv530 := integerPair bk1169 bk559 52180474730786211722796160942269282444784297801 24052370121343200000000000000000000000000000000 (by decide +kernel)
private def pv531 := integerPair bk1 bk1174 426036725173348024397681791759918564343755603641 25071018315200000000000000000000000000000000000000 (by decide +kernel)
private def pv532 := integerPair bk1 bk164 971637943791926379756913911136286279234437 8354018816000000000000000000000000000000000 (by decide +kernel)
private def pv533 := integerPair bk1 bk183 1976981791651572096738568067426014986606169 115335334400000000000000000000000000000000000 (by decide +kernel)

end Terminal3Pairs17
set_option maxRecDepth 262144
set_option maxHeartbeats 0
private def terminal3ValidPairs := [Terminal3Pairs17.pv001,
  Terminal3Pairs17.pv002,
  Terminal3Pairs17.pv003,
  Terminal3Pairs17.pv004,
  Terminal3Pairs17.pv005,
  Terminal3Pairs17.pv006,
  Terminal3Pairs17.pv007,
  Terminal3Pairs17.pv008,
  Terminal3Pairs17.pv009,
  Terminal3Pairs17.pv010,
  Terminal3Pairs17.pv011,
  Terminal3Pairs17.pv012,
  Terminal3Pairs17.pv013,
  Terminal3Pairs17.pv014,
  Terminal3Pairs17.pv015,
  Terminal3Pairs17.pv016,
  Terminal3Pairs17.pv017,
  Terminal3Pairs17.pv018,
  Terminal3Pairs17.pv019,
  Terminal3Pairs17.pv020,
  Terminal3Pairs17.pv021,
  Terminal3Pairs17.pv022,
  Terminal3Pairs17.pv023,
  Terminal3Pairs17.pv024,
  Terminal3Pairs17.pv025,
  Terminal3Pairs17.pv026,
  Terminal3Pairs17.pv027,
  Terminal3Pairs17.pv028,
  Terminal3Pairs17.pv029,
  Terminal3Pairs17.pv030,
  Terminal3Pairs17.pv031,
  Terminal3Pairs17.pv032,
  Terminal3Pairs17.pv033,
  Terminal3Pairs17.pv034,
  Terminal3Pairs17.pv035,
  Terminal3Pairs17.pv036,
  Terminal3Pairs17.pv037,
  Terminal3Pairs17.pv038,
  Terminal3Pairs17.pv039,
  Terminal3Pairs17.pv040,
  Terminal3Pairs17.pv041,
  Terminal3Pairs17.pv042,
  Terminal3Pairs17.pv043,
  Terminal3Pairs17.pv044,
  Terminal3Pairs17.pv045,
  Terminal3Pairs17.pv046,
  Terminal3Pairs17.pv047,
  Terminal3Pairs17.pv048,
  Terminal3Pairs17.pv049,
  Terminal3Pairs17.pv050,
  Terminal3Pairs17.pv051,
  Terminal3Pairs17.pv052,
  Terminal3Pairs17.pv053,
  Terminal3Pairs17.pv054,
  Terminal3Pairs17.pv055,
  Terminal3Pairs17.pv056,
  Terminal3Pairs17.pv057,
  Terminal3Pairs17.pv058,
  Terminal3Pairs17.pv059,
  Terminal3Pairs17.pv060,
  Terminal3Pairs17.pv061,
  Terminal3Pairs17.pv062,
  Terminal3Pairs17.pv063,
  Terminal3Pairs17.pv064,
  Terminal3Pairs17.pv065,
  Terminal3Pairs17.pv066,
  Terminal3Pairs17.pv067,
  Terminal3Pairs17.pv068,
  Terminal3Pairs17.pv069,
  Terminal3Pairs17.pv070,
  Terminal3Pairs17.pv071,
  Terminal3Pairs17.pv072,
  Terminal3Pairs17.pv073,
  Terminal3Pairs17.pv074,
  Terminal3Pairs17.pv075,
  Terminal3Pairs17.pv076,
  Terminal3Pairs17.pv077,
  Terminal3Pairs17.pv078,
  Terminal3Pairs17.pv079,
  Terminal3Pairs17.pv080,
  Terminal3Pairs17.pv081,
  Terminal3Pairs17.pv082,
  Terminal3Pairs17.pv083,
  Terminal3Pairs17.pv084,
  Terminal3Pairs17.pv085,
  Terminal3Pairs17.pv086,
  Terminal3Pairs17.pv087,
  Terminal3Pairs17.pv088,
  Terminal3Pairs17.pv089,
  Terminal3Pairs17.pv090,
  Terminal3Pairs17.pv091,
  Terminal3Pairs17.pv092,
  Terminal3Pairs17.pv093,
  Terminal3Pairs17.pv094,
  Terminal3Pairs17.pv095,
  Terminal3Pairs17.pv096,
  Terminal3Pairs17.pv097,
  Terminal3Pairs17.pv098,
  Terminal3Pairs17.pv099,
  Terminal3Pairs17.pv100,
  Terminal3Pairs17.pv101,
  Terminal3Pairs17.pv102,
  Terminal3Pairs17.pv103,
  Terminal3Pairs17.pv104,
  Terminal3Pairs17.pv105,
  Terminal3Pairs17.pv106,
  Terminal3Pairs17.pv107,
  Terminal3Pairs17.pv108,
  Terminal3Pairs17.pv109,
  Terminal3Pairs17.pv110,
  Terminal3Pairs17.pv111,
  Terminal3Pairs17.pv112,
  Terminal3Pairs17.pv113,
  Terminal3Pairs17.pv114,
  Terminal3Pairs17.pv115,
  Terminal3Pairs17.pv116,
  Terminal3Pairs17.pv117,
  Terminal3Pairs17.pv118,
  Terminal3Pairs17.pv119,
  Terminal3Pairs17.pv120,
  Terminal3Pairs17.pv121,
  Terminal3Pairs17.pv122,
  Terminal3Pairs17.pv123,
  Terminal3Pairs17.pv124,
  Terminal3Pairs17.pv125,
  Terminal3Pairs17.pv126,
  Terminal3Pairs17.pv127,
  Terminal3Pairs17.pv128,
  Terminal3Pairs17.pv129,
  Terminal3Pairs17.pv130,
  Terminal3Pairs17.pv131,
  Terminal3Pairs17.pv132,
  Terminal3Pairs17.pv133,
  Terminal3Pairs17.pv134,
  Terminal3Pairs17.pv135,
  Terminal3Pairs17.pv136,
  Terminal3Pairs17.pv137,
  Terminal3Pairs17.pv138,
  Terminal3Pairs17.pv139,
  Terminal3Pairs17.pv140,
  Terminal3Pairs17.pv141,
  Terminal3Pairs17.pv142,
  Terminal3Pairs17.pv143,
  Terminal3Pairs17.pv144,
  Terminal3Pairs17.pv145,
  Terminal3Pairs17.pv146,
  Terminal3Pairs17.pv147,
  Terminal3Pairs17.pv148,
  Terminal3Pairs17.pv149,
  Terminal3Pairs17.pv150,
  Terminal3Pairs17.pv151,
  Terminal3Pairs17.pv152,
  Terminal3Pairs17.pv153,
  Terminal3Pairs17.pv154,
  Terminal3Pairs17.pv155,
  Terminal3Pairs17.pv156,
  Terminal3Pairs17.pv157,
  Terminal3Pairs17.pv158,
  Terminal3Pairs17.pv159,
  Terminal3Pairs17.pv160,
  Terminal3Pairs17.pv161,
  Terminal3Pairs17.pv162,
  Terminal3Pairs17.pv163,
  Terminal3Pairs17.pv164,
  Terminal3Pairs17.pv165,
  Terminal3Pairs17.pv166,
  Terminal3Pairs17.pv167,
  Terminal3Pairs17.pv168,
  Terminal3Pairs17.pv169,
  Terminal3Pairs17.pv170,
  Terminal3Pairs17.pv171,
  Terminal3Pairs17.pv172,
  Terminal3Pairs17.pv173,
  Terminal3Pairs17.pv174,
  Terminal3Pairs17.pv175,
  Terminal3Pairs17.pv176,
  Terminal3Pairs17.pv177,
  Terminal3Pairs17.pv178,
  Terminal3Pairs17.pv179,
  Terminal3Pairs17.pv180,
  Terminal3Pairs17.pv181,
  Terminal3Pairs17.pv182,
  Terminal3Pairs17.pv183,
  Terminal3Pairs17.pv184,
  Terminal3Pairs17.pv185,
  Terminal3Pairs17.pv186,
  Terminal3Pairs17.pv187,
  Terminal3Pairs17.pv188,
  Terminal3Pairs17.pv189,
  Terminal3Pairs17.pv190,
  Terminal3Pairs17.pv191,
  Terminal3Pairs17.pv192,
  Terminal3Pairs17.pv193,
  Terminal3Pairs17.pv194,
  Terminal3Pairs17.pv195,
  Terminal3Pairs17.pv196,
  Terminal3Pairs17.pv197,
  Terminal3Pairs17.pv198,
  Terminal3Pairs17.pv199,
  Terminal3Pairs17.pv200,
  Terminal3Pairs17.pv201,
  Terminal3Pairs17.pv202,
  Terminal3Pairs17.pv203,
  Terminal3Pairs17.pv204,
  Terminal3Pairs17.pv205,
  Terminal3Pairs17.pv206,
  Terminal3Pairs17.pv207,
  Terminal3Pairs17.pv208,
  Terminal3Pairs17.pv209,
  Terminal3Pairs17.pv210,
  Terminal3Pairs17.pv211,
  Terminal3Pairs17.pv212,
  Terminal3Pairs17.pv213,
  Terminal3Pairs17.pv214,
  Terminal3Pairs17.pv215,
  Terminal3Pairs17.pv216,
  Terminal3Pairs17.pv217,
  Terminal3Pairs17.pv218,
  Terminal3Pairs17.pv219,
  Terminal3Pairs17.pv220,
  Terminal3Pairs17.pv221,
  Terminal3Pairs17.pv222,
  Terminal3Pairs17.pv223,
  Terminal3Pairs17.pv224,
  Terminal3Pairs17.pv225,
  Terminal3Pairs17.pv226,
  Terminal3Pairs17.pv227,
  Terminal3Pairs17.pv228,
  Terminal3Pairs17.pv229,
  Terminal3Pairs17.pv230,
  Terminal3Pairs17.pv231,
  Terminal3Pairs17.pv232,
  Terminal3Pairs17.pv233,
  Terminal3Pairs17.pv234,
  Terminal3Pairs17.pv235,
  Terminal3Pairs17.pv236,
  Terminal3Pairs17.pv237,
  Terminal3Pairs17.pv238,
  Terminal3Pairs17.pv239,
  Terminal3Pairs17.pv240,
  Terminal3Pairs17.pv241,
  Terminal3Pairs17.pv242,
  Terminal3Pairs17.pv243,
  Terminal3Pairs17.pv244,
  Terminal3Pairs17.pv245,
  Terminal3Pairs17.pv246,
  Terminal3Pairs17.pv247,
  Terminal3Pairs17.pv248,
  Terminal3Pairs17.pv249,
  Terminal3Pairs17.pv250,
  Terminal3Pairs17.pv251,
  Terminal3Pairs17.pv252,
  Terminal3Pairs17.pv253,
  Terminal3Pairs17.pv254,
  Terminal3Pairs17.pv255,
  Terminal3Pairs17.pv256,
  Terminal3Pairs17.pv257,
  Terminal3Pairs17.pv258,
  Terminal3Pairs17.pv259,
  Terminal3Pairs17.pv260,
  Terminal3Pairs17.pv261,
  Terminal3Pairs17.pv262,
  Terminal3Pairs17.pv263,
  Terminal3Pairs17.pv264,
  Terminal3Pairs17.pv265,
  Terminal3Pairs17.pv266,
  Terminal3Pairs17.pv267,
  Terminal3Pairs17.pv268,
  Terminal3Pairs17.pv269,
  Terminal3Pairs17.pv270,
  Terminal3Pairs17.pv271,
  Terminal3Pairs17.pv272,
  Terminal3Pairs17.pv273,
  Terminal3Pairs17.pv274,
  Terminal3Pairs17.pv275,
  Terminal3Pairs17.pv276,
  Terminal3Pairs17.pv277,
  Terminal3Pairs17.pv278,
  Terminal3Pairs17.pv279,
  Terminal3Pairs17.pv280,
  Terminal3Pairs17.pv281,
  Terminal3Pairs17.pv282,
  Terminal3Pairs17.pv283,
  Terminal3Pairs17.pv284,
  Terminal3Pairs17.pv285,
  Terminal3Pairs17.pv286,
  Terminal3Pairs17.pv287,
  Terminal3Pairs17.pv288,
  Terminal3Pairs17.pv289,
  Terminal3Pairs17.pv290,
  Terminal3Pairs17.pv291,
  Terminal3Pairs17.pv292,
  Terminal3Pairs17.pv293,
  Terminal3Pairs17.pv294,
  Terminal3Pairs17.pv295,
  Terminal3Pairs17.pv296,
  Terminal3Pairs17.pv297,
  Terminal3Pairs17.pv298,
  Terminal3Pairs17.pv299,
  Terminal3Pairs17.pv300,
  Terminal3Pairs17.pv301,
  Terminal3Pairs17.pv302,
  Terminal3Pairs17.pv303,
  Terminal3Pairs17.pv304,
  Terminal3Pairs17.pv305,
  Terminal3Pairs17.pv306,
  Terminal3Pairs17.pv307,
  Terminal3Pairs17.pv308,
  Terminal3Pairs17.pv309,
  Terminal3Pairs17.pv310,
  Terminal3Pairs17.pv311,
  Terminal3Pairs17.pv312,
  Terminal3Pairs17.pv313,
  Terminal3Pairs17.pv314,
  Terminal3Pairs17.pv315,
  Terminal3Pairs17.pv316,
  Terminal3Pairs17.pv317,
  Terminal3Pairs17.pv318,
  Terminal3Pairs17.pv319,
  Terminal3Pairs17.pv320,
  Terminal3Pairs17.pv321,
  Terminal3Pairs17.pv322,
  Terminal3Pairs17.pv323,
  Terminal3Pairs17.pv324,
  Terminal3Pairs17.pv325,
  Terminal3Pairs17.pv326,
  Terminal3Pairs17.pv327,
  Terminal3Pairs17.pv328,
  Terminal3Pairs17.pv329,
  Terminal3Pairs17.pv330,
  Terminal3Pairs17.pv331,
  Terminal3Pairs17.pv332,
  Terminal3Pairs17.pv333,
  Terminal3Pairs17.pv334,
  Terminal3Pairs17.pv335,
  Terminal3Pairs17.pv336,
  Terminal3Pairs17.pv337,
  Terminal3Pairs17.pv338,
  Terminal3Pairs17.pv339,
  Terminal3Pairs17.pv340,
  Terminal3Pairs17.pv341,
  Terminal3Pairs17.pv342,
  Terminal3Pairs17.pv343,
  Terminal3Pairs17.pv344,
  Terminal3Pairs17.pv345,
  Terminal3Pairs17.pv346,
  Terminal3Pairs17.pv347,
  Terminal3Pairs17.pv348,
  Terminal3Pairs17.pv349,
  Terminal3Pairs17.pv350,
  Terminal3Pairs17.pv351,
  Terminal3Pairs17.pv352,
  Terminal3Pairs17.pv353,
  Terminal3Pairs17.pv354,
  Terminal3Pairs17.pv355,
  Terminal3Pairs17.pv356,
  Terminal3Pairs17.pv357,
  Terminal3Pairs17.pv358,
  Terminal3Pairs17.pv359,
  Terminal3Pairs17.pv360,
  Terminal3Pairs17.pv361,
  Terminal3Pairs17.pv362,
  Terminal3Pairs17.pv363,
  Terminal3Pairs17.pv364,
  Terminal3Pairs17.pv365,
  Terminal3Pairs17.pv366,
  Terminal3Pairs17.pv367,
  Terminal3Pairs17.pv368,
  Terminal3Pairs17.pv369,
  Terminal3Pairs17.pv370,
  Terminal3Pairs17.pv371,
  Terminal3Pairs17.pv372,
  Terminal3Pairs17.pv373,
  Terminal3Pairs17.pv374,
  Terminal3Pairs17.pv375,
  Terminal3Pairs17.pv376,
  Terminal3Pairs17.pv377,
  Terminal3Pairs17.pv378,
  Terminal3Pairs17.pv379,
  Terminal3Pairs17.pv380,
  Terminal3Pairs17.pv381,
  Terminal3Pairs17.pv382,
  Terminal3Pairs17.pv383,
  Terminal3Pairs17.pv384,
  Terminal3Pairs17.pv385,
  Terminal3Pairs17.pv386,
  Terminal3Pairs17.pv387,
  Terminal3Pairs17.pv388,
  Terminal3Pairs17.pv389,
  Terminal3Pairs17.pv390,
  Terminal3Pairs17.pv391,
  Terminal3Pairs17.pv392,
  Terminal3Pairs17.pv393,
  Terminal3Pairs17.pv394,
  Terminal3Pairs17.pv395,
  Terminal3Pairs17.pv396,
  Terminal3Pairs17.pv397,
  Terminal3Pairs17.pv398,
  Terminal3Pairs17.pv399,
  Terminal3Pairs17.pv400,
  Terminal3Pairs17.pv401,
  Terminal3Pairs17.pv402,
  Terminal3Pairs17.pv403,
  Terminal3Pairs17.pv404,
  Terminal3Pairs17.pv405,
  Terminal3Pairs17.pv406,
  Terminal3Pairs17.pv407,
  Terminal3Pairs17.pv408,
  Terminal3Pairs17.pv409,
  Terminal3Pairs17.pv410,
  Terminal3Pairs17.pv411,
  Terminal3Pairs17.pv412,
  Terminal3Pairs17.pv413,
  Terminal3Pairs17.pv414,
  Terminal3Pairs17.pv415,
  Terminal3Pairs17.pv416,
  Terminal3Pairs17.pv417,
  Terminal3Pairs17.pv418,
  Terminal3Pairs17.pv419,
  Terminal3Pairs17.pv420,
  Terminal3Pairs17.pv421,
  Terminal3Pairs17.pv422,
  Terminal3Pairs17.pv423,
  Terminal3Pairs17.pv424,
  Terminal3Pairs17.pv425,
  Terminal3Pairs17.pv426,
  Terminal3Pairs17.pv427,
  Terminal3Pairs17.pv428,
  Terminal3Pairs17.pv429,
  Terminal3Pairs17.pv430,
  Terminal3Pairs17.pv431,
  Terminal3Pairs17.pv432,
  Terminal3Pairs17.pv433,
  Terminal3Pairs17.pv434,
  Terminal3Pairs17.pv435,
  Terminal3Pairs17.pv436,
  Terminal3Pairs17.pv437,
  Terminal3Pairs17.pv438,
  Terminal3Pairs17.pv439,
  Terminal3Pairs17.pv440,
  Terminal3Pairs17.pv441,
  Terminal3Pairs17.pv442,
  Terminal3Pairs17.pv443,
  Terminal3Pairs17.pv444,
  Terminal3Pairs17.pv445,
  Terminal3Pairs17.pv446,
  Terminal3Pairs17.pv447,
  Terminal3Pairs17.pv448,
  Terminal3Pairs17.pv449,
  Terminal3Pairs17.pv450,
  Terminal3Pairs17.pv451,
  Terminal3Pairs17.pv452,
  Terminal3Pairs17.pv453,
  Terminal3Pairs17.pv454,
  Terminal3Pairs17.pv455,
  Terminal3Pairs17.pv456,
  Terminal3Pairs17.pv457,
  Terminal3Pairs17.pv458,
  Terminal3Pairs17.pv459,
  Terminal3Pairs17.pv460,
  Terminal3Pairs17.pv461,
  Terminal3Pairs17.pv462,
  Terminal3Pairs17.pv463,
  Terminal3Pairs17.pv464,
  Terminal3Pairs17.pv465,
  Terminal3Pairs17.pv466,
  Terminal3Pairs17.pv467,
  Terminal3Pairs17.pv468,
  Terminal3Pairs17.pv469,
  Terminal3Pairs17.pv470,
  Terminal3Pairs17.pv471,
  Terminal3Pairs17.pv472,
  Terminal3Pairs17.pv473,
  Terminal3Pairs17.pv474,
  Terminal3Pairs17.pv475,
  Terminal3Pairs17.pv476,
  Terminal3Pairs17.pv477,
  Terminal3Pairs17.pv478,
  Terminal3Pairs17.pv479,
  Terminal3Pairs17.pv480,
  Terminal3Pairs17.pv481,
  Terminal3Pairs17.pv482,
  Terminal3Pairs17.pv483,
  Terminal3Pairs17.pv484,
  Terminal3Pairs17.pv485,
  Terminal3Pairs17.pv486,
  Terminal3Pairs17.pv487,
  Terminal3Pairs17.pv488,
  Terminal3Pairs17.pv489,
  Terminal3Pairs17.pv490,
  Terminal3Pairs17.pv491,
  Terminal3Pairs17.pv492,
  Terminal3Pairs17.pv493,
  Terminal3Pairs17.pv494,
  Terminal3Pairs17.pv495,
  Terminal3Pairs17.pv496,
  Terminal3Pairs17.pv497,
  Terminal3Pairs17.pv498,
  Terminal3Pairs17.pv499,
  Terminal3Pairs17.pv500,
  Terminal3Pairs17.pv501,
  Terminal3Pairs17.pv502,
  Terminal3Pairs17.pv503,
  Terminal3Pairs17.pv504,
  Terminal3Pairs17.pv505,
  Terminal3Pairs17.pv506,
  Terminal3Pairs17.pv507,
  Terminal3Pairs17.pv508,
  Terminal3Pairs17.pv509,
  Terminal3Pairs17.pv510,
  Terminal3Pairs17.pv511,
  Terminal3Pairs17.pv512,
  Terminal3Pairs17.pv513,
  Terminal3Pairs17.pv514,
  Terminal3Pairs17.pv515,
  Terminal3Pairs17.pv516,
  Terminal3Pairs17.pv517,
  Terminal3Pairs17.pv518,
  Terminal3Pairs17.pv519,
  Terminal3Pairs17.pv520,
  Terminal3Pairs17.pv521,
  Terminal3Pairs17.pv522,
  Terminal3Pairs17.pv523,
  Terminal3Pairs17.pv524,
  Terminal3Pairs17.pv525,
  Terminal3Pairs17.pv526,
  Terminal3Pairs17.pv527,
  Terminal3Pairs17.pv528,
  Terminal3Pairs17.pv529,
  Terminal3Pairs17.pv530,
  Terminal3Pairs17.pv531,
  Terminal3Pairs17.pv532,
  Terminal3Pairs17.pv533]
theorem solution : ∀ p ∈ lowerEarlyTerminalTerminal3.pairs,
    lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p := by
  intro p hp
  have h : lowerEarlyTerminalTerminal3.pairs = terminal3ValidPairs.map Subtype.val := by rfl
  rw [h] at hp
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
  exact v.property
#print axioms solution
