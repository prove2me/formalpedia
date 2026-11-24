-- Prove2me | solution 1 for BB6Kit.zero_rank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T08:07:13.082421+00:00
-- url     : https://prove2.me/submissions/f13f08e0-3cba-486c-bb91-5ea6a319c1c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_zero_poly

open Finset

namespace ZR

noncomputable def coefP (c d : ℝ) (k k' : ℕ) : ℝ :=
  (Polynomial.C ((k.factorial : ℝ)⁻¹) *
    (descPochhammer ℝ k).comp (Polynomial.C c * Polynomial.X + Polynomial.C (c * d))).coeff k'

lemma coefP_natDegree (c d : ℝ) (hc : c ≠ 0) (k : ℕ) :
    (Polynomial.C ((k.factorial : ℝ)⁻¹) *
      (descPochhammer ℝ k).comp (Polynomial.C c * Polynomial.X + Polynomial.C (c * d))).natDegree ≤ k := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree, Polynomial.natDegree_linear hc, mul_one]

lemma coefP_diag (c d : ℝ) (hc : c ≠ 0) (k : ℕ) : coefP c d k k = c ^ k / (k.factorial : ℝ) := by
  unfold coefP
  rw [Polynomial.coeff_C_mul]
  have h := Polynomial.coeff_comp_degree_mul_degree (p := descPochhammer ℝ k)
    (q := Polynomial.C c * Polynomial.X + Polynomial.C (c * d)) (by rw [Polynomial.natDegree_linear hc]; norm_num)
  rw [descPochhammer_natDegree, Polynomial.natDegree_linear hc, mul_one, (monic_descPochhammer ℝ k).leadingCoeff,
    Polynomial.leadingCoeff_linear hc, one_mul] at h
  rw [h]
  field_simp

lemma coefP_eval (c d : ℝ) (hc : c ≠ 0) (k n : ℕ) (η : ℝ) (hn : (n : ℝ) = c * (η + d)) :
    ((n.choose k : ℕ) : ℝ) = ∑ k' ∈ range (k + 1), coefP c d k k' * η ^ k' := by
  unfold coefP
  rw [← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (coefP_natDegree c d hc k))]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  rw [show c * η + c * d = (n : ℝ) by rw [hn]; ring, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]


lemma coefP_zero (c d : ℝ) (hc : c ≠ 0) (k k' : ℕ) (h : k < k') : coefP c d k k' = 0 := by
  unfold coefP
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (coefP_natDegree c d hc k) h)

lemma mem_rowSet {K L : ℕ} (p : ℕ × ℕ × ℕ) :
    p ∈ BB6Kit.rowSet K L ↔ p.1 < K ∧ p.2.1 < K ∧ p.2.2 < L ∧ p.1 + p.2.1 ≤ K - 1 := by
  unfold BB6Kit.rowSet
  simp only [mem_filter, mem_product, mem_range]
  tauto

lemma slice (K L k m ℓ : ℕ) (hp : (k, m, ℓ) ∈ BB6Kit.rowSet K L) (A B : ℕ → ℝ)
    (hA : ∀ a, k < a → A a = 0) (hB : ∀ b, m < b → B b = 0) (x1 x2 y : ℝ) :
    ∑ q ∈ BB6Kit.rowSet K L, (if ℓ = q.2.2 then A q.1 * B q.2.1 else 0) * x1 ^ q.1 * x2 ^ q.2.1 * y ^ q.2.2 =
      (∑ a ∈ range (k + 1), A a * x1 ^ a) * (∑ b ∈ range (m + 1), B b * x2 ^ b) * y ^ ℓ := by
  have hp' := (mem_rowSet (k, m, ℓ)).mp hp
  have hk : k < K := hp'.1
  have hm : m < K := hp'.2.1
  have hl : ℓ < L := hp'.2.2.1
  have hkm : k + m ≤ K - 1 := hp'.2.2.2
  unfold BB6Kit.rowSet
  rw [sum_filter]
  simp only [sum_product]
  have hinner : ∀ a ∈ range K, ∀ b ∈ range K,
      ∑ e ∈ range L, (if a + b ≤ K - 1 then (if ℓ = e then A a * B b else 0) * x1 ^ a * x2 ^ b * y ^ e else 0) =
        A a * x1 ^ a * (B b * x2 ^ b) * y ^ ℓ := by
    intro a _ b _
    by_cases hab : a + b ≤ K - 1
    · simp only [if_pos hab, ite_mul, zero_mul]
      rw [sum_ite_eq]
      rw [if_pos (mem_range.mpr hl)]
      ring
    · simp only [if_neg hab, sum_const_zero]
      rcases Nat.lt_or_ge k a with h | h
      · rw [hA a h]; ring
      · rw [hB b (by omega)]; ring
  rw [sum_congr rfl (fun a ha => sum_congr rfl (fun b hb => hinner a ha b hb))]
  have eA : ∑ a ∈ range (k + 1), A a * x1 ^ a = ∑ a ∈ range K, A a * x1 ^ a := by
    apply sum_subset (by intro x hx; simp only [mem_range] at hx ⊢; omega)
    intro a _ ha
    rw [mem_range] at ha
    rw [hA a (by omega), zero_mul]
  have eB : ∑ b ∈ range (m + 1), B b * x2 ^ b = ∑ b ∈ range K, B b * x2 ^ b := by
    apply sum_subset (by intro x hx; simp only [mem_range] at hx ⊢; omega)
    intro b _ hb
    rw [mem_range] at hb
    rw [hB b (by omega), zero_mul]
  rw [eA, eB, sum_mul_sum, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [sum_mul]

end ZR

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 : ℕ) (χ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (hpos : 0 < R1 ∧ 0 < S1 ∧ 0 < T1 ∧ 0 < R2 ∧ 0 < S2 ∧ 0 < T2 ∧ 0 < R3 ∧ 0 < S3 ∧ 0 < T3)
    (h27 : R1 + R2 + R3 < R ∧ S1 + S2 + S3 < S ∧ T1 + T2 + T3 < T) (hχ : 0 < χ)
    (h29 : (K : ℝ) * (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) < (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))
    (h210 : L < ((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h211 : 2 * K * L < ((Finset.range (R2 + 1) ×ˢ Finset.range (S2 + 1) ×ˢ Finset.range (T2 + 1)).image (fun x => α1 ^ x.1 * α2 ^ x.2.1 * α3 ^ x.2.2)).card)
    (h212 : K ^ 2 < (R2 + 1) * (S2 + 1) * (T2 + 1))
    (h213 : 3 * K ^ 2 * L < (R3 + 1) * (S3 + 1) * (T3 + 1))
    (h214 : ¬ (b1 ≤ max R1 R2 ∧ b2 ≤ max S1 S2 ∧ b3 ≤ max T1 T2))
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (S1 : ℝ) T1) ∧
        (|u2| : ℝ) ≤ ((R1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) T1) ∧
        (|u3| : ℝ) ≤ ((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) S1))) :
    LinearIndependent ℝ (fun p : BB6Kit.rowSet K L => fun q : (Finset.range R ×ˢ Finset.range S ×ˢ Finset.range T) =>
      (Nat.choose ((q : ℕ × ℕ × ℕ).1 * (b3 / Nat.gcd b1 b3) + (q : ℕ × ℕ × ℕ).2.2 * (b1 / Nat.gcd b1 b3)) (p : ℕ × ℕ × ℕ).1 : ℝ) *
      (Nat.choose ((q : ℕ × ℕ × ℕ).2.1 * (b3 / Nat.gcd b2 b3) + (q : ℕ × ℕ × ℕ).2.2 * (b2 / Nat.gcd b2 b3)) (p : ℕ × ℕ × ℕ).2.1 : ℝ) *
      (α1 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (q : ℕ × ℕ × ℕ).1) * (α2 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (q : ℕ × ℕ × ℕ).2.1) *
      (α3 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (q : ℕ × ℕ × ℕ).2.2)) := by
  have hzp := BB6Kit.zero_poly K L R S T N b1 b2 b3 α1 α2 α3 R1 S1 T1 R2 S2 T2 R3 S3 T3 χ hK hL hN hRST
    hα1 hα2 hα3 hind hb1 hb2 hb3 hgcd hΛ hpos h27 hχ h29 h210 h211 h212 h213 h214 h215
  have hg13 : 0 < Nat.gcd b1 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hg23 : 0 < Nat.gcd b2 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hc2 : 0 < b3 / Nat.gcd b1 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg13
  have hc4 : 0 < b3 / Nat.gcd b2 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg23
  generalize b1 / Nat.gcd b1 b3 = c1 at hzp ⊢
  generalize b3 / Nat.gcd b1 b3 = c2 at hzp hc2 ⊢
  generalize b2 / Nat.gcd b2 b3 = c3 at hzp ⊢
  generalize b3 / Nat.gcd b2 b3 = c4 at hzp hc4 ⊢
  have hc2r : (c2 : ℝ) ≠ 0 := by exact_mod_cast hc2.ne'
  have hc4r : (c4 : ℝ) ≠ 0 := by exact_mod_cast hc4.ne'
  rw [Fintype.linearIndependent_iff]
  intro g hg
  obtain ⟨cf, hcf⟩ : ∃ cf : ℕ × ℕ × ℕ → ℝ, cf = fun q => ∑ p : BB6Kit.rowSet K L,
      if (p : ℕ × ℕ × ℕ).2.2 = q.2.2 then
        g p * ZR.coefP (c2 : ℝ) 0 (p : ℕ × ℕ × ℕ).1 q.1 * ZR.coefP (c4 : ℝ) 0 (p : ℕ × ℕ × ℕ).2.1 q.2.1
      else 0 := ⟨_, rfl⟩
  have hvan : ∀ r < R, ∀ s < S, ∀ t < T,
      ∑ q ∈ BB6Kit.rowSet K L, cf q * ((r : ℝ) + t * ((c1 : ℝ) / (c2 : ℝ))) ^ q.1 *
        ((s : ℝ) + t * ((c3 : ℝ) / (c4 : ℝ))) ^ q.2.1 *
        ((α1 : ℝ) ^ r * (α2 : ℝ) ^ s * (α3 : ℝ) ^ t) ^ q.2.2 = 0 := by
    intro r hr s hs t ht
    have hq0 : (r, s, t) ∈ range R ×ˢ range S ×ˢ range T := by
      simp only [mem_product, mem_range]
      exact ⟨hr, hs, ht⟩
    have h0 := congrFun hg ⟨(r, s, t), hq0⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    have hp_eq : ∀ p : BB6Kit.rowSet K L,
        ∑ q ∈ BB6Kit.rowSet K L, (if (p : ℕ × ℕ × ℕ).2.2 = q.2.2 then
          g p * ZR.coefP (c2 : ℝ) 0 (p : ℕ × ℕ × ℕ).1 q.1 * ZR.coefP (c4 : ℝ) 0 (p : ℕ × ℕ × ℕ).2.1 q.2.1
          else 0) * ((r : ℝ) + t * ((c1 : ℝ) / (c2 : ℝ))) ^ q.1 *
          ((s : ℝ) + t * ((c3 : ℝ) / (c4 : ℝ))) ^ q.2.1 *
          ((α1 : ℝ) ^ r * (α2 : ℝ) ^ s * (α3 : ℝ) ^ t) ^ q.2.2 =
        g p * ((Nat.choose ((((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).1 * c2 +
            (((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).2.2 * c1) (p : ℕ × ℕ × ℕ).1 : ℝ) *
          (Nat.choose ((((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).2.1 * c4 +
            (((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).2.2 * c3) (p : ℕ × ℕ × ℕ).2.1 : ℝ) *
          (α1 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).1) *
          (α2 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).2.1) *
          (α3 : ℝ) ^ ((p : ℕ × ℕ × ℕ).2.2 * (((⟨(r, s, t), hq0⟩ : range R ×ˢ range S ×ˢ range T) : ℕ × ℕ × ℕ)).2.2)) := by
      intro p
      obtain ⟨⟨k, m, ℓ⟩, hpmem⟩ := p
      dsimp only
      have h1 : ∑ q ∈ BB6Kit.rowSet K L, (if ℓ = q.2.2 then
            g ⟨(k, m, ℓ), hpmem⟩ * ZR.coefP (c2 : ℝ) 0 k q.1 * ZR.coefP (c4 : ℝ) 0 m q.2.1 else 0) *
            ((r : ℝ) + t * ((c1 : ℝ) / (c2 : ℝ))) ^ q.1 * ((s : ℝ) + t * ((c3 : ℝ) / (c4 : ℝ))) ^ q.2.1 *
            ((α1 : ℝ) ^ r * (α2 : ℝ) ^ s * (α3 : ℝ) ^ t) ^ q.2.2 =
          g ⟨(k, m, ℓ), hpmem⟩ * ∑ q ∈ BB6Kit.rowSet K L, (if ℓ = q.2.2 then
            ZR.coefP (c2 : ℝ) 0 k q.1 * ZR.coefP (c4 : ℝ) 0 m q.2.1 else 0) *
            ((r : ℝ) + t * ((c1 : ℝ) / (c2 : ℝ))) ^ q.1 * ((s : ℝ) + t * ((c3 : ℝ) / (c4 : ℝ))) ^ q.2.1 *
            ((α1 : ℝ) ^ r * (α2 : ℝ) ^ s * (α3 : ℝ) ^ t) ^ q.2.2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        split_ifs <;> ring
      rw [h1, ZR.slice K L k m ℓ hpmem (fun a => ZR.coefP (c2 : ℝ) 0 k a) (fun b => ZR.coefP (c4 : ℝ) 0 m b)
        (fun a ha => ZR.coefP_zero _ _ hc2r k a ha) (fun b hb => ZR.coefP_zero _ _ hc4r m b hb)]
      beta_reduce
      rw [← ZR.coefP_eval (c2 : ℝ) 0 hc2r k (r * c2 + t * c1) ((r : ℝ) + t * ((c1 : ℝ) / (c2 : ℝ))) (by
            push_cast
            first
            | (field_simp; ring)
            | field_simp
            | ring),
        ← ZR.coefP_eval (c4 : ℝ) 0 hc4r m (s * c4 + t * c3) ((s : ℝ) + t * ((c3 : ℝ) / (c4 : ℝ))) (by
            push_cast
            first
            | (field_simp; ring)
            | field_simp
            | ring)]
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
      ring
    exact (sum_congr rfl (fun p _ => by rw [hcf])).trans
      (by
        simp only [sum_mul]
        rw [sum_comm]
        exact (sum_congr rfl (fun p _ => hp_eq p)).trans h0)
  have hall := hzp cf hvan
  intro p0
  by_contra hne
  obtain ⟨pm, hpm, hmax⟩ := exists_max_image (univ.filter (fun p : BB6Kit.rowSet K L => g p ≠ 0))
    (fun p : BB6Kit.rowSet K L => (p : ℕ × ℕ × ℕ).1 + (p : ℕ × ℕ × ℕ).2.1) ⟨p0, by simp [hne]⟩
  rw [mem_filter] at hpm
  have hz := hall (pm : ℕ × ℕ × ℕ) pm.2
  rw [hcf] at hz
  beta_reduce at hz
  rw [sum_eq_single pm] at hz
  · rw [if_pos rfl, ZR.coefP_diag _ _ hc2r, ZR.coefP_diag _ _ hc4r] at hz
    have hf1 : ((pm : ℕ × ℕ × ℕ).1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hf2 : ((pm : ℕ × ℕ × ℕ).2.1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hp1 : (c2 : ℝ) ^ (pm : ℕ × ℕ × ℕ).1 / ((pm : ℕ × ℕ × ℕ).1.factorial : ℝ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ hc2r) hf1
    have hp2 : (c4 : ℝ) ^ (pm : ℕ × ℕ × ℕ).2.1 / ((pm : ℕ × ℕ × ℕ).2.1.factorial : ℝ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ hc4r) hf2
    exact hpm.2 (by
      rcases mul_eq_zero.mp hz with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hp1
      · exact absurd h hp2)
  · intro p _ hp
    by_cases hℓ : (p : ℕ × ℕ × ℕ).2.2 = (pm : ℕ × ℕ × ℕ).2.2
    · rw [if_pos hℓ]
      by_cases hg0 : g p = 0
      · rw [hg0, zero_mul, zero_mul]
      · have hle := hmax p (by rw [mem_filter]; exact ⟨mem_univ _, hg0⟩)
        rcases Nat.lt_or_ge (p : ℕ × ℕ × ℕ).1 (pm : ℕ × ℕ × ℕ).1 with h1 | h1
        · rw [ZR.coefP_zero _ _ hc2r _ _ h1, mul_zero, zero_mul]
        · rcases Nat.lt_or_ge (p : ℕ × ℕ × ℕ).2.1 (pm : ℕ × ℕ × ℕ).2.1 with h2 | h2
          · rw [ZR.coefP_zero _ _ hc4r _ _ h2, mul_zero]
          · exfalso
            apply hp
            apply Subtype.ext
            exact Prod.ext (by omega) (Prod.ext (by omega) hℓ)
    · rw [if_neg hℓ]
  · intro h
    exact absurd (mem_univ pm) h
