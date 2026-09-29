-- Prove2me | solution 1 for FourExp.small_irreducible_factor
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T09:51:23.534343+00:00
-- url     : https://prove2.me/submissions/6b6f512b-dbcc-4ced-8a3b-154e6c2a47fe

import Mathlib

open Polynomial

namespace FourExpGelfond

lemma eval_eq_prod_roots (p : ℂ[X]) (x : ℂ) :
    p.eval x = p.leadingCoeff * (p.roots.map fun a => x - a).prod := by
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← h]
  simp [eval_multiset_prod, Multiset.map_map, Function.comp_def]

lemma norm_prod_map {ι : Type*} (s : Multiset ι) (f : ι → ℂ) :
    ‖(s.map f).prod‖ = (s.map fun i => ‖f i‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

lemma prod_map_le {ι : Type*} (s : Multiset ι) (f g : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ g i) : (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have ha := h a (Multiset.mem_cons_self a s)
    have ha0 := h0 a (Multiset.mem_cons_self a s)
    have hs0 : 0 ≤ (s.map f).prod := Multiset.prod_nonneg fun x hx => by
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
      exact h0 i (Multiset.mem_cons_of_mem hi)
    exact mul_le_mul ha (ih (fun i hi => h0 i (Multiset.mem_cons_of_mem hi))
      (fun i hi => h i (Multiset.mem_cons_of_mem hi))) hs0 (ha0.trans ha)

/-- At a root `α₁` nearer to `θ` than every root of `G`: `|G(α₁)| ≤ 2ⁿ |G(θ)|`. -/
lemma eval_near (G : ℂ[X]) (θ α1 : ℂ) (hnear : ∀ β ∈ G.roots, ‖θ - α1‖ ≤ ‖θ - β‖) :
    ‖G.eval α1‖ ≤ 2 ^ G.natDegree * ‖G.eval θ‖ := by
  rw [eval_eq_prod_roots G α1, eval_eq_prod_roots G θ, norm_mul, norm_mul, norm_prod_map,
    norm_prod_map]
  have hle := prod_map_le G.roots (fun β => ‖α1 - β‖) (fun β => 2 * ‖θ - β‖)
    (fun _ _ => norm_nonneg _) (fun β hβ => by
      have h1 := norm_sub_le_norm_sub_add_norm_sub α1 θ β
      rw [norm_sub_rev α1 θ] at h1
      linarith [hnear β hβ])
  have h2 : (G.roots.map fun β => 2 * ‖θ - β‖).prod
      = 2 ^ G.natDegree * (G.roots.map fun β => ‖θ - β‖).prod := by
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [h2] at hle
  calc ‖G.leadingCoeff‖ * (G.roots.map fun β => ‖α1 - β‖).prod
      ≤ ‖G.leadingCoeff‖ * (2 ^ G.natDegree * (G.roots.map fun β => ‖θ - β‖).prod) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = _ := by ring

/-- Anywhere: `|G(a)| ≤ 2ⁿ max(1,|a|)ⁿ M(G)`. -/
lemma eval_far (G : ℂ[X]) (a : ℂ) :
    ‖G.eval a‖ ≤ 2 ^ G.natDegree * max 1 ‖a‖ ^ G.natDegree * G.mahlerMeasure := by
  rw [eval_eq_prod_roots G a, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, norm_mul, norm_prod_map]
  have hle := prod_map_le G.roots (fun β => ‖a - β‖) (fun β => (2 * max 1 ‖a‖) * max 1 ‖β‖)
    (fun _ _ => norm_nonneg _) (fun β _ => by
      have h1 := norm_sub_le a β
      have h2 : ‖a‖ ≤ max 1 ‖a‖ := le_max_right _ _
      have h3 : ‖β‖ ≤ max 1 ‖β‖ := le_max_right _ _
      have h4 : (1 : ℝ) ≤ max 1 ‖a‖ := le_max_left _ _
      have h5 : (1 : ℝ) ≤ max 1 ‖β‖ := le_max_left _ _
      nlinarith [mul_le_mul h2 h5 zero_le_one (by linarith),
        mul_le_mul h4 h3 (norm_nonneg _) (by linarith)])
  have h2 : (G.roots.map fun β => (2 * max 1 ‖a‖) * max 1 ‖β‖).prod
      = (2 * max 1 ‖a‖) ^ G.natDegree * (G.roots.map fun β => max 1 ‖β‖).prod := by
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [h2] at hle
  calc ‖G.leadingCoeff‖ * (G.roots.map fun β => ‖a - β‖).prod
      ≤ ‖G.leadingCoeff‖ * ((2 * max 1 ‖a‖) ^ G.natDegree * (G.roots.map fun β => max 1 ‖β‖).prod) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = _ := by rw [mul_pow]; ring

/-- The root product in `Res(F, G) = a^n ∏ G(α)`, when a root `α₁` of `F` is nearest to `θ`. -/
lemma bound_near (F G : ℂ[X]) (θ α1 : ℂ) (h1 : α1 ∈ F.roots)
    (hnear : ∀ β ∈ G.roots, ‖θ - α1‖ ≤ ‖θ - β‖) (hG1 : 1 ≤ G.mahlerMeasure) :
    ‖F.leadingCoeff ^ G.natDegree * (F.roots.map G.eval).prod‖
      ≤ 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree
        * G.mahlerMeasure ^ F.natDegree * ‖G.eval θ‖ := by
  obtain ⟨s, hs⟩ : ∃ s, F.roots = α1 ::ₘ s := ⟨_, (Multiset.cons_erase h1).symm⟩
  have hcard : Multiset.card s + 1 = F.natDegree := by
    have := IsAlgClosed.card_roots_eq_natDegree (p := F)
    rw [hs, Multiset.card_cons] at this
    exact this
  have hmax0 : 0 ≤ (s.map fun a => max 1 ‖a‖).prod := Multiset.prod_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
    exact zero_le_one.trans (le_max_left _ _)
  have hMF : ‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod ≤ F.mahlerMeasure := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots F, hs, Multiset.map_cons, Multiset.prod_cons]
    have hnn : 0 ≤ ‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod :=
      mul_nonneg (norm_nonneg _) hmax0
    calc ‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod
        = (‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod) * 1 := by ring
      _ ≤ (‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod) * max 1 ‖α1‖ :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hnn
      _ = _ := by ring
  have hP0 : 0 ≤ (s.map fun a => ‖G.eval a‖).prod := Multiset.prod_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
    exact norm_nonneg _
  have hA := eval_near G θ α1 (fun β hβ => hnear β hβ)
  have hB := prod_map_le s (fun a => ‖G.eval a‖)
    (fun a => 2 ^ G.natDegree * max 1 ‖a‖ ^ G.natDegree * G.mahlerMeasure)
    (fun _ _ => norm_nonneg _) (fun a _ => eval_far G a)
  have hfun : (fun a : ℂ => 2 ^ G.natDegree * max 1 ‖a‖ ^ G.natDegree * G.mahlerMeasure)
      = fun a => (2 ^ G.natDegree * G.mahlerMeasure) * max 1 ‖a‖ ^ G.natDegree := by
    funext a; ring
  rw [hfun, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.prod_map_pow] at hB
  rw [norm_mul, norm_pow, hs, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_prod_map]
  have hMG0 : 0 ≤ G.mahlerMeasure := zero_le_one.trans hG1
  have hMF0 : 0 ≤ F.mahlerMeasure := (mul_nonneg (norm_nonneg _) hmax0).trans hMF
  calc ‖F.leadingCoeff‖ ^ G.natDegree * (‖G.eval α1‖ * (s.map fun a => ‖G.eval a‖).prod)
      ≤ ‖F.leadingCoeff‖ ^ G.natDegree * ((2 ^ G.natDegree * ‖G.eval θ‖)
          * ((2 ^ G.natDegree * G.mahlerMeasure) ^ Multiset.card s
            * (s.map fun a => max 1 ‖a‖).prod ^ G.natDegree)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hB hP0 (by positivity)) (by positivity)
    _ = 2 ^ G.natDegree * (2 ^ G.natDegree) ^ Multiset.card s
          * (‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod) ^ G.natDegree
          * G.mahlerMeasure ^ Multiset.card s * ‖G.eval θ‖ := by ring
    _ ≤ 2 ^ G.natDegree * (2 ^ G.natDegree) ^ Multiset.card s * F.mahlerMeasure ^ G.natDegree
          * G.mahlerMeasure ^ (Multiset.card s + 1) * ‖G.eval θ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul _ (pow_le_pow_right₀ hG1 (Nat.le_succ _)) (pow_nonneg hMG0 _)
          (mul_nonneg (by positivity) (pow_nonneg hMF0 _))
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hmax0) hMF _) (by positivity)
    _ = _ := by
        have e2 : (2 : ℝ) ^ ((Multiset.card s + 1) * G.natDegree)
            = 2 ^ G.natDegree * (2 ^ G.natDegree) ^ Multiset.card s := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
        rw [← hcard, e2]

lemma splits_C (p : ℂ[X]) : p.Splits := splits_iff_card_roots.2 IsAlgClosed.card_roots_eq_natDegree

/-- Roy–Waldschmidt 1997, Corollary 3.7, from `|Res(F, G)| ≥ 1`. -/
lemma res_lower (F G : ℂ[X]) (hF : 0 < F.natDegree) (hMF : 1 ≤ F.mahlerMeasure)
    (hMG : 1 ≤ G.mahlerMeasure) (hres : 1 ≤ ‖resultant F G‖) (θ : ℂ) :
    1 ≤ 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree
      * G.mahlerMeasure ^ F.natDegree * max ‖F.eval θ‖ ‖G.eval θ‖ := by
  classical
  have hne : ((F.roots + G.roots).toFinset).Nonempty := by
    have hc : 0 < Multiset.card F.roots := by
      rw [IsAlgClosed.card_roots_eq_natDegree]; exact hF
    obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 hc
    exact ⟨z, Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inl hz))⟩
  obtain ⟨z, hzS, hzmin⟩ := Finset.exists_min_image _ (fun x => ‖θ - x‖) hne
  have hmem : ∀ x, x ∈ F.roots ∨ x ∈ G.roots → ‖θ - z‖ ≤ ‖θ - x‖ := fun x hx =>
    hzmin x (Multiset.mem_toFinset.2 (Multiset.mem_add.2 hx))
  rcases Multiset.mem_add.1 (Multiset.mem_toFinset.1 hzS) with hz | hz
  · have e := resultant_eq_prod_eval F G G.natDegree le_rfl (splits_C F)
    have hb := bound_near F G θ z hz (fun β hβ => hmem β (Or.inr hβ)) hMG
    rw [← e] at hb
    refine hres.trans (hb.trans ?_)
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  · have e := resultant_eq_prod_eval G F F.natDegree le_rfl (splits_C G)
    have hb := bound_near G F θ z hz (fun β hβ => hmem β (Or.inl hβ)) hMF
    rw [← e] at hb
    have hcomm : ‖resultant F G‖ = ‖resultant G F‖ := by
      rw [resultant_comm]
      simp
    rw [hcomm] at hres
    refine hres.trans (hb.trans ?_)
    calc 2 ^ (G.natDegree * F.natDegree) * G.mahlerMeasure ^ F.natDegree
          * F.mahlerMeasure ^ G.natDegree * ‖F.eval θ‖
        = 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree
          * G.mahlerMeasure ^ F.natDegree * ‖F.eval θ‖ := by rw [mul_comm G.natDegree]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

/-- `M(T) ≥ 1` for a non-zero integer polynomial, read in `ℂ`. -/
lemma one_le_M (T : ℤ[X]) (hT : T ≠ 0) : 1 ≤ (T.map (Int.castRingHom ℂ)).mahlerMeasure := by
  apply one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  rw [leadingCoeff_map_of_injective Int.cast_injective]
  have h1 : (1 : ℤ) ≤ |T.leadingCoeff| := Int.one_le_abs (leadingCoeff_ne_zero.mpr hT)
  simp only [eq_intCast, Complex.norm_intCast]
  exact_mod_cast h1

lemma aeval_eq_eval_map (T : ℤ[X]) (α : ℂ) :
    Polynomial.aeval α T = (T.map (Int.castRingHom ℂ)).eval α := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

/-- The pair bound in `ℤ[X]`: `Q` irreducible and non-constant, `Q ∤ T`. -/
lemma int_pair (Q T : ℤ[X]) (hQ : Irreducible Q) (hQd : 0 < Q.natDegree) (hT : T ≠ 0)
    (hndvd : ¬ Q ∣ T) (α : ℂ) :
    1 ≤ 2 ^ (Q.natDegree * T.natDegree) * (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ T.natDegree
      * (T.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree
      * max ‖Polynomial.aeval α Q‖ ‖Polynomial.aeval α T‖ := by
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ with hφ
  set ψ : ℤ →+* ℂ := Int.castRingHom ℂ with hψ
  have hprim : Q.IsPrimitive := hQ.isPrimitive hQd.ne'
  have hQ'irr : Irreducible (Q.map φ) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hQ
  have hndvd' : ¬ Q.map φ ∣ T.map φ :=
    fun hdiv => hndvd ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast Q T hprim).mpr hdiv)
  have hcop : IsCoprime (Q.map φ) (T.map φ) := (hQ'irr.coprime_iff_not_dvd).mpr hndvd'
  have hres' := resultant_ne_zero (Q.map φ) (T.map φ) hcop
  have hresZ : Q.resultant T Q.natDegree T.natDegree ≠ 0 := by
    intro h0
    apply hres'
    rw [natDegree_map_eq_of_injective Int.cast_injective, natDegree_map_eq_of_injective Int.cast_injective,
      resultant_map_map, h0, map_zero]
  have hresC : 1 ≤ ‖resultant (Q.map ψ) (T.map ψ)‖ := by
    rw [natDegree_map_eq_of_injective Int.cast_injective, natDegree_map_eq_of_injective Int.cast_injective,
      resultant_map_map, hψ, eq_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hresZ
  have hQC : 0 < (Q.map ψ).natDegree := by rwa [natDegree_map_eq_of_injective Int.cast_injective]
  have h := res_lower (Q.map ψ) (T.map ψ) hQC (one_le_M Q hQ.ne_zero) (one_le_M T hT) hresC α
  rw [natDegree_map_eq_of_injective Int.cast_injective,
    natDegree_map_eq_of_injective Int.cast_injective] at h
  rwa [aeval_eq_eval_map, aeval_eq_eval_map]

/-- The quantity bounded below for every factor of `P` other than `Q`. -/
def Good (Q : ℤ[X]) (α : ℂ) (T : ℤ[X]) : Prop :=
  T ≠ 0 ∧ 1 ≤ 2 ^ (Q.natDegree * T.natDegree)
    * (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ T.natDegree
    * (T.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree * ‖Polynomial.aeval α T‖

lemma good_one (Q : ℤ[X]) (α : ℂ) : Good Q α 1 := by
  refine ⟨one_ne_zero, ?_⟩
  simp [Polynomial.map_one, mahlerMeasure_one]

lemma good_mul (Q : ℤ[X]) (α : ℂ) (T₁ T₂ : ℤ[X]) (h₁ : Good Q α T₁) (h₂ : Good Q α T₂) :
    Good Q α (T₁ * T₂) := by
  obtain ⟨hT₁, hb₁⟩ := h₁
  obtain ⟨hT₂, hb₂⟩ := h₂
  refine ⟨mul_ne_zero hT₁ hT₂, ?_⟩
  rw [natDegree_mul hT₁ hT₂, Polynomial.map_mul, mahlerMeasure_mul, map_mul, norm_mul]
  have e : 2 ^ (Q.natDegree * (T₁.natDegree + T₂.natDegree))
      * (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ (T₁.natDegree + T₂.natDegree)
      * ((T₁.map (Int.castRingHom ℂ)).mahlerMeasure * (T₂.map (Int.castRingHom ℂ)).mahlerMeasure)
          ^ Q.natDegree
      * (‖Polynomial.aeval α T₁‖ * ‖Polynomial.aeval α T₂‖)
      = (2 ^ (Q.natDegree * T₁.natDegree)
          * (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ T₁.natDegree
          * (T₁.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree * ‖Polynomial.aeval α T₁‖)
        * (2 ^ (Q.natDegree * T₂.natDegree)
          * (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ T₂.natDegree
          * (T₂.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree * ‖Polynomial.aeval α T₂‖) := by
    rw [mul_add, pow_add, pow_add, mul_pow]
    ring
  rw [e]
  nlinarith

/-- An irreducible factor `T` with `Q ∤ T` and `|Q(α)| ≤ |T(α)|` is `Good`. -/
lemma good_of_factor (Q T : ℤ[X]) (hQ : Irreducible Q) (hQd : 0 < Q.natDegree) (hT : T ≠ 0)
    (hndvd : ¬ Q ∣ T) (α : ℂ) (hmin : ‖Polynomial.aeval α Q‖ ≤ ‖Polynomial.aeval α T‖) :
    Good Q α T := by
  refine ⟨hT, ?_⟩
  have h := int_pair Q T hQ hQd hT hndvd α
  rwa [max_eq_right hmin] at h

/-- The numerical core of Gel'fond's lemma, with the polynomials abstracted away. -/
lemma numeric (n lam H MQ MR vQ vR : ℝ) (d δ r e : ℕ) (he : 0 < e) (hδd : e * δ ≤ d)
    (hrd : r ≤ d) (hdn : (d : ℝ) ≤ n) (hlog : n ≤ Real.log H) (hH0 : 0 < H)
    (hMQ : 1 ≤ MQ) (hMR : 1 ≤ MR) (hMP : MQ ^ e * MR ≤ Real.sqrt ((d : ℝ) + 1) * H)
    (hvQ : 0 ≤ vQ) (hgood : 1 ≤ 2 ^ (δ * r) * MQ ^ r * MR ^ δ * vR)
    (hsmall : vQ ^ e * vR < Real.exp (Real.log H * (-(lam * n)))) :
    vQ < Real.exp (Real.log H * (-((lam - 6) * n / e))) ∧
      2 ^ δ * MQ ≤ Real.exp (Real.log H * ((1 : ℝ) / e)) * Real.exp (2 * n / e) := by
  set L := Real.log H with hL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : 0 ≤ n := hd0.trans hdn
  have hL0 : 0 ≤ L := hn0.trans hlog
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hδd' : δ ≤ d := le_trans (Nat.le_mul_of_pos_left δ he) hδd
  have hδ' : (δ : ℝ) ≤ d / e := by
    rw [le_div_iff₀ he']
    have : ((e * δ : ℕ) : ℝ) ≤ d := by exact_mod_cast hδd
    push_cast at this
    linarith
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : Real.sqrt ((d : ℝ) + 1) ≤ Real.exp (d / 2) := by
    rw [Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
    have h := Real.add_one_le_exp (d : ℝ)
    calc (d : ℝ) + 1 ≤ Real.exp d := by linarith
      _ = Real.exp ((2 : ℕ) * (d / 2)) := by congr 1; push_cast; ring
  set B := Real.sqrt ((d : ℝ) + 1) * H with hB
  have hMQe1 : 1 ≤ MQ ^ e := one_le_pow₀ hMQ
  have hB1 : 1 ≤ B := by
    have : 1 ≤ MQ ^ e * MR := one_le_mul_of_one_le_of_one_le hMQe1 hMR
    linarith
  have hBexp : B ≤ Real.exp (d / 2 + L) := by
    calc B = Real.sqrt ((d : ℝ) + 1) * H := rfl
      _ ≤ Real.exp (d / 2) * H := mul_le_mul_of_nonneg_right hsq hH0.le
      _ = Real.exp (d / 2) * Real.exp L := by rw [hL, Real.exp_log hH0]
      _ = Real.exp (d / 2 + L) := (Real.exp_add _ _).symm
  have hMQB : MQ ≤ B :=
    (le_self_pow₀ hMQ he.ne').trans
      ((le_mul_of_one_le_right (zero_le_one.trans hMQe1) hMR).trans hMP)
  have hMRB : MR ≤ B := (le_mul_of_one_le_left (zero_le_one.trans hMR) hMQe1).trans hMP
  have hK : 2 ^ (δ * r) * MQ ^ r * MR ^ δ ≤ Real.exp (4 * n * L) := by
    have h2 : (2 : ℝ) ^ (δ * r) ≤ Real.exp (n * L) := by
      have hk : ((δ * r : ℕ) : ℝ) ≤ n * L := by
        have h1 : ((δ * r : ℕ) : ℝ) ≤ (d : ℝ) * d := by exact_mod_cast Nat.mul_le_mul hδd' hrd
        have h3 : (d : ℝ) * d ≤ n * L := mul_le_mul hdn (hdn.trans hlog) hd0 hn0
        linarith
      calc (2 : ℝ) ^ (δ * r) = Real.exp ((δ * r : ℕ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        _ ≤ Real.exp (n * L) := by
            apply Real.exp_le_exp.2
            have := mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg (δ * r) : (0 : ℝ) ≤ (δ * r : ℕ))
            linarith
    have hMQr : MQ ^ r ≤ B ^ d :=
      (pow_le_pow_left₀ (zero_le_one.trans hMQ) hMQB r).trans (pow_le_pow_right₀ hB1 hrd)
    have hMRd : MR ^ δ ≤ B ^ d :=
      (pow_le_pow_left₀ (zero_le_one.trans hMR) hMRB δ).trans (pow_le_pow_right₀ hB1 hδd')
    have hBd : B ^ d ≤ Real.exp (d * (d / 2 + L)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (zero_le_one.trans hB1) hBexp d
    have hexp3 : Real.exp (d * (d / 2 + L)) * Real.exp (d * (d / 2 + L))
        ≤ Real.exp (3 * n * L) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (d : ℝ) * d ≤ n * L := mul_le_mul hdn (hdn.trans hlog) hd0 hn0
      have h3 : (d : ℝ) * L ≤ n * L := mul_le_mul_of_nonneg_right hdn hL0
      nlinarith
    have hBd0 : 0 ≤ B ^ d := pow_nonneg (zero_le_one.trans hB1) _
    calc 2 ^ (δ * r) * MQ ^ r * MR ^ δ ≤ Real.exp (n * L) * B ^ d * B ^ d :=
          mul_le_mul (mul_le_mul h2 hMQr (pow_nonneg (zero_le_one.trans hMQ) r) (Real.exp_pos _).le)
            hMRd (pow_nonneg (zero_le_one.trans hMR) δ) (mul_nonneg (Real.exp_pos _).le hBd0)
      _ = Real.exp (n * L) * (B ^ d * B ^ d) := by ring
      _ ≤ Real.exp (n * L) * (Real.exp (d * (d / 2 + L)) * Real.exp (d * (d / 2 + L))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hBd hBd hBd0 (Real.exp_pos _).le) (Real.exp_pos _).le
      _ ≤ Real.exp (n * L) * Real.exp (3 * n * L) :=
          mul_le_mul_of_nonneg_left hexp3 (Real.exp_pos _).le
      _ = Real.exp (4 * n * L) := by rw [← Real.exp_add]; congr 1; ring
  set Kp := 2 ^ (δ * r) * MQ ^ r * MR ^ δ with hKpdef
  have hKp : 0 ≤ Kp := mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hMQ) r))
    (pow_nonneg (zero_le_one.trans hMR) δ)
  have hvR0 : 0 ≤ vR := by
    by_contra hc
    push_neg at hc
    nlinarith
  refine ⟨?_, ?_⟩
  · have hK6 : Kp ≤ Real.exp (6 * n * L) :=
      hK.trans (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hn0 hL0]))
    have hpow : vQ ^ e < Real.exp (-((lam - 6) * n) * L) := by
      calc vQ ^ e = vQ ^ e * 1 := (mul_one _).symm
        _ ≤ vQ ^ e * (Kp * vR) := mul_le_mul_of_nonneg_left hgood (pow_nonneg hvQ e)
        _ = (vQ ^ e * vR) * Kp := by ring
        _ ≤ (vQ ^ e * vR) * Real.exp (6 * n * L) :=
            mul_le_mul_of_nonneg_left hK6 (mul_nonneg (pow_nonneg hvQ e) hvR0)
        _ < Real.exp (L * (-(lam * n))) * Real.exp (6 * n * L) :=
            mul_lt_mul_of_pos_right hsmall (Real.exp_pos _)
        _ = Real.exp (-((lam - 6) * n) * L) := by rw [← Real.exp_add]; congr 1; ring
    by_contra hc
    push_neg at hc
    have h1 : Real.exp (L * (-((lam - 6) * n / e))) ^ e ≤ vQ ^ e :=
      pow_le_pow_left₀ (Real.exp_pos _).le hc e
    rw [← Real.exp_nat_mul] at h1
    have h2 : ((e : ℕ) : ℝ) * (L * (-((lam - 6) * n / e))) = -((lam - 6) * n) * L := by
      field_simp <;> ring
    rw [h2] at h1
    linarith
  · have hMQe : MQ ^ e ≤ Real.exp (d / 2 + L) :=
      (le_mul_of_one_le_right (zero_le_one.trans hMQe1) hMR).trans (hMP.trans hBexp)
    have hMQle : MQ ≤ Real.exp ((d / 2 + L) / e) := by
      by_contra hc
      push_neg at hc
      have h1 := pow_lt_pow_left₀ hc (Real.exp_pos _).le he.ne'
      rw [← Real.exp_nat_mul] at h1
      have h2 : ((e : ℕ) : ℝ) * ((d / 2 + L) / e) = d / 2 + L := by
        rw [mul_div_assoc', mul_div_right_comm, div_self he'.ne', one_mul]
      rw [h2] at h1
      linarith
    have h2d : (2 : ℝ) ^ δ ≤ Real.exp (d / e) := by
      calc (2 : ℝ) ^ δ = Real.exp (δ * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        _ ≤ Real.exp (d / e) := by
            apply Real.exp_le_exp.2
            have := mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg δ : (0 : ℝ) ≤ δ)
            linarith
    calc 2 ^ δ * MQ ≤ Real.exp (d / e) * Real.exp ((d / 2 + L) / e) :=
          mul_le_mul h2d hMQle (zero_le_one.trans hMQ) (Real.exp_pos _).le
      _ = Real.exp (L * (1 / e)) * Real.exp ((3 * d / 2) / e) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (L * (1 / e)) * Real.exp (2 * n / e) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply Real.exp_le_exp.2
          apply div_le_div_of_nonneg_right _ he'.le
          linarith

lemma mahlerMeasure_pow' (p : ℂ[X]) (k : ℕ) : (p ^ k).mahlerMeasure = p.mahlerMeasure ^ k := by
  induction k with
  | zero => simp [mahlerMeasure_one]
  | succ k ih => rw [pow_succ, mahlerMeasure_mul, ih, pow_succ]

end FourExpGelfond

theorem solution
    (α : ℂ) (hα : Transcendental ℚ α) (P : Polynomial ℤ) (hprim : P.IsPrimitive)
    (H n lam : ℝ) (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H)
    (hlog : n ≤ Real.log H) (hdeg : (P.natDegree : ℝ) ≤ n) (hlam : 6 < lam)
    (hsmall : ‖Polynomial.aeval α P‖ < H ^ (-(lam * n))) :
    ∃ Q : Polynomial ℤ, Q ∣ P ∧ Q.IsPrimitive ∧ Irreducible Q ∧
      ∃ s : ℕ, 0 < s ∧
        ‖Polynomial.aeval α Q‖ < H ^ (-((lam - 6) * n / s)) ∧
        (∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ H ^ ((1 : ℝ) / s) * Real.exp (2 * n / s)) ∧
        (Q.natDegree : ℝ) ≤ n / s := by
  classical
  set ψ : ℤ →+* ℂ := Int.castRingHom ℂ with hψ
  have hP0 : P ≠ 0 := hprim.ne_zero
  have hlc : (1 : ℝ) ≤ |(P.leadingCoeff : ℝ)| := by
    exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hP0)
  have hH1 : 1 ≤ H := hlc.trans (hPH P.natDegree)
  have hH0 : 0 < H := by linarith
  have hn0 : 0 ≤ n := (Nat.cast_nonneg _).trans hdeg
  -- `P` is not constant
  have hdpos : 0 < P.natDegree := by
    by_contra h0
    have hd0 : P.natDegree = 0 := by omega
    have hPC := eq_C_of_natDegree_eq_zero hd0
    have hu : IsUnit (P.coeff 0) := hprim _ ⟨1, by rw [mul_one]; exact hPC⟩
    have h1 : ‖Polynomial.aeval α P‖ = 1 := by
      rw [hPC, aeval_C, algebraMap_int_eq, eq_intCast, Complex.norm_intCast]
      rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
    have h2 : H ^ (-(lam * n)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hH1 (by nlinarith)
    linarith
  have hnu : ¬ IsUnit P := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu
    omega
  -- the irreducible factor with the smallest value at `α`
  set S := UniqueFactorizationMonoid.normalizedFactors P with hS
  have hSpos : 0 < S := (UniqueFactorizationMonoid.normalizedFactors_pos P hP0).2 hnu
  have hne : S.toFinset.Nonempty := by
    obtain ⟨T, hT⟩ := Multiset.exists_mem_of_ne_zero hSpos.ne'
    exact ⟨T, Multiset.mem_toFinset.2 hT⟩
  obtain ⟨Q, hQS', hmin'⟩ := Finset.exists_min_image _ (fun T => ‖Polynomial.aeval α T‖) hne
  have hQS : Q ∈ S := Multiset.mem_toFinset.1 hQS'
  have hmin : ∀ T ∈ S, ‖Polynomial.aeval α Q‖ ≤ ‖Polynomial.aeval α T‖ :=
    fun T hT => hmin' T (Multiset.mem_toFinset.2 hT)
  have hirr : ∀ T ∈ S, Irreducible T := UniqueFactorizationMonoid.irreducible_of_normalized_factor
  have hposS : ∀ T ∈ S, 0 < T.natDegree := by
    intro T hT
    by_contra h0
    have hTC := eq_C_of_natDegree_eq_zero (by omega : T.natDegree = 0)
    have hdvd : C (T.coeff 0) ∣ P := by
      rw [← hTC]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hT
    exact (hirr T hT).not_isUnit (by rw [hTC]; exact isUnit_C.mpr (hprim _ hdvd))
  have hQirr := hirr Q hQS
  have hQpos := hposS Q hQS
  set e := S.count Q with he_def
  have he : 0 < e := Multiset.count_pos.2 hQS
  set R := (S.filter fun T => ¬ T = Q).prod with hR
  have hprod : S.prod = Q ^ e * R := by
    have h := Multiset.filter_add_not (fun T => T = Q) S
    conv_lhs => rw [← h]
    rw [Multiset.prod_add, Multiset.filter_eq', Multiset.prod_replicate]
  have hgoodR : FourExpGelfond.Good Q α R := by
    refine Multiset.prod_induction (FourExpGelfond.Good Q α) _ (FourExpGelfond.good_mul Q α)
      (FourExpGelfond.good_one Q α) fun T hT => ?_
    obtain ⟨hTS, hTQ⟩ := Multiset.mem_filter.1 hT
    refine FourExpGelfond.good_of_factor Q T hQirr hQpos
      (UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hTS) ?_ α (hmin T hTS)
    intro hd
    apply hTQ
    have hn := normalize_eq_normalize hd (hQirr.associated_of_dvd (hirr T hTS) hd).symm.dvd
    rw [UniqueFactorizationMonoid.normalize_normalized_factor Q hQS,
      UniqueFactorizationMonoid.normalize_normalized_factor T hTS] at hn
    exact hn.symm
  -- `P = ±(Q^e · R)`
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hP0
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hPeq : P = Q ^ e * R * C r := by
    rw [hru, ← hprod]
    exact hu.symm
  have hR0 : R ≠ 0 := hgoodR.1
  have hQe0 : Q ^ e ≠ 0 := pow_ne_zero _ hQirr.ne_zero
  have hdeg_eq : P.natDegree = e * Q.natDegree + R.natDegree := by
    rw [hPeq, natDegree_mul (mul_ne_zero hQe0 hR0) (C_ne_zero.2 hr.ne_zero), natDegree_C, add_zero,
      natDegree_mul hQe0 hR0, natDegree_pow]
  have hMP : (Q.map ψ).mahlerMeasure ^ e * (R.map ψ).mahlerMeasure
      ≤ Real.sqrt ((P.natDegree : ℝ) + 1) * H := by
    have hM := mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm (P.map ψ)
    rw [natDegree_map_eq_of_injective Int.cast_injective] at hM
    have hsup : (P.map ψ).supNorm ≤ H := by
      obtain ⟨j, hj⟩ := (P.map ψ).exists_eq_supNorm
      rw [hj, coeff_map, hψ, eq_intCast, Complex.norm_intCast]
      exact hPH j
    have heq : (P.map ψ).mahlerMeasure = (Q.map ψ).mahlerMeasure ^ e * (R.map ψ).mahlerMeasure := by
      rw [hPeq, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, mahlerMeasure_mul,
        mahlerMeasure_mul, FourExpGelfond.mahlerMeasure_pow', Polynomial.map_C, mahlerMeasure_const]
      rcases Int.isUnit_iff.1 hr with h | h <;> simp [h, hψ]
    rw [← heq]
    exact hM.trans (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _))
  have hval : ‖Polynomial.aeval α P‖ = ‖Polynomial.aeval α Q‖ ^ e * ‖Polynomial.aeval α R‖ := by
    rw [hPeq, map_mul, map_mul, map_pow, aeval_C, norm_mul, norm_mul, norm_pow]
    rcases Int.isUnit_iff.1 hr with h | h <;> simp [h]
  have hsmall' : ‖Polynomial.aeval α Q‖ ^ e * ‖Polynomial.aeval α R‖
      < Real.exp (Real.log H * (-(lam * n))) := by
    rw [← hval, ← Real.rpow_def_of_pos hH0]
    exact hsmall
  have hnum := FourExpGelfond.numeric n lam H (Q.map ψ).mahlerMeasure (R.map ψ).mahlerMeasure
    ‖Polynomial.aeval α Q‖ ‖Polynomial.aeval α R‖ P.natDegree Q.natDegree R.natDegree e he
    (by rw [hdeg_eq]; omega) (by rw [hdeg_eq]; omega) hdeg hlog hH0
    (FourExpGelfond.one_le_M Q hQirr.ne_zero) (FourExpGelfond.one_le_M R hR0) hMP
    (norm_nonneg _) hgoodR.2 hsmall'
  refine ⟨Q, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQS,
    hQirr.isPrimitive hQpos.ne', hQirr, e, he, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hH0]
    exact hnum.1
  · intro i
    rw [Real.rpow_def_of_pos hH0]
    have hc := norm_coeff_le_choose_mul_mahlerMeasure i (Q.map ψ)
    rw [natDegree_map_eq_of_injective Int.cast_injective, coeff_map, hψ, eq_intCast,
      Complex.norm_intCast] at hc
    have hch : ((Q.natDegree.choose i : ℕ) : ℝ) ≤ 2 ^ Q.natDegree := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have hM0 : 0 ≤ (Q.map ψ).mahlerMeasure :=
      zero_le_one.trans (FourExpGelfond.one_le_M Q hQirr.ne_zero)
    exact hc.trans ((mul_le_mul_of_nonneg_right hch hM0).trans hnum.2)
  · have he' : (0 : ℝ) < e := by exact_mod_cast he
    rw [le_div_iff₀ he']
    have h1 : ((e * Q.natDegree : ℕ) : ℝ) ≤ P.natDegree := by
      exact_mod_cast (by rw [hdeg_eq]; omega : e * Q.natDegree ≤ P.natDegree)
    push_cast at h1
    linarith
