-- Prove2me | solution 1 for BalcanDDA.Piecewise.theorem3_3_pdim_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:17:11.655688+00:00
-- url     : https://prove2.me/submissions/d2196dcf-1d69-404e-9623-9bcb403d6c29

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim
import Definitions.Def_BalcanDDA_Piecewise_dual
import Definitions.Def_BalcanDDA_Piecewise_PiecewiseDecomposable

set_option autoImplicit false

open FoundationsML.Regression FoundationsML.RademacherVC

namespace BalcanP33

lemma sum_choose_le (n d : ℕ) : ∑ j ∈ Finset.range (d + 1), n.choose j ≤ (n + 1) ^ d := by
  rw [add_pow]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 : 1 ≤ d.choose j := Nat.choose_pos hj'
  calc n.choose j ≤ n ^ j := Nat.choose_le_pow n j
    _ ≤ n ^ j * 1 ^ (d - j) * d.choose j := by
      rw [one_pow, mul_one]; exact Nat.le_mul_of_pos_right _ h1

lemma sauer_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset (ι → Bool)) (d : ℕ)
    (h : ∀ S : Finset ι, (∀ T ⊆ S, ∃ p ∈ P, ∀ i ∈ S, (p i = true ↔ i ∈ T)) → S.card ≤ d) :
    P.card ≤ (Fintype.card ι + 1) ^ d := by
  classical
  let enc : (ι → Bool) → Finset ι := fun p => Finset.univ.filter (fun i => p i = true)
  have hmem : ∀ p i, i ∈ enc p ↔ p i = true := by
    intro p i; simp [enc]
  have hinj : Set.InjOn enc P := by
    intro p _ q _ hpq
    funext i
    have h1 := hmem p i
    have h2 := hmem q i
    rw [hpq] at h1
    exact Bool.eq_iff_iff.mpr (h1.symm.trans h2)
  have hcard : (P.image enc).card = P.card := Finset.card_image_of_injOn hinj
  have hvc : (P.image enc).vcDim ≤ d := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_shatterer] at hS
    apply h S
    intro T hT
    obtain ⟨u, hu, hSu⟩ := hS hT
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨p, hp, fun i hi => ?_⟩
    rw [← hSu, Finset.mem_inter, hmem]
    exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
  calc P.card = (P.image enc).card := hcard.symm
    _ ≤ (P.image enc).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ j ∈ Finset.Iic (P.image enc).vcDim, (Fintype.card ι).choose j :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ j ∈ Finset.range (d + 1), (Fintype.card ι).choose j := by
        apply Finset.sum_le_sum_of_subset
        intro j hj
        rw [Finset.mem_Iic] at hj
        exact Finset.mem_range.mpr (by omega)
    _ ≤ _ := sum_choose_le _ _

lemma growth_eq_of_full {Y : Type*} (H : Set (Y → Bool)) {m : ℕ} (y : Fin m → Y)
    (hfull : ∀ t : Fin m → Bool, ∃ h ∈ H, t = h ∘ y) : GrowthFunction H m = 2 ^ m := by
  have hle : ∀ z : Fin m → Y, Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ z} ≤ 2 ^ m := by
    intro z
    calc _ ≤ Nat.card (Fin m → Bool) := Finite.card_subtype_le _
      _ = 2 ^ m := by simp
  have hy : Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ y} = 2 ^ m := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hfull)]; simp
  have : Nonempty (Fin m → Y) := ⟨y⟩
  unfold GrowthFunction
  apply le_antisymm
  · exact ciSup_le hle
  · rw [← hy]
    exact le_ciSup (f := fun z : Fin m → Y => Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ z})
      ⟨2 ^ m, by rintro _ ⟨z, rfl⟩; exact hle z⟩ y

open BalcanDDA.Piecewise FoundationsML.Regression FoundationsML.RademacherVC in
lemma count_bound {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ))
    (G : Set (↥U → Bool)) (k dF dG : ℕ)
    (hdec : PiecewiseDecomposable (dual U) F G k)
    (hF : PseudoDim (dual F) dF) (hG : HasVCDim (dualB G) dG)
    (N : ℕ) (x : Fin N → X) (hsh : Shatters U x) :
    2 ^ N ≤ (N * k + 1) ^ dG * (N + 1) ^ dF := by
  classical
  obtain ⟨t, ht⟩ := hsh
  choose u huU hu using ht
  have hd : ∀ i, (fun h : ↥U => (h : X → ℝ) (x i)) ∈ dual U := fun i => ⟨x i, rfl⟩
  choose g hg f hf hfg using fun i => hdec _ (hd i)
  let v : (Fin N → Bool) → ↥U := fun b => ⟨u b, huU b⟩
  let R : (Fin N → Bool) → (Fin N × Fin k → Bool) := fun b ij => g ij.1 ij.2 (v b)
  have hval : ∀ b i, (u b) (x i) = f i (fun j => g i j (v b)) (v b) := fun b i => hfg i (v b)
  have hreg : ((Finset.univ : Finset (Fin N → Bool)).image R).card ≤ (N * k + 1) ^ dG := by
    have key := sauer_pow ((Finset.univ : Finset (Fin N → Bool)).image R) dG ?_
    · simpa [Fintype.card_prod] using key
    intro S hS
    let e : Fin S.card ≃ S := S.equivFin.symm
    let emb : Fin S.card ↪ Fin N × Fin k := e.toEmbedding.trans (Function.Embedding.subtype _)
    let y : Fin S.card → ↥G := fun l => ⟨g (emb l).1 (emb l).2, hg _ _⟩
    apply hG.2 S.card
    apply growth_eq_of_full _ y
    intro τ
    obtain ⟨r, hr, hrS⟩ := hS ((Finset.univ.filter (fun l => τ l = true)).map emb) (by
      intro ij hij
      rw [Finset.mem_map] at hij
      obtain ⟨l, _, rfl⟩ := hij
      exact (e l).2)
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨fun g' => (g' : ↥U → Bool) (v b), ⟨v b, rfl⟩, ?_⟩
    funext l
    have h1 := hrS (emb l) (e l).2
    rw [Finset.mem_map', Finset.mem_filter] at h1
    show τ l = R b (emb l)
    have h3 : R b (emb l) = true ↔ τ l = true := by
      rw [h1]; simp
    exact Bool.eq_iff_iff.mpr h3.symm
  have hpiece : ∀ r ∈ (Finset.univ : Finset (Fin N → Bool)).image R,
      ((Finset.univ : Finset (Fin N → Bool)).filter (fun b => R b = r)).card ≤ (N + 1) ^ dF := by
    intro r _
    have key := sauer_pow ((Finset.univ : Finset (Fin N → Bool)).filter (fun b => R b = r)) dF ?_
    · simpa using key
    intro S hS
    let e : Fin S.card ≃ S := S.equivFin.symm
    let emb : Fin S.card ↪ Fin N := e.toEmbedding.trans (Function.Embedding.subtype _)
    let z : Fin S.card → ↥F := fun l => ⟨f (emb l) (fun j => r (emb l, j)), hf _ _⟩
    refine hF.2 S.card ⟨z, fun l => t (emb l), fun b' => ?_⟩
    obtain ⟨p, hp, hpS⟩ := hS ((Finset.univ.filter (fun l => b' l = true)).map emb) (by
      intro i hi
      rw [Finset.mem_map] at hi
      obtain ⟨l, _, rfl⟩ := hi
      exact (e l).2)
    rw [Finset.mem_filter] at hp
    refine ⟨fun f' => (f' : ↥U → ℝ) (v p), ⟨v p, rfl⟩, fun l => ?_⟩
    have h1 := hpS (emb l) (e l).2
    rw [Finset.mem_map', Finset.mem_filter] at h1
    have h2 := hu p (emb l)
    have h4 : (u p) (x (emb l)) = f (emb l) (fun j => r (emb l, j)) (v p) := by
      rw [hval p (emb l)]
      have h3 : (fun j => g (emb l) j (v p)) = fun j => r (emb l, j) := by
        funext j; rw [← hp.2]
      rw [h3]
    rw [h4] at h2
    show b' l = true ↔ t (emb l) < f (emb l) (fun j => r (emb l, j)) (v p)
    rw [← h2, h1]; simp
  have hsum := Finset.card_eq_sum_card_image R (Finset.univ : Finset (Fin N → Bool))
  have hB : (Finset.univ : Finset (Fin N → Bool)).card = 2 ^ N := by simp
  rw [← hB, hsum]
  calc ∑ r ∈ (Finset.univ : Finset (Fin N → Bool)).image R,
        ((Finset.univ : Finset (Fin N → Bool)).filter (fun b => R b = r)).card
      ≤ ∑ r ∈ (Finset.univ : Finset (Fin N → Bool)).image R, (N + 1) ^ dF :=
        Finset.sum_le_sum hpiece
    _ = ((Finset.univ : Finset (Fin N → Bool)).image R).card * (N + 1) ^ dF := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (N * k + 1) ^ dG * (N + 1) ^ dF := Nat.mul_le_mul_right _ hreg

lemma analytic (k dF dG N : ℕ) (hk : 1 ≤ k) (h : 2 ^ N ≤ (N * k + 1) ^ dG * (N + 1) ^ dF) :
    (N : ℝ) ≤ 4 * (((dF + dG : ℕ) : ℝ) / Real.log 2) *
          Real.log (2 * (((dF + dG : ℕ) : ℝ) / Real.log 2)) +
        2 * ((((dF + dG : ℕ) : ℝ) + (dG : ℝ) * Real.log k) / Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hkr
  rcases Nat.eq_zero_or_pos (dF + dG) with hD | hD
  · have hF0 : dF = 0 := by omega
    have hG0 : dG = 0 := by omega
    subst hF0; subst hG0
    have h1 : 2 ^ N ≤ 1 := by simpa using h
    have h2 : N < 2 ^ N := Nat.lt_two_pow_self
    have hN : N = 0 := by omega
    subst hN; simp
  · have hD1 : (1 : ℝ) ≤ ((dF + dG : ℕ) : ℝ) := by exact_mod_cast hD
    have hDsum : ((dF + dG : ℕ) : ℝ) = (dF : ℝ) + dG := by push_cast; ring
    set D : ℝ := ((dF + dG : ℕ) : ℝ) with hDdef
    set a := D / Real.log 2 with ha
    have ha1 : 1 ≤ a := by rw [ha, le_div_iff₀ hl2]; linarith
    have hlog2a : 0 ≤ Real.log (2 * a) := Real.log_nonneg (by linarith)
    have hpa : 0 ≤ a * Real.log (2 * a) := mul_nonneg (by linarith) hlog2a
    have hdGr : (0 : ℝ) ≤ dG := by positivity
    have hdFr : (0 : ℝ) ≤ dF := by positivity
    have hb : 0 ≤ (D + dG * Real.log k) / Real.log 2 := by
      apply div_nonneg _ hl2.le
      nlinarith
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp only [Nat.cast_zero]; nlinarith
    · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hcast : (2 : ℝ) ^ N ≤ ((N : ℝ) * k + 1) ^ dG * ((N : ℝ) + 1) ^ dF := by
        exact_mod_cast h
      have hlog := Real.log_le_log (by positivity) hcast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_pow] at hlog
      have hA : Real.log ((N : ℝ) * k + 1) ≤ 1 + Real.log k + Real.log N := by
        have h1 : (N : ℝ) * k + 1 ≤ 2 * ((k : ℝ) * N) := by nlinarith
        calc Real.log ((N : ℝ) * k + 1) ≤ Real.log (2 * ((k : ℝ) * N)) :=
              Real.log_le_log (by positivity) h1
          _ = Real.log 2 + Real.log k + Real.log N := by
              rw [Real.log_mul (by norm_num) (by positivity),
                Real.log_mul (by positivity) (by positivity)]; ring
          _ ≤ _ := by linarith
      have hB : Real.log ((N : ℝ) + 1) ≤ 1 + Real.log N := by
        have h1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
        calc Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) :=
              Real.log_le_log (by positivity) h1
          _ = Real.log 2 + Real.log N := by
              rw [Real.log_mul (by norm_num) (by positivity)]
          _ ≤ _ := by linarith
      have key : (N : ℝ) * Real.log 2 ≤ D + dG * Real.log k + D * Real.log N := by
        rw [hDsum]
        nlinarith [mul_le_mul_of_nonneg_left hA hdGr, mul_le_mul_of_nonneg_left hB hdFr]
      have h2a : 0 < 2 * a := by linarith
      have hln : Real.log N ≤ N / (2 * a) + Real.log (2 * a) - 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / (2 * a) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at this
        linarith
      have k1 : (N : ℝ) ≤ (D + dG * Real.log k + D * Real.log N) / Real.log 2 := by
        rw [le_div_iff₀ hl2]; linarith
      have e1 : (D + dG * Real.log k + D * Real.log N) / Real.log 2
          = (D + dG * Real.log k) / Real.log 2 + a * Real.log N := by
        rw [ha]; ring
      have hmul := mul_le_mul_of_nonneg_left hln (by linarith : (0 : ℝ) ≤ a)
      have e2 : a * ((N : ℝ) / (2 * a) + Real.log (2 * a) - 1)
          = (N : ℝ) / 2 + a * Real.log (2 * a) - a := by
        field_simp
      rw [e1] at k1
      nlinarith
end BalcanP33

open BalcanDDA.Piecewise FoundationsML.Regression FoundationsML.RademacherVC in
theorem solution {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ))
    (G : Set (↥U → Bool)) (k dF dG : ℕ)
    (hk : 1 ≤ k)
    (hdec : PiecewiseDecomposable (dual U) F G k)
    (hF : PseudoDim (dual F) dF) (hG : HasVCDim (dualB G) dG) :
    ∀ (N : ℕ) (x : Fin N → X), Shatters U x →
      (N : ℝ) ≤ 4 * (((dF + dG : ℕ) : ℝ) / Real.log 2) *
          Real.log (2 * (((dF + dG : ℕ) : ℝ) / Real.log 2)) +
        2 * ((((dF + dG : ℕ) : ℝ) + (dG : ℝ) * Real.log k) / Real.log 2) := by
  intro N x hx
  exact BalcanP33.analytic k dF dG N hk (BalcanP33.count_bound U F G k dF dG hdec hF hG N x hx)
