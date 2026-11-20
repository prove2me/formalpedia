-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.Supplement.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:01:48.370098+00:00
-- url     : https://prove2.me/submissions/f0f89272-14e2-4c4a-a83e-83622b4db74d

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_Connectivity

section
namespace BinarySketchTruncation.Dev.Lemma3
open BinarySketchTruncation.Opposite BinarySketchTruncation.Opposite.Supplement

def sg (x : Bit) : ℝ := if x = 0 then 1 else -1

lemma bit_cases (x : Bit) : x = 0 ∨ x = 1 := by revert x; decide

lemma one_ne_zero_bit : (1 : Bit) ≠ 0 := by decide

lemma one_add_one_bit : (1 : Bit) + 1 = 0 := by decide

lemma sum_bit (g : Bit → ℝ) : ∑ x : Bit, g x = g 0 + g 1 := by
  have : (Finset.univ : Finset Bit) = {0, 1} := by decide
  rw [this, Finset.sum_pair (Ne.symm one_ne_zero_bit)]

lemma sg_zero : sg 0 = 1 := by simp [sg]
lemma sg_one : sg 1 = -1 := by simp [sg, one_ne_zero_bit]

lemma sg_add (x y : Bit) : sg (x + y) = sg x * sg y := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    simp [sg_zero, sg_one, one_add_one_bit]

lemma sg_sq (x : Bit) : sg x * sg x = 1 := by
  rcases bit_cases x with rfl | rfl <;> simp [sg_zero, sg_one]

lemma sg_ne (x y : Bit) (h : x ≠ y) : sg x * sg y = -1 := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    simp_all [sg_zero, sg_one]

section general
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def chi (J : Finset ι) (z : ι → Bit) : ℝ := ∏ l, if l ∈ J then sg (z l) else 1

lemma sum_prod (g : ι → Bit → ℝ) : ∑ z : ι → Bit, ∏ l, g l (z l) = ∏ l, ∑ x : Bit, g l x := by
  have := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bit)) g
  rw [this, Fintype.piFinset_univ]

lemma card_pi : (Fintype.card (ι → Bit) : ℝ) = 2 ^ Fintype.card ι := by
  simp

lemma orth (J K : Finset ι) :
    ∑ z : ι → Bit, chi J z * chi K z = if J = K then (2 : ℝ) ^ Fintype.card ι else 0 := by
  unfold chi
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod (fun l x => (if l ∈ J then sg x else 1) * (if l ∈ K then sg x else 1))]
  have key : ∀ l, ∑ x : Bit, ((if l ∈ J then sg x else 1) * (if l ∈ K then sg x else 1)) =
      if (l ∈ J ↔ l ∈ K) then 2 else 0 := by
    intro l
    by_cases h1 : l ∈ J <;> by_cases h2 : l ∈ K <;>
      simp [h1, h2, sum_bit, sg_zero, sg_one] <;> norm_num
  simp_rw [key]
  by_cases h : J = K
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨l, hl⟩ : ∃ l, ¬ (l ∈ J ↔ l ∈ K) := by
      by_contra hc; push Not at hc; exact h (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])

lemma chi_empty (z : ι → Bit) : chi (∅ : Finset ι) z = 1 := by simp [chi]

lemma sum_chi_pair (w z : ι → Bit) :
    ∑ J : Finset ι, chi J w * chi J z = if w = z then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have h1 : ∀ J : Finset ι, chi J w * chi J z = ∏ l ∈ J, (sg (w l) * sg (z l)) := by
    intro J
    unfold chi
    rw [← Finset.prod_mul_distrib]
    calc (∏ x, (if x ∈ J then sg (w x) else 1) * if x ∈ J then sg (z x) else 1)
        = ∏ l, if l ∈ J then sg (w l) * sg (z l) else 1 := by
          apply Finset.prod_congr rfl
          intro l _
          by_cases h : l ∈ J <;> simp [h]
      _ = ∏ l ∈ Finset.univ ∩ J, sg (w l) * sg (z l) :=
          Finset.prod_ite_mem Finset.univ J (fun l => sg (w l) * sg (z l))
      _ = _ := by rw [Finset.univ_inter]
  simp_rw [h1]
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  by_cases h : w = z
  · subst h
    rw [if_pos rfl]
    have : ∀ l ∈ (Finset.univ : Finset ι), (1 + sg (w l) * sg (w l)) = 2 := by
      intro l _; rw [sg_sq]; norm_num
    rw [Finset.prod_congr rfl this]
    simp
  · rw [if_neg h]
    obtain ⟨l, hl⟩ : ∃ l, w l ≠ z l := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [sg_ne _ _ hl]; norm_num)

/-- Walsh coefficient. -/
noncomputable def fh (f : (ι → Bit) → ℝ) (J : Finset ι) : ℝ :=
  (∑ w, f w * chi J w) / 2 ^ Fintype.card ι

lemma two_pow_pos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity

lemma inversion (f : (ι → Bit) → ℝ) (z : ι → Bit) : f z = ∑ J, fh f J * chi J z := by
  have h1 : ∀ J : Finset ι, fh f J * chi J z =
      (∑ w, f w * (chi J w * chi J z)) / 2 ^ Fintype.card ι := by
    intro J
    unfold fh
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intros; ring
  simp_rw [h1]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_chi_pair]
  simp [mul_ite]

lemma mean_expand (c : Finset ι → ℝ) (g : (ι → Bit) → ℝ)
    (hg : ∀ z, g z = ∑ J, c J * chi J z) :
    uniformMean g = c ∅ := by
  unfold uniformMean
  have h1 : ∑ z, g z = c ∅ * 2 ^ Fintype.card ι := by
    simp_rw [hg]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have : ∀ J : Finset ι, ∑ z : ι → Bit, chi J z = if J = ∅ then (2:ℝ) ^ Fintype.card ι else 0 := by
      intro J
      have := orth J ∅
      simpa [chi_empty] using this
    simp_rw [this]
    simp [mul_ite]
  rw [h1, card_pi]
  field_simp

lemma var_expand (c : Finset ι → ℝ) (g : (ι → Bit) → ℝ)
    (hg : ∀ z, g z = ∑ J, c J * chi J z) :
    uniformVariance g = ∑ J, c J ^ 2 - c ∅ ^ 2 := by
  have hmean := mean_expand c g hg
  have hcard : (Fintype.card (ι → Bit) : ℝ) = 2 ^ Fintype.card ι := card_pi
  have hpos := two_pow_pos (ι := ι)
  unfold uniformVariance
  rw [hmean]
  unfold uniformMean at hmean ⊢
  have hS : ∑ z, g z = c ∅ * 2 ^ Fintype.card ι := by
    rw [hcard] at hmean
    exact (div_eq_iff hpos.ne').mp hmean
  have hsq : ∑ z, g z ^ 2 = (∑ J, c J ^ 2) * 2 ^ Fintype.card ι := by
    have h2 : ∀ z, g z ^ 2 = ∑ J, ∑ K, (c J * c K) * (chi J z * chi K z) := by
      intro z
      rw [sq, hg z, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro J _
      apply Finset.sum_congr rfl; intro K _
      ring
    simp_rw [h2]
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro J _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, orth]
    simp [mul_ite]
    ring
  have hexp : ∑ z, (g z - c ∅) ^ 2 =
      ∑ z, g z ^ 2 - 2 * c ∅ * ∑ z, g z + Fintype.card (ι → Bit) * c ∅ ^ 2 := by
    have : ∀ z, (g z - c ∅) ^ 2 = g z ^ 2 - 2 * c ∅ * g z + c ∅ ^ 2 := by intro z; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  rw [hexp, hsq, hS, hcard]
  field_simp
  ring

lemma bit_two (x : Bit) : x + x = 0 := by revert x; decide

lemma mem_fiber (I : Finset ι) (z w : ι → Bit) :
    w ∈ coordinateFiber I z ↔ ∀ i ∈ I, w i = z i := by
  unfold coordinateFiber
  simp

lemma fiber_card_pos (I : Finset ι) (z : ι → Bit) : 0 < (coordinateFiber I z).card :=
  Finset.card_pos.mpr ⟨z, (mem_fiber I z z).mpr (fun _ _ => rfl)⟩

lemma chi_flip (K : Finset ι) (l : ι) (hl : l ∈ K) (w : ι → Bit) :
    chi K (w + Pi.single l 1) = - chi K w := by
  unfold chi
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun k => if k ∈ K then sg (w k) else 1)
      (Finset.mem_univ l)]
  have : ∏ k ∈ Finset.univ.erase l, (if k ∈ K then sg (((w + Pi.single l 1 : ι → Bit)) k) else 1) =
      ∏ k ∈ Finset.univ.erase l, (if k ∈ K then sg (w k) else 1) := by
    apply Finset.prod_congr rfl
    intro k hk
    have : k ≠ l := Finset.ne_of_mem_erase hk
    simp [Pi.single_eq_of_ne this]
  rw [this]
  simp [hl, sg_add, sg_one]

lemma fiber_sum_chi (K I : Finset ι) (z : ι → Bit) :
    ∑ w ∈ coordinateFiber I z, chi K w =
      if K ⊆ I then ((coordinateFiber I z).card : ℝ) * chi K z else 0 := by
  by_cases hK : K ⊆ I
  · rw [if_pos hK]
    rw [Finset.sum_congr rfl (g := fun _ => chi K z)]
    · simp
    · intro w hw
      rw [mem_fiber] at hw
      unfold chi
      apply Finset.prod_congr rfl
      intro l _
      by_cases h : l ∈ K
      · simp [h, hw l (hK h)]
      · simp [h]
  · rw [if_neg hK]
    obtain ⟨l, hlK, hlI⟩ := Finset.not_subset.mp hK
    set e : ι → Bit := Pi.single l 1 with he
    have hee : ∀ w : ι → Bit, w + e + e = w := by
      intro w; funext k; simp [add_assoc, bit_two]
    have hmem : ∀ w ∈ coordinateFiber I z, w + e ∈ coordinateFiber I z := by
      intro w hw
      rw [mem_fiber] at hw ⊢
      intro i hi
      have : i ≠ l := fun h => hlI (h ▸ hi)
      simp [he, Pi.single_eq_of_ne this, hw i hi]
    have h1 : ∑ w ∈ coordinateFiber I z, chi K w = ∑ w ∈ coordinateFiber I z, chi K (w + e) := by
      apply Finset.sum_nbij' (fun w => w + e) (fun w => w + e) hmem hmem
      · intro w _; exact hee w
      · intro w _; exact hee w
      · intro w _; rw [hee]
    have h2 : ∑ w ∈ coordinateFiber I z, chi K (w + e) = - ∑ w ∈ coordinateFiber I z, chi K w := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun w _ => chi_flip K l hlK w)
    linarith

lemma condmean_expand (f : (ι → Bit) → ℝ) (I : Finset ι) (z : ι → Bit) :
    coordinateConditionalMean f I z =
      ∑ J, (if J ⊆ I then fh f J else 0) * chi J z := by
  unfold coordinateConditionalMean
  have hc : ((coordinateFiber I z).card : ℝ) ≠ 0 := by
    exact_mod_cast (fiber_card_pos I z).ne'
  rw [div_eq_iff hc]
  calc ∑ w ∈ coordinateFiber I z, f w
      = ∑ w ∈ coordinateFiber I z, ∑ K, fh f K * chi K w :=
        Finset.sum_congr rfl (fun w _ => inversion f w)
    _ = ∑ K, fh f K * ∑ w ∈ coordinateFiber I z, chi K w := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ K, fh f K * (if K ⊆ I then ((coordinateFiber I z).card : ℝ) * chi K z else 0) := by
        simp_rw [fiber_sum_chi]
    _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro K _
        by_cases h : K ⊆ I <;> simp [h]; ring

lemma chi_map (π : Equiv.Perm ι) (J : Finset ι) (w : ι → Bit) :
    chi (J.map π.toEmbedding) w = chi J (fun k => w (π k)) := by
  unfold chi
  rw [← Equiv.prod_comp π]
  apply Finset.prod_congr rfl
  intro k _
  simp [Finset.mem_map_equiv]

lemma fh_perm (f : (ι → Bit) → ℝ) (π : Equiv.Perm ι)
    (hf : ∀ z, f (fun k => z (π k)) = f z) (J : Finset ι) :
    fh f (J.map π.toEmbedding) = fh f J := by
  unfold fh
  congr 1
  let e : (ι → Bit) ≃ (ι → Bit) := Equiv.arrowCongr π (Equiv.refl Bit)
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro u _
  have he : e u = fun k => u (π.symm k) := by
    funext k; simp [e, Equiv.arrowCongr]
  rw [he, chi_map]
  have h1 : (fun k => (fun k => u (π.symm k)) (π k)) = u := by funext k; simp
  rw [h1]
  have := hf (fun k => u (π.symm k))
  rw [h1] at this
  rw [this]

noncomputable def tt (f : (ι → Bit) → ℝ) (J : Finset ι) (l : ι) : ℝ :=
  if l ∈ J then fh f J ^ 2 / J.card else 0

noncomputable def av (f : (ι → Bit) → ℝ) (l : ι) : ℝ := ∑ J, tt f J l

lemma av_perm (f : (ι → Bit) → ℝ) (π : Equiv.Perm ι)
    (hf : ∀ z, f (fun k => z (π k)) = f z) (l : ι) : av f (π l) = av f l := by
  unfold av
  rw [← Equiv.sum_comp (Equiv.finsetCongr π) (fun J => tt f J (π l))]
  apply Finset.sum_congr rfl
  intro J _
  unfold tt
  rw [Equiv.finsetCongr_apply, fh_perm f π hf, Finset.card_map]
  simp [Finset.mem_map_equiv]

lemma tt_nonneg (f : (ι → Bit) → ℝ) (J : Finset ι) (l : ι) : 0 ≤ tt f J l := by
  unfold tt; split_ifs <;> positivity

lemma sum_tt_l (f : (ι → Bit) → ℝ) (J : Finset ι) :
    ∑ l, tt f J l = if J = ∅ then 0 else fh f J ^ 2 := by
  unfold tt
  rw [Finset.sum_ite_mem Finset.univ J, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  by_cases h : J = ∅
  · simp [h]
  · have : (J.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.nonempty_iff_ne_empty.mpr h).card_pos.ne'
    simp [h]
    field_simp

lemma var_eq_tot (c : Finset ι → ℝ) (g : (ι → Bit) → ℝ)
    (hg : ∀ z, g z = ∑ J, c J * chi J z) :
    uniformVariance g = ∑ J, (if J = ∅ then 0 else c J ^ 2) := by
  rw [var_expand c g hg]
  have : ∀ J : Finset ι, c J ^ 2 = (if J = ∅ then 0 else c J ^ 2) + (if J = ∅ then c ∅ ^ 2 else 0) := by
    intro J; by_cases h : J = ∅ <;> simp [h]
  conv_lhs => rw [Finset.sum_congr rfl (fun J _ => this J)]
  rw [Finset.sum_add_distrib]
  simp

theorem general (f : (ι → Bit) → ℝ)
    (hsym : ∀ l l' : ι, ∃ π : Equiv.Perm ι, π l = l' ∧ ∀ z, f (fun k => z (π k)) = f z)
    (I : Finset ι) :
    (Fintype.card ι : ℝ) * uniformVariance (coordinateConditionalMean f I) ≤
      I.card * uniformVariance f := by
  have hVf := var_eq_tot (fh f) f (inversion f)
  have hV := var_eq_tot (fun J => if J ⊆ I then fh f J else 0) (coordinateConditionalMean f I)
    (condmean_expand f I)
  by_cases hι : IsEmpty ι
  · have h0 : (Fintype.card ι : ℝ) = 0 := by simp
    rw [h0, zero_mul]
    apply mul_nonneg (by positivity)
    unfold uniformVariance uniformMean
    apply div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  · rw [not_isEmpty_iff] at hι
    obtain ⟨l0⟩ := hι
    have hav : ∀ l, av f l = av f l0 := by
      intro l
      obtain ⟨π, h1, h2⟩ := hsym l0 l
      rw [← h1, av_perm f π h2]
    have htot : ∑ l, av f l = uniformVariance f := by
      rw [hVf]
      unfold av
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun J _ => sum_tt_l f J)
    have hsumav : ∑ l, av f l = Fintype.card ι * av f l0 := by
      rw [Finset.sum_congr rfl (fun l _ => hav l)]
      simp
    have hVI : uniformVariance (coordinateConditionalMean f I) ≤ ∑ l ∈ I, av f l := by
      rw [hV]
      have h1 : ∀ J : Finset ι, (if J = ∅ then 0 else
          (if J ⊆ I then fh f J else 0) ^ 2) =
          ∑ l ∈ I, (if J ⊆ I then tt f J l else 0) := by
        intro J
        by_cases hJ : J ⊆ I
        · simp only [hJ, if_true]
          unfold tt
          rw [Finset.sum_ite_mem I J, Finset.inter_eq_right.mpr hJ, Finset.sum_const, nsmul_eq_mul]
          by_cases h : J = ∅
          · simp [h]
          · have : (J.card : ℝ) ≠ 0 := by
              exact_mod_cast (Finset.nonempty_iff_ne_empty.mpr h).card_pos.ne'
            simp [h]
            field_simp
        · simp [hJ]
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro l _
      unfold av
      apply Finset.sum_le_sum
      intro J _
      split_ifs
      · exact le_rfl
      · exact tt_nonneg f J l
    have hsum : ∑ l ∈ I, av f l = I.card * av f l0 := by
      rw [Finset.sum_congr rfl (fun l _ => hav l)]
      simp
    have hn : 0 ≤ (Fintype.card ι : ℝ) := by positivity
    calc (Fintype.card ι : ℝ) * uniformVariance (coordinateConditionalMean f I)
        ≤ Fintype.card ι * (I.card * av f l0) := by
          apply mul_le_mul_of_nonneg_left _ hn
          rw [← hsum]; exact hVI
      _ = I.card * (Fintype.card ι * av f l0) := by ring
      _ = I.card * uniformVariance f := by rw [← hsumav, htot]

end general
lemma connectivity_invariant {a b : ℕ} (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (z : (Fin a × Fin b) → Bit) :
    connectivityIndicator (fun k => z (Equiv.prodCongr σ τ k)) = connectivityIndicator z := by
  let φ : edgeGraph (fun k => z (Equiv.prodCongr σ τ k)) ≃g edgeGraph z :=
    { toEquiv := Equiv.sumCongr σ τ
      map_rel_iff' := by
        intro x y
        rcases x with i | j <;> rcases y with i' | j' <;> simp [edgeGraph] }
  have hiff := φ.connected_iff
  unfold connectivityIndicator connectivityBool
  classical
  have hd : decide (edgeGraph (fun k => z (Equiv.prodCongr σ τ k))).Connected =
      decide (edgeGraph z).Connected := decide_eq_decide.mpr hiff
  simp only [hd]

end BinarySketchTruncation.Dev.Lemma3

namespace BinarySketchTruncation.Opposite.Supplement

theorem chk_lemma_3 (a b : ℕ) (I : Finset (Fin a × Fin b)) :
    (a * b : ℕ) * uniformVariance
      (coordinateConditionalMean (connectivityIndicator (a := a) (b := b)) I) ≤
    (I.card : ℝ) * uniformVariance (connectivityIndicator (a := a) (b := b)) := by
  have h := BinarySketchTruncation.Dev.Lemma3.general
    (connectivityIndicator (a := a) (b := b)) (by
      intro l l'
      refine ⟨Equiv.prodCongr (Equiv.swap l.1 l'.1) (Equiv.swap l.2 l'.2), ?_, ?_⟩
      · ext <;> simp
      · intro z
        exact BinarySketchTruncation.Dev.Lemma3.connectivity_invariant _ _ z) I
  simpa [Fintype.card_prod] using h

end BinarySketchTruncation.Opposite.Supplement
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.Supplement.chk_lemma_3 := @BinarySketchTruncation.Opposite.Supplement.chk_lemma_3
