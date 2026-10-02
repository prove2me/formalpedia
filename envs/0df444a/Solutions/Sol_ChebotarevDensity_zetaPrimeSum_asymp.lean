-- Prove2me | solution 1 for ChebotarevDensity.zetaPrimeSum_asymp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:28:08.261635+00:00
-- url     : https://prove2.me/submissions/7cf86229-ec87-45ff-96d2-67e4c80d1707

import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField
open IsDedekindDomain
open scoped Classical

set_option linter.unusedSectionVars false

section
variable {L : Type*} [Field L] [NumberField L]

private noncomputable def PhiI (F : Finset (HeightOneSpectrum (𝓞 L))) (e : F → ℕ) : Ideal (𝓞 L) :=
  ∏ v : F, (v : HeightOneSpectrum (𝓞 L)).asIdeal ^ e v

private lemma PhiI_ne_bot (F : Finset (HeightOneSpectrum (𝓞 L))) (e : F → ℕ) : PhiI F e ≠ ⊥ := by
  unfold PhiI
  show _ ≠ (0 : Ideal (𝓞 L))
  rw [Finset.prod_ne_zero_iff]
  intro v _
  exact pow_ne_zero _ (v : HeightOneSpectrum (𝓞 L)).ne_bot

private lemma normalizedFactors_finset_prod_count {ι : Type*} (s : Finset ι) (f : ι → Ideal (𝓞 L))
    (hf : ∀ i ∈ s, f i ≠ 0) (w : Ideal (𝓞 L)) :
    Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ s, f i)) =
      ∑ i ∈ s, Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, UniqueFactorizationMonoid.normalizedFactors_one]; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      UniqueFactorizationMonoid.normalizedFactors_mul (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      Multiset.count_add, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma PhiI_count (F : Finset (HeightOneSpectrum (𝓞 L))) (e : F → ℕ) (w : F) :
    Multiset.count (w : HeightOneSpectrum (𝓞 L)).asIdeal
      (UniqueFactorizationMonoid.normalizedFactors (PhiI F e)) = e w := by
  classical
  unfold PhiI
  rw [normalizedFactors_finset_prod_count (Finset.univ : Finset F) (fun v : F => (v : HeightOneSpectrum (𝓞 L)).asIdeal ^ e v) (fun v _ => pow_ne_zero _ (v : HeightOneSpectrum (𝓞 L)).ne_bot)]
  have : ∀ v : F, Multiset.count (w : HeightOneSpectrum (𝓞 L)).asIdeal
      (UniqueFactorizationMonoid.normalizedFactors ((v : HeightOneSpectrum (𝓞 L)).asIdeal ^ e v))
      = if v = w then e v else 0 := by
    intro v
    rw [(HeightOneSpectrum.irreducible (v : HeightOneSpectrum (𝓞 L))).normalizedFactors_pow,
      normalize_eq, Multiset.count_replicate]
    congr 1
    apply propext
    constructor
    · intro h; exact Subtype.ext (HeightOneSpectrum.ext h)
    · intro h; rw [h]
  simp_rw [this]
  simp

private lemma PhiI_injective (F : Finset (HeightOneSpectrum (𝓞 L))) : Function.Injective (PhiI F) := by
  intro e e' h
  funext w
  rw [← PhiI_count F e w, ← PhiI_count F e' w, h]

private lemma absNorm_PhiI (F : Finset (HeightOneSpectrum (𝓞 L))) (e : F → ℕ) :
    Ideal.absNorm (PhiI F e) = ∏ v : F, Ideal.absNorm (v : HeightOneSpectrum (𝓞 L)).asIdeal ^ e v := by
  unfold PhiI
  simp [map_prod]

private lemma two_le_absNorm (v : HeightOneSpectrum (𝓞 L)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private lemma PhiI_surj (F : Finset (HeightOneSpectrum (𝓞 L))) (I : Ideal (𝓞 L)) (hI : I ≠ ⊥)
    (hF : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ I → v ∈ F) : ∃ e, PhiI F e = I := by
  classical
  refine ⟨fun v => multiplicity (v : HeightOneSpectrum (𝓞 L)).asIdeal I, ?_⟩
  have h := Ideal.finprod_heightOneSpectrum_pow_multiplicity hI
  unfold PhiI
  rw [Finset.prod_coe_sort F (fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal ^ multiplicity v.asIdeal I),
    ← finprod_eq_prod_of_mulSupport_subset _ (s := F), h]
  intro v hv
  by_contra hvF
  apply hv
  have : ¬ v.asIdeal ∣ I := fun hd => hvF (hF v hd)
  simp [multiplicity_eq_zero.mpr this]

private lemma PhiI_bound (F : Finset (HeightOneSpectrum (𝓞 L))) (e : F → ℕ) (w : F) :
    e w < Ideal.absNorm (PhiI F e) := by
  rw [absNorm_PhiI]
  calc e w < 2 ^ e w := Nat.lt_two_pow_self
    _ ≤ Ideal.absNorm (w : HeightOneSpectrum (𝓞 L)).asIdeal ^ e w :=
        Nat.pow_le_pow_left (two_le_absNorm _) _
    _ ≤ _ := Finset.single_le_prod' (f := fun v : F => Ideal.absNorm (v : HeightOneSpectrum (𝓞 L)).asIdeal ^ e v)
        (fun v _ => Nat.one_le_pow _ _ (by have := two_le_absNorm (v : HeightOneSpectrum (𝓞 L)); omega))
        (Finset.mem_univ w)

private noncomputable def zetaR (L : Type*) [Field L] [NumberField L] (s : ℝ) : ℝ :=
  ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)

private noncomputable def xs (s : ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℝ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)

private lemma term_PhiI (s : ℝ) (F : Finset (HeightOneSpectrum (𝓞 L))) (e : F → ℕ) :
    ((Ideal.absNorm (PhiI F e) : ℕ) : ℝ) ^ (-s) =
      ∏ v : F, xs s (v : HeightOneSpectrum (𝓞 L)) ^ e v := by
  unfold xs
  rw [absNorm_PhiI, Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
    Real.rpow_mul_natCast (by positivity)]

private lemma sum_box (s : ℝ) (F : Finset (HeightOneSpectrum (𝓞 L))) (K : ℕ) :
    ∑ e ∈ Fintype.piFinset (fun _ : F => Finset.range K), ((Ideal.absNorm (PhiI F e) : ℕ) : ℝ) ^ (-s) =
      ∏ v : F, ∑ j ∈ Finset.range K, xs s (v : HeightOneSpectrum (𝓞 L)) ^ j := by
  classical
  rw [Finset.prod_univ_sum (fun _ : F => Finset.range K)
    (fun (v : F) (j : ℕ) => xs s (v : HeightOneSpectrum (𝓞 L)) ^ j)]
  exact Finset.sum_congr rfl fun e _ => term_PhiI s F e

private lemma finite_primes_le (M : ℕ) :
    {v : HeightOneSpectrum (𝓞 L) | Ideal.absNorm v.asIdeal ≤ M}.Finite := by
  refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).preimage ?_)
  intro a _ b _ h
  exact HeightOneSpectrum.ext h

private lemma partial_sum_eq (s : ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) =
      ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset,
        ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset)
    (t := Finset.range (M + 1)) (g := fun I => Ideal.absNorm I)
    (fun I hI => by simpa [Nat.lt_succ_iff] using hI)]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have : ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset with Ideal.absNorm I = n,
      ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) = ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset with Ideal.absNorm I = n, (n : ℝ) ^ (-s) :=
    Finset.sum_congr rfl fun I hI => by rw [(Finset.mem_filter.mp hI).2]
  rw [this, Finset.sum_const, nsmul_eq_mul]
  congr 2
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 L) n
  have e1 : ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset.filter fun I => Ideal.absNorm I = n) = hfin.toFinset := by
    ext I
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hn', h⟩⟩
  rw [e1]
  exact (Nat.card_eq_card_finite_toFinset hfin)


private lemma xs_pos (s : ℝ) (v : HeightOneSpectrum (𝓞 L)) : 0 < xs s v := by
  unfold xs
  have := two_le_absNorm v
  have : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by positivity
  positivity

private lemma xs_le_half (s : ℝ) (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 L)) : xs s v ≤ 1 / 2 := by
  unfold xs
  have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm v
  calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

private lemma xs_sq_le (s : ℝ) (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 L)) : xs s v ^ 2 ≤ xs 2 v := by
  unfold xs
  have h2 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by have := two_le_absNorm v; omega : 1 ≤ Ideal.absNorm v.asIdeal)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le h2
  push_cast
  linarith

private lemma exp_le_inv_sub {x : ℝ} (h1 : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have := Real.add_one_le_exp (-x)
  calc Real.exp x = (Real.exp (-x))⁻¹ := by rw [Real.exp_neg, inv_inv]
    _ ≤ (1 - x)⁻¹ := inv_anti₀ (by linarith) (by linarith)

private lemma inv_sub_le_exp {x : ℝ} (h1 : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (x + 2 * x ^ 2) := by
  have hpos : 0 < 1 - x := by linarith
  have h2 : (1 - x)⁻¹ = 1 + x / (1 - x) := by field_simp; ring
  have h3 : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0:ℝ) ≤ 1 - 2 * x)]
  calc (1 - x)⁻¹ = x / (1 - x) + 1 := by rw [h2]; ring
    _ ≤ Real.exp (x / (1 - x)) := Real.add_one_le_exp _
    _ ≤ _ := Real.exp_le_exp.mpr h3

private lemma zetaR_nonneg_term (s : ℝ) (n : ℕ) :
    0 ≤ (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by positivity

private lemma sum_le_zetaR (s : ℝ)
    (hsum : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s))
    (T : Finset (Ideal (𝓞 L))) :
    ∑ I ∈ T, ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) ≤ zetaR L s := by
  set M := ∑ I ∈ T, Ideal.absNorm I with hM
  have hsub : T ⊆ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset := by
    intro I hI
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Finset.single_le_sum (f := fun I => Ideal.absNorm I) (fun _ _ => Nat.zero_le _) hI
  calc ∑ I ∈ T, ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s)
      ≤ ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset, ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ n ∈ Finset.range (M + 1), (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) :=
        (partial_sum_eq s M).symm
    _ ≤ zetaR L s := hsum.sum_le_tsum _ (fun n _ => zetaR_nonneg_term s n)

private lemma prod_geom_le_zetaR (s : ℝ)
    (hsum : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s))
    (F : Finset (HeightOneSpectrum (𝓞 L))) (K : ℕ) :
    ∏ v : F, ∑ j ∈ Finset.range K, (xs s (v : HeightOneSpectrum (𝓞 L))) ^ j ≤ zetaR L s := by
  rw [← sum_box s F K]
  rw [← Finset.sum_image (f := fun I : Ideal (𝓞 L) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s))
    (s := Fintype.piFinset (fun _ : F => Finset.range K)) (g := PhiI F)
    (fun a _ b _ h => PhiI_injective F h)]
  exact sum_le_zetaR s hsum _

private lemma sum_xs_le_log (s : ℝ) (hs : 1 ≤ s)
    (hsum : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s))
    (F : Finset (HeightOneSpectrum (𝓞 L))) :
    Real.exp (∑ v ∈ F, xs s v) ≤ zetaR L s := by
  have h1 : ∏ v : F, (1 - xs s (v : HeightOneSpectrum (𝓞 L)))⁻¹ ≤ zetaR L s := by
    have ht : Filter.Tendsto (fun K : ℕ => ∏ v : F, ∑ j ∈ Finset.range K, (xs s (v : HeightOneSpectrum (𝓞 L))) ^ j)
        Filter.atTop (nhds (∏ v : F, (1 - xs s (v : HeightOneSpectrum (𝓞 L)))⁻¹)) := by
      refine tendsto_finsetProd _ (fun v _ => ?_)
      have hx0 := xs_pos s (v : HeightOneSpectrum (𝓞 L))
      have hx1 : xs s (v : HeightOneSpectrum (𝓞 L)) < 1 := by
        linarith [xs_le_half s hs (v : HeightOneSpectrum (𝓞 L))]
      exact (hasSum_geometric_of_lt_one hx0.le hx1).tendsto_sum_nat
    exact le_of_tendsto' ht (fun K => prod_geom_le_zetaR s hsum F K)
  refine le_trans ?_ h1
  rw [← Finset.sum_coe_sort F, Real.exp_sum]
  refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun v _ => ?_
  exact exp_le_inv_sub (by linarith [xs_le_half s hs (v : HeightOneSpectrum (𝓞 L))])


private lemma partial_le (s : ℝ) (hs : 1 ≤ s) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) ≤
      ∏ v : (finite_primes_le (L := L) M).toFinset, (1 - xs s (v : HeightOneSpectrum (𝓞 L)))⁻¹ := by
  rw [partial_sum_eq]
  set F := (finite_primes_le (L := L) M).toFinset with hF
  have hnz : ∀ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset,
      ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) ≠ 0 → I ∈ Finset.image (PhiI F) (Fintype.piFinset (fun _ : F => Finset.range (M + 1))) := by
    intro I hI hne
    have hIM : Ideal.absNorm I ≤ M := by simpa using hI
    have hI0 : I ≠ ⊥ := by
      rintro rfl
      exact hne (by rw [Ideal.absNorm_bot, Nat.cast_zero, Real.zero_rpow (by linarith)])
    have hN0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨e, he⟩ := PhiI_surj F I hI0 (fun v hv => by
      have h1 : Ideal.absNorm v.asIdeal ∣ Ideal.absNorm I := map_dvd _ hv
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) h1
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      omega)
    refine Finset.mem_image.mpr ⟨e, ?_, he⟩
    rw [Fintype.mem_piFinset]
    intro w
    rw [Finset.mem_range]
    have := PhiI_bound F e w
    rw [he] at this
    omega
  calc ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset, ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s)
      = ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) M).toFinset with ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) ≠ 0, ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ I ∈ Finset.image (PhiI F) (Fintype.piFinset (fun _ : F => Finset.range (M + 1))), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun I hI => hnz I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2)
          (fun _ _ _ => by positivity)
    _ = ∑ e ∈ Fintype.piFinset (fun _ : F => Finset.range (M + 1)), ((Ideal.absNorm (PhiI F e) : ℕ) : ℝ) ^ (-s) :=
        Finset.sum_image (fun a _ b _ h => PhiI_injective F h)
    _ = _ := sum_box s F (M + 1)
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun v _ => Finset.sum_nonneg fun j _ =>
        pow_nonneg (xs_pos s (v : HeightOneSpectrum (𝓞 L))).le j) fun v _ => ?_
      have hx0 := xs_pos s (v : HeightOneSpectrum (𝓞 L))
      have hx1 : xs s (v : HeightOneSpectrum (𝓞 L)) < 1 := by
        linarith [xs_le_half s hs (v : HeightOneSpectrum (𝓞 L))]
      have hg := hasSum_geometric_of_lt_one hx0.le hx1
      rw [← hg.tsum_eq]
      exact hg.summable.sum_le_tsum _ (fun j _ => pow_nonneg hx0.le j)


private lemma one_le_zetaR (s : ℝ) (hs : 1 ≤ s)
    (hsum : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) :
    1 ≤ zetaR L s := by
  simpa using sum_xs_le_log s hs hsum ∅

private lemma summable_xs (s : ℝ) (hs : 1 ≤ s)
    (hsum : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) :
    Summable (xs (L := L) s) ∧ ∑' v, xs (L := L) s v ≤ Real.log (zetaR L s) := by
  have hz := one_le_zetaR s hs hsum
  have hle : ∀ F : Finset (HeightOneSpectrum (𝓞 L)), ∑ v ∈ F, xs (L := L) s v ≤ Real.log (zetaR L s) := fun F =>
    (Real.le_log_iff_exp_le (by linarith)).mpr (sum_xs_le_log s hs hsum F)
  have hsm : Summable (xs (L := L) s) := summable_of_sum_le (fun v => (xs_pos s v).le) hle
  exact ⟨hsm, hsm.tsum_le_of_sum_le hle⟩

private lemma log_zetaR_le (s : ℝ) (hs : 1 ≤ s)
    (hsum : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s))
    (hsum2 : Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :
    Real.log (zetaR L s) ≤ ∑' v, xs (L := L) s v + 2 * ∑' v, xs (L := L) 2 v := by
  have hz := one_le_zetaR s hs hsum
  obtain ⟨hx, -⟩ := summable_xs s hs hsum
  obtain ⟨hy, -⟩ := summable_xs 2 (by norm_num) hsum2
  rw [Real.log_le_iff_le_exp (by linarith)]
  unfold zetaR
  refine Summable.tsum_le_of_sum_range_le hsum fun n => ?_
  have h1 : ∑ i ∈ Finset.range n, (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = i} : ℝ) * (i : ℝ) ^ (-s) ≤
      ∑ i ∈ Finset.range (n + 1), (Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = i} : ℝ) * (i : ℝ) ^ (-s) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ n))
      (fun i _ _ => zetaR_nonneg_term s i)
  refine h1.trans ((partial_le s hs n).trans ?_)
  set F := (finite_primes_le (L := L) n).toFinset
  calc ∏ v : F, (1 - xs s (v : HeightOneSpectrum (𝓞 L)))⁻¹
      ≤ ∏ v : F, Real.exp (xs s (v : HeightOneSpectrum (𝓞 L)) + 2 * xs 2 (v : HeightOneSpectrum (𝓞 L))) := by
        refine Finset.prod_le_prod (fun v _ => by
          have := xs_le_half s hs (v : HeightOneSpectrum (𝓞 L)); have := xs_pos s (v : HeightOneSpectrum (𝓞 L))
          have : 0 < 1 - xs s (v : HeightOneSpectrum (𝓞 L)) := by linarith
          positivity) fun v _ => ?_
        refine (inv_sub_le_exp (xs_le_half s hs _)).trans (Real.exp_le_exp.mpr ?_)
        have := xs_sq_le s hs (v : HeightOneSpectrum (𝓞 L))
        linarith
    _ = Real.exp (∑ v ∈ F, (xs (L := L) s v + 2 * xs 2 v)) := by
        rw [← Finset.sum_coe_sort F, Real.exp_sum]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have h1 := hx.sum_le_tsum F (fun v _ => (xs_pos s v).le)
        have h2 := hy.sum_le_tsum F (fun v _ => (xs_pos 2 v).le)
        linarith

end

section analytic
open Filter Topology Finset Ideal Asymptotics
variable (L : Type*) [Field L] [NumberField L]

private lemma hlim_aux :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 L) // absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue L)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ L).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 L) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private lemma lseries_summable (s : ℝ) (hs : 1 < s) :
    LSeriesSummable (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 L) // absNorm I = n} : ℕ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (Nat.card {I : Ideal (𝓞 L) // absNorm I = n} : ℝ)) ?_ (fun _ => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim_aux L)

private lemma real_summable (s : ℝ) (hs : 1 < s) :
    Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 L) // absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  have h := (lseries_summable L s hs)
  have h2 : Summable fun n => ‖LSeries.term (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 L) // absNorm I = n} : ℕ) : ℂ)) s n‖ :=
    summable_norm_iff.mpr h
  refine h2.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  · simp [hn.ne', Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

private lemma dedekindZeta_ofReal (s : ℝ) (hs : 0 < s) :
    dedekindZeta L (s : ℂ) = ((zetaR L s : ℝ) : ℂ) := by
  unfold dedekindZeta zetaR LSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (by linarith : -s ≠ 0)]
  · simp only [LSeries.term, hn.ne', if_false]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
      Complex.cpow_neg, div_eq_mul_inv]

end analytic

theorem solution (L : Type) [Field L] [NumberField L] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      |(∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
          (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) - Real.log (1 / (s - 1))| ≤ C := by
  set ρ := dedekindZeta_residue L with hρdef
  have hρ : 0 < ρ := dedekindZeta_residue_pos L
  have h := tendsto_sub_one_mul_dedekindZeta_nhdsGT L
  have h' := (Complex.continuous_re.tendsto _).comp h
  have ht : Filter.Tendsto (fun s : ℝ => (s - 1) * zetaR L s) (nhdsWithin 1 (Set.Ioi 1)) (nhds ρ) := by
    refine (h'.congr' ?_).trans_eq (by simp [hρdef])
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := by have : (1 : ℝ) < s := hs; linarith
    simp only [Function.comp_apply]
    rw [dedekindZeta_ofReal L s hs']
    have : ((s : ℂ) - 1) * ((zetaR L s : ℝ) : ℂ) = (((s - 1) * zetaR L s : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  have hlog := (Real.continuousAt_log hρ.ne').tendsto.comp ht
  have hev := Metric.tendsto_nhds.mp hlog 1 one_pos
  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := Ioo_mem_nhdsGT (by norm_num)
  refine ⟨|Real.log ρ| + 1 + 2 * ∑' v, xs (L := L) 2 v, ?_⟩
  filter_upwards [hev, hIoo] with s hs1 hs2
  obtain ⟨hsa, hsb⟩ := hs2
  have hsum := real_summable L s hsa
  have hsum2 := real_summable L 2 (by norm_num)
  obtain ⟨-, hlow⟩ := summable_xs s hsa.le hsum
  have hup := log_zetaR_le s hsa.le hsum hsum2
  have hz := one_le_zetaR s hsa.le hsum
  have hS2 : 0 ≤ ∑' v, xs (L := L) 2 v := tsum_nonneg fun v => (xs_pos 2 v).le
  have hs1' : |Real.log ((s - 1) * zetaR L s) - Real.log ρ| < 1 := by
    simpa [Real.dist_eq] using hs1
  have hsm1 : s - 1 ≠ 0 := by linarith
  rw [Real.log_mul hsm1 (by linarith)] at hs1'
  have hl : Real.log (1 / (s - 1)) = - Real.log (s - 1) := by rw [one_div, Real.log_inv]
  show |(∑' v, xs (L := L) s v) - Real.log (1 / (s - 1))| ≤ _
  rw [hl]
  rw [abs_lt] at hs1'
  have habs := abs_nonneg (Real.log ρ)
  have h1 := le_abs_self (Real.log ρ)
  have h2 := neg_abs_le (Real.log ρ)
  rw [abs_le]
  constructor <;> linarith [hs1'.1, hs1'.2]
