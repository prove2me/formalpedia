-- Prove2me | solution 1 for DeepONetUniversal.universal_approximation_operator_tw
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:40:31.09801+00:00
-- url     : https://prove2.me/submissions/7c168c76-9066-47c2-aa12-67cdaa0641ae

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic
import Theorems.Thm_DeepONetUniversal_universal_approximation_functional

open MeasureTheory Filter Topology DeepONetUniversal

-- Step 1: Stone-Weierstrass decomposition on V × K₂ into ∑_s f_s(u) * exp(w_s · y)
private lemma approx_by_separated_exp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {d : ℕ} (K₁ : Set X) (hK₁ : IsCompact K₁)
    (K₂ : Set (Fin d → ℝ)) (hK₂ : IsCompact K₂) (hK₂ne : K₂.Nonempty)
    (V : Set C(K₁, ℝ)) (hV : IsCompact V) (hVne : V.Nonempty)
    (G : C(K₁, ℝ) → C(K₂, ℝ)) (hG : ContinuousOn G V)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (S : ℕ) (fs : Fin S → C(↥V, ℝ)) (ws : Fin S → Fin d → ℝ),
      ∀ (u : ↥V) (y : ↥K₂),
        |G u.1 y - ∑ s : Fin S, fs s u * Real.exp (∑ l : Fin d, ws s l * y.1 l)| < δ := by
  have : CompactSpace ↥K₁ := isCompact_iff_compactSpace.mp hK₁
  have : CompactSpace ↥V := isCompact_iff_compactSpace.mp hV
  have : CompactSpace ↥K₂ := isCompact_iff_compactSpace.mp hK₂
  have : Nonempty ↥V := hVne.to_subtype
  have : Nonempty ↥K₂ := hK₂ne.to_subtype
  have hG_joint : Continuous (fun q : ↥V × ↥K₂ => G q.1.1 q.2) := by
    have h1 : Continuous (fun q : ↥V × ↥K₂ => (G q.1.1, q.2)) :=
      (hG.domRestrict.comp continuous_fst).prodMk continuous_snd
    exact continuous_eval.comp h1
  let gen (f : C(↥V, ℝ)) (w : Fin d → ℝ) : C(↥V × ↥K₂, ℝ) :=
    ⟨fun q => f q.1 * Real.exp (∑ l : Fin d, w l * q.2.1 l), by
      refine (f.continuous.comp continuous_fst).mul (Real.continuous_exp.comp ?_)
      refine continuous_finsetSum _ fun l _ => ?_
      exact continuous_const.mul
        ((continuous_apply l).comp (continuous_subtype_val.comp continuous_snd))⟩
  have hgen_one : gen 1 0 = 1 := by ext q; simp [gen]
  have hgen_mul : ∀ f₁ f₂ w₁ w₂, gen f₁ w₁ * gen f₂ w₂ = gen (f₁ * f₂) (w₁ + w₂) := by
    intro f₁ f₂ w₁ w₂
    ext q
    simp only [ContinuousMap.mul_apply, gen, ContinuousMap.coe_mk]
    calc f₁ q.1 * Real.exp (∑ l, w₁ l * q.2.1 l) * (f₂ q.1 * Real.exp (∑ l, w₂ l * q.2.1 l))
        = (f₁ q.1 * f₂ q.1) * (Real.exp (∑ l, w₁ l * q.2.1 l) * Real.exp (∑ l, w₂ l * q.2.1 l)) := by ring
      _ = (f₁ q.1 * f₂ q.1) * Real.exp (∑ l, (w₁ l + w₂ l) * q.2.1 l) := by
          rw [← Real.exp_add, ← Finset.sum_add_distrib]
          congr 2
          refine Finset.sum_congr rfl fun l _ => by ring
  let GenSet : Set C(↥V × ↥K₂, ℝ) := Set.range (fun p : C(↥V, ℝ) × (Fin d → ℝ) => gen p.1 p.2)
  let Sspan : Submodule ℝ C(↥V × ↥K₂, ℝ) := Submodule.span ℝ GenSet
  let A : Subalgebra ℝ C(↥V × ↥K₂, ℝ) :=
    { carrier := Sspan
      mul_mem' := by
        intro g₁ g₂ hg₁ hg₂
        change g₁ ∈ Sspan at hg₁; change g₂ ∈ Sspan at hg₂; change g₁ * g₂ ∈ Sspan
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hg₁
        · rintro _ ⟨⟨f₁, w₁⟩, rfl⟩
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hg₂
          · rintro _ ⟨⟨f₂, w₂⟩, rfl⟩
            rw [hgen_mul]
            exact Submodule.subset_span ⟨⟨f₁ * f₂, w₁ + w₂⟩, rfl⟩
          · rw [mul_zero]; exact Sspan.zero_mem
          · intro a b _ _ ha hb; rw [mul_add]; exact Sspan.add_mem ha hb
          · intro r a _ ha; rw [mul_smul_comm]; exact Sspan.smul_mem r ha
        · rw [zero_mul]; exact Sspan.zero_mem
        · intro a b _ _ ha hb; rw [add_mul]; exact Sspan.add_mem ha hb
        · intro r a _ ha; rw [smul_mul_assoc]; exact Sspan.smul_mem r ha
      one_mem' := by
        change (1 : C(↥V × ↥K₂, ℝ)) ∈ Sspan
        rw [← hgen_one]
        exact Submodule.subset_span ⟨⟨1, 0⟩, rfl⟩
      add_mem' := fun ha hb => Sspan.add_mem ha hb
      zero_mem' := Sspan.zero_mem
      algebraMap_mem' := fun r => by
        change algebraMap ℝ C(↥V × ↥K₂, ℝ) r ∈ Sspan
        rw [Algebra.algebraMap_eq_smul_one]
        refine Sspan.smul_mem r ?_
        rw [← hgen_one]
        exact Submodule.subset_span ⟨⟨1, 0⟩, rfl⟩ }
  have hAsep : A.SeparatesPoints := by
    intro q₁ q₂ hne
    by_cases hu : q₁.1 ≠ q₂.1
    · let f : C(↥V, ℝ) := ⟨fun u => dist u q₁.1, continuous_id.dist continuous_const⟩
      refine ⟨gen f 0, ⟨gen f 0, Submodule.subset_span ⟨⟨f, 0⟩, rfl⟩, rfl⟩, ?_⟩
      simp only [gen, ContinuousMap.coe_mk, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        Real.exp_zero, mul_one, f, dist_self]
      exact (dist_pos.mpr hu.symm).ne
    · push Not at hu
      have hy : q₁.2 ≠ q₂.2 := fun h => hne (Prod.ext hu h)
      have hyval : q₁.2.1 ≠ q₂.2.1 := fun h => hy (Subtype.ext h)
      have hexl : ∃ l : Fin d, q₁.2.1 l ≠ q₂.2.1 l := by
        by_contra hall
        push Not at hall
        exact hyval (funext hall)
      obtain ⟨l, hl⟩ := hexl
      let w : Fin d → ℝ := Pi.single l 1
      refine ⟨gen 1 w, ⟨gen 1 w, Submodule.subset_span ⟨⟨1, w⟩, rfl⟩, rfl⟩, ?_⟩
      simp only [gen, ContinuousMap.coe_mk, ContinuousMap.one_apply, one_mul, w,
        Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact fun h => hl (Real.exp_injective h)
  obtain ⟨⟨g, hgA⟩, hg_approx⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hAsep
      (fun q : ↥V × ↥K₂ => G q.1.1 q.2) hG_joint δ hδ
  have hg_span : g ∈ Submodule.span ℝ GenSet := hgA
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg_span
  obtain ⟨coeff, hcoeff⟩ := hg_span
  let S : ℕ := coeff.support.card
  let eS : Fin S ≃ coeff.support := coeff.support.equivFin.symm
  let fs : Fin S → C(↥V, ℝ) := fun s => coeff (eS s).1 • (eS s).1.1
  let ws : Fin S → Fin d → ℝ := fun s => (eS s).1.2
  refine ⟨S, fs, ws, fun u y => ?_⟩
  have hg_eq : g (u, y) = ∑ s : Fin S, fs s u * Real.exp (∑ l : Fin d, ws s l * y.1 l) := by
    rw [← hcoeff]
    simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    rw [← Finset.sum_coe_sort coeff.support]
    rw [← Equiv.sum_comp eS]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [fs, ws, gen, ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul, mul_assoc]
  have h1 := hg_approx (u, y)
  rw [Real.norm_eq_abs, abs_sub_comm] at h1
  simpa [hg_eq] using h1

private lemma sum_prod_error_lt {S : ℕ} (hS : 0 < S) {ε : ℝ} (hε : 0 < ε)
    {a b : Fin S → ℝ} {M : Fin S → ℝ} (hM : ∀ s, 0 ≤ M s)
    (ha : ∀ s, |a s| ≤ M s) (hb : ∀ s, |b s| < ε / (3 * S * (M s + 1))) :
    |∑ s : Fin S, a s * b s| < ε / 3 := by
  have hS_rpos : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  calc |∑ s : Fin S, a s * b s|
      ≤ ∑ s : Fin S, |a s * b s| := Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _s : Fin S, ε / (3 * S) := by
        refine Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hS)) ?_
        intro s _
        rw [abs_mul]
        have hMp : 0 < M s + 1 := by linarith [hM s]
        have hden : 0 < 3 * (S : ℝ) * (M s + 1) := mul_pos (mul_pos (by norm_num) hS_rpos) hMp
        have hfrac_pos : 0 < ε / (3 * S * (M s + 1)) := div_pos hε hden
        have h1 : |a s| * |b s| ≤ M s * (ε / (3 * S * (M s + 1))) :=
          mul_le_mul (ha s) (hb s).le (abs_nonneg _) (hM s)
        have h2 : M s * (ε / (3 * S * (M s + 1))) < (M s + 1) * (ε / (3 * S * (M s + 1))) :=
          mul_lt_mul_of_pos_right (lt_add_one (M s)) hfrac_pos
        have h3 : (M s + 1) * (ε / (3 * S * (M s + 1))) = ε / (3 * S) := by
          field_simp [hMp.ne', hS_rpos.ne']
        linarith
    _ = ε / 3 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [hS_rpos.ne']

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {d : ℕ} (σ : ℝ → ℝ) (hσ : IsTauberWiener σ)
    (K₁ : Set X) (hK₁ : IsCompact K₁) (hK₁ne : K₁.Nonempty)
    (K₂ : Set (Fin d → ℝ)) (hK₂ : IsCompact K₂)
    (V : Set C(K₁, ℝ)) (hV : IsCompact V) (G : C(K₁, ℝ) → C(K₂, ℝ)) (hG : ContinuousOn G V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n p m : ℕ, 0 < n ∧ 0 < p ∧ 0 < m ∧
      ∃ (c : Fin p → Fin n → ℝ) (ξ : Fin p → Fin n → Fin m → ℝ) (θ : Fin p → Fin n → ℝ)
        (ζ : Fin p → ℝ) (w : Fin p → Fin d → ℝ) (x : Fin m → K₁),
        ∀ u ∈ V, ∀ y : K₂, |G u y - operatorNet σ c ξ θ w ζ (fun j => u (x j)) y| < ε := by
  obtain ⟨x₀, hx₀⟩ := hK₁ne
  by_cases hVne : V.Nonempty
  · by_cases hK₂ne : K₂.Nonempty
    · have : CompactSpace ↥V := isCompact_iff_compactSpace.mp hV
      have : CompactSpace ↥K₂ := isCompact_iff_compactSpace.mp hK₂
      obtain ⟨S, fs, ws, hSW⟩ :=
        approx_by_separated_exp K₁ hK₁ K₂ hK₂ hK₂ne V hV hVne G hG (ε / 3) (by positivity)
      by_cases hS : S = 0
      · refine ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one,
          fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0,
          fun _ => ⟨x₀, hx₀⟩, ?_⟩
        intro u huV y
        have h1 := hSW ⟨u, huV⟩ y
        have hzero : (∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l)) = 0 :=
          Finset.sum_eq_zero fun s _ => absurd s.2 (by omega)
        rw [hzero, sub_zero] at h1
        simp only [operatorNet, branchNet, zero_mul, Finset.sum_const_zero, sub_zero]
        linarith
      · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
        -- Step 1: For each s, approximate exp(ws s · y) uniformly on K₂ via IsTauberWiener σ
        have htrunk_s : ∀ s : Fin S,
            ∃ (Nt : ℕ) (at_ lamt ζt : Fin Nt → ℝ) (Me : ℝ), 0 ≤ Me ∧
              (∀ y : ↥K₂, |Real.exp (∑ l, ws s l * y.1 l) -
                ∑ r : Fin Nt, at_ r * σ (lamt r * (∑ l, ws s l * y.1 l) + ζt r)| <
                ε / (3 * S * (‖fs s‖ + 1))) ∧
              (∀ y : ↥K₂, |∑ r : Fin Nt, at_ r * σ (lamt r * (∑ l, ws s l * y.1 l) + ζt r)| ≤ Me) := by
          intro s
          let Ly : C(↥K₂, ℝ) :=
            ⟨fun y => ∑ l : Fin d, ws s l * y.1 l,
              continuous_finsetSum _ fun l _ =>
                continuous_const.mul ((continuous_apply l).comp continuous_subtype_val)⟩
          let R : ℝ := ‖Ly‖
          have hS_rpos : (0 : ℝ) < S := Nat.cast_pos.mpr hSpos
          let δ : ℝ := min 1 (ε / (3 * S * (‖fs s‖ + 1)))
          have hδpos : 0 < δ := lt_min zero_lt_one (by positivity)
          obtain ⟨Nt, at_, lamt, ζt, hNt⟩ :=
            hσ (-R) R Real.exp Real.continuous_exp.continuousOn δ hδpos
          refine ⟨Nt, at_, lamt, ζt, Real.exp R + 1, by positivity, ?_, ?_⟩
          · intro y
            have hmem : ∑ l, ws s l * y.1 l ∈ Set.Icc (-R) R :=
              abs_le.mp (ContinuousMap.norm_coe_le_norm Ly y)
            exact (hNt _ hmem).trans_le (min_le_right _ _)
          · intro y
            have hmem : ∑ l, ws s l * y.1 l ∈ Set.Icc (-R) R :=
              abs_le.mp (ContinuousMap.norm_coe_le_norm Ly y)
            have hdiff : |Real.exp (∑ l, ws s l * y.1 l) -
                ∑ r : Fin Nt, at_ r * σ (lamt r * (∑ l, ws s l * y.1 l) + ζt r)| < 1 :=
              (hNt _ hmem).trans_le (min_le_left _ _)
            have habs_exp : |Real.exp (∑ l, ws s l * y.1 l)| ≤ Real.exp R := by
              rw [abs_of_pos (Real.exp_pos _)]
              exact Real.exp_le_exp.mpr hmem.2
            have htri := abs_sub_abs_le_abs_sub
              (∑ r : Fin Nt, at_ r * σ (lamt r * (∑ l, ws s l * y.1 l) + ζt r))
              (Real.exp (∑ l, ws s l * y.1 l))
            rw [abs_sub_comm] at htri
            linarith
        choose Nt at_ lamt ζt Me hMe_nonneg hNt_approx hNt_bd using htrunk_s
        -- Step 2: For each s, approximate fs s on V using universal_approximation_functional
        classical
        have hbranch_s : ∀ s : Fin S,
            ∃ (nb : ℕ) (mb : ℕ) (xb : Fin mb → K₁) (cb θb : Fin nb → ℝ) (ξb : Fin nb → Fin mb → ℝ),
              ∀ u (hu : u ∈ V), |fs s ⟨u, hu⟩ - branchNet σ cb ξb θb (fun j => u (xb j))| <
                ε / (3 * S * (Me s + 1)) := by
          intro s
          let Fs : C(K₁, ℝ) → ℝ := fun u => if hu : u ∈ V then fs s ⟨u, hu⟩ else 0
          have hFs_cont : ContinuousOn Fs V := by
            rw [continuousOn_iff_continuous_domRestrict]
            have heq : V.domRestrict Fs = fun u : ↥V => fs s u := by
              ext u
              simp [Set.domRestrict, Fs]
            rw [heq]
            exact (fs s).continuous
          have hS_rpos : (0 : ℝ) < S := Nat.cast_pos.mpr hSpos
          have hδpos : 0 < ε / (3 * S * (Me s + 1)) := by
            have := hMe_nonneg s
            positivity
          obtain ⟨nb, _, mb, xb, cb, θb, ξb, hnb⟩ :=
            universal_approximation_functional σ hσ K₁ hK₁ V hV Fs hFs_cont _ hδpos
          refine ⟨nb, mb, xb, cb, θb, ξb, fun u huV => ?_⟩
          simpa [Fs, dif_pos huV] using hnb u huV
        choose nb mb xb cb θb ξb hnb using hbranch_s
        -- Step 3: Pool sensors into Fin m (with m > 0) and branch width into Fin n (with n > 0)
        let IdxM := Σ s : Fin S, Fin (mb s)
        let m₀ : ℕ := Fintype.card IdxM
        let eM : Fin m₀ ≃ IdxM := (Fintype.equivFin IdxM).symm
        let m : ℕ := m₀ + 1
        let x : Fin m → K₁ := fun j =>
          if hj : j.1 < m₀ then
            let q := eM ⟨j.1, hj⟩
            xb q.1 q.2
          else ⟨x₀, hx₀⟩
        let n : ℕ := (Finset.univ.sup nb) + 1
        let c_pad (s : Fin S) (i : Fin n) : ℝ :=
          if hi : i.1 < nb s then cb s ⟨i.1, hi⟩ else 0
        let θ_pad (s : Fin S) (i : Fin n) : ℝ :=
          if hi : i.1 < nb s then θb s ⟨i.1, hi⟩ else 0
        let ξ_pad (s : Fin S) (i : Fin n) (j : Fin m) : ℝ :=
          if hi : i.1 < nb s then
            if hj : j.1 < m₀ then
              let q := eM ⟨j.1, hj⟩
              if hqs : q.1 = s then ξb s ⟨i.1, hi⟩ (hqs ▸ q.2) else 0
            else 0
          else 0
        have hbranch_pad : ∀ (s : Fin S) (u : C(K₁, ℝ)),
            branchNet σ (c_pad s) (ξ_pad s) (θ_pad s) (fun j => u (x j)) =
              branchNet σ (cb s) (ξb s) (θb s) (fun j => u (xb s j)) := by
          intro s u
          unfold branchNet
          have hnb_le : nb s ≤ n := Nat.le_succ_of_le (Finset.le_sup (f := nb) (Finset.mem_univ s))
          have hinner : ∀ (i : Fin (nb s)),
              ∑ j : Fin m, ξ_pad s ⟨i.1, lt_of_lt_of_le i.2 hnb_le⟩ j * u (x j) =
                ∑ j : Fin (mb s), ξb s i j * u (xb s j) := by
            intro i
            rw [Fin.sum_univ_castSucc]
            have hlast : ξ_pad s ⟨i.1, lt_of_lt_of_le i.2 hnb_le⟩ (Fin.last m₀) *
                u (x (Fin.last m₀)) = 0 := by simp [ξ_pad]
            rw [hlast, add_zero]
            have h1 : (∑ j : Fin m₀,
                ξ_pad s ⟨i.1, lt_of_lt_of_le i.2 hnb_le⟩ j.castSucc * u (x j.castSucc)) =
                ∑ q : IdxM, (if hqs : q.1 = s then ξb s i (hqs ▸ q.2) else 0) * u (xb q.1 q.2) := by
              rw [← Equiv.sum_comp eM]
              refine Finset.sum_congr rfl fun j _ => ?_
              have hj : j.castSucc.1 < m₀ := j.2
              simp only [ξ_pad, x, dif_pos i.2, dif_pos hj, Fin.val_castSucc, Fin.eta, dif_pos j.2]
            rw [h1, Fintype.sum_sigma, Finset.sum_eq_single s]
            · refine Finset.sum_congr rfl fun j _ => by simp
            · intro s' _ hs'
              exact Finset.sum_eq_zero fun j _ => by simp [hs']
            · intro h; exact (h (Finset.mem_univ s)).elim
          have hsplit : (∑ i : Fin n, c_pad s i * σ (∑ j, ξ_pad s i j * u (x j) + θ_pad s i)) =
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.1 < nb s),
                c_pad s i * σ (∑ j, ξ_pad s i j * u (x j) + θ_pad s i) := by
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
            simp [c_pad, not_lt.mpr hi]
          rw [hsplit]
          refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
            (fun i _ => ⟨⟨i.1, lt_of_lt_of_le i.2 hnb_le⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩, rfl⟩)
            (fun i hi => ?_)
          have hi' : i.1 < nb s := (Finset.mem_filter.mp hi).2
          have hi_eq : (⟨i.1, lt_of_lt_of_le hi' hnb_le⟩ : Fin n) = i := Fin.ext rfl
          simp only [c_pad, θ_pad, dif_pos hi']
          congr 2
          simpa [hi_eq] using hinner ⟨i.1, hi'⟩
        -- Step 4: Pool trunk indices into Fin p (with p > 0)
        let IdxP := Σ s : Fin S, Fin (Nt s)
        let p₀ : ℕ := Fintype.card IdxP
        let eP : Fin p₀ ≃ IdxP := (Fintype.equivFin IdxP).symm
        let p : ℕ := p₀ + 1
        let c_op : Fin p → Fin n → ℝ := fun k i =>
          if hk : k.1 < p₀ then
            let q := eP ⟨k.1, hk⟩
            at_ q.1 q.2 * c_pad q.1 i
          else 0
        let ξ_op : Fin p → Fin n → Fin m → ℝ := fun k i j =>
          if hk : k.1 < p₀ then
            let q := eP ⟨k.1, hk⟩
            ξ_pad q.1 i j
          else 0
        let θ_op : Fin p → Fin n → ℝ := fun k i =>
          if hk : k.1 < p₀ then
            let q := eP ⟨k.1, hk⟩
            θ_pad q.1 i
          else 0
        let w_op : Fin p → Fin d → ℝ := fun k l =>
          if hk : k.1 < p₀ then
            let q := eP ⟨k.1, hk⟩
            lamt q.1 q.2 * ws q.1 l
          else 0
        let ζ_op : Fin p → ℝ := fun k =>
          if hk : k.1 < p₀ then
            let q := eP ⟨k.1, hk⟩
            ζt q.1 q.2
          else 0
        refine ⟨n, p, m, Nat.succ_pos _, Nat.succ_pos _, Nat.succ_pos _,
          c_op, ξ_op, θ_op, ζ_op, w_op, x, ?_⟩
        intro u huV y
        let B (s : Fin S) : ℝ := branchNet σ (cb s) (ξb s) (θb s) (fun j => u (xb s j))
        let T (s : Fin S) : ℝ := ∑ r : Fin (Nt s), at_ s r * σ (lamt s r * (∑ l, ws s l * y.1 l) + ζt s r)
        have hop_eq : operatorNet σ c_op ξ_op θ_op w_op ζ_op (fun j => u (x j)) y.1 =
            ∑ s : Fin S, B s * T s := by
          unfold operatorNet
          rw [Fin.sum_univ_castSucc]
          have hlast : branchNet σ (c_op (Fin.last p₀)) (ξ_op (Fin.last p₀)) (θ_op (Fin.last p₀))
              (fun j => u (x j)) * trunkNet σ (w_op (Fin.last p₀)) (ζ_op (Fin.last p₀)) y.1 = 0 := by
            simp [branchNet, c_op]
          rw [hlast, add_zero]
          have h1 : (∑ k : Fin p₀,
              branchNet σ (c_op k.castSucc) (ξ_op k.castSucc) (θ_op k.castSucc) (fun j => u (x j)) *
              trunkNet σ (w_op k.castSucc) (ζ_op k.castSucc) y.1) =
              ∑ q : IdxP, B q.1 * (at_ q.1 q.2 * σ (lamt q.1 q.2 * (∑ l, ws q.1 l * y.1 l) + ζt q.1 q.2)) := by
            rw [← Equiv.sum_comp eP]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hk : k.castSucc.1 < p₀ := k.2
            have hb_scale : branchNet σ (c_op k.castSucc) (ξ_op k.castSucc) (θ_op k.castSucc)
                (fun j => u (x j)) = at_ (eP k).1 (eP k).2 * B (eP k).1 := by
              dsimp only [B]
              rw [← hbranch_pad (eP k).1 u]
              unfold branchNet
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              simp only [c_op, ξ_op, θ_op, dif_pos hk, Fin.val_castSucc, Fin.eta, mul_assoc]
            have ht_eq : trunkNet σ (w_op k.castSucc) (ζ_op k.castSucc) y.1 =
                σ (lamt (eP k).1 (eP k).2 * (∑ l, ws (eP k).1 l * y.1 l) + ζt (eP k).1 (eP k).2) := by
              unfold trunkNet
              simp only [w_op, ζ_op, dif_pos hk, Fin.val_castSucc, Fin.eta]
              congr 2
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun l _ => by ring
            rw [hb_scale, ht_eq]
            ring
          rw [h1, Fintype.sum_sigma]
          refine Finset.sum_congr rfl fun s _ => ?_
          dsimp only [T]
          rw [Finset.mul_sum]
        rw [hop_eq]
        have h_err1 : |G u y - ∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l)| < ε / 3 :=
          hSW ⟨u, huV⟩ y
        have h_err2 : |∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l) -
            ∑ s : Fin S, fs s ⟨u, huV⟩ * T s| < ε / 3 := by
          rw [← Finset.sum_sub_distrib]
          have hsub : (∑ s : Fin S, (fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l) -
              fs s ⟨u, huV⟩ * T s)) =
              ∑ s : Fin S, fs s ⟨u, huV⟩ * (Real.exp (∑ l : Fin d, ws s l * y.1 l) - T s) :=
            Finset.sum_congr rfl fun s _ => (mul_sub _ _ _).symm
          rw [hsub]
          exact sum_prod_error_lt hSpos hε (fun s => norm_nonneg (fs s))
            (fun s => ContinuousMap.norm_coe_le_norm (fs s) ⟨u, huV⟩)
            (fun s => hNt_approx s y)
        have h_err3 : |∑ s : Fin S, fs s ⟨u, huV⟩ * T s - ∑ s : Fin S, B s * T s| < ε / 3 := by
          rw [← Finset.sum_sub_distrib]
          have hsub : (∑ s : Fin S, (fs s ⟨u, huV⟩ * T s - B s * T s)) =
              ∑ s : Fin S, T s * (fs s ⟨u, huV⟩ - B s) :=
            Finset.sum_congr rfl fun s _ => by ring
          rw [hsub]
          exact sum_prod_error_lt hSpos hε hMe_nonneg (fun s => hNt_bd s y) (fun s => hnb s u huV)
        have hsplit_eq : G u y - ∑ s : Fin S, B s * T s =
            (G u y - ∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l)) +
              (∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l) -
                ∑ s : Fin S, fs s ⟨u, huV⟩ * T s) +
              (∑ s : Fin S, fs s ⟨u, huV⟩ * T s - ∑ s : Fin S, B s * T s) := by ring
        rw [hsplit_eq]
        have htri1 := abs_add_le
          ((G u y - ∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l)) +
            (∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l) -
              ∑ s : Fin S, fs s ⟨u, huV⟩ * T s))
          (∑ s : Fin S, fs s ⟨u, huV⟩ * T s - ∑ s : Fin S, B s * T s)
        have htri2 := abs_add_le
          (G u y - ∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l))
          (∑ s : Fin S, fs s ⟨u, huV⟩ * Real.exp (∑ l : Fin d, ws s l * y.1 l) -
            ∑ s : Fin S, fs s ⟨u, huV⟩ * T s)
        linarith
    · refine ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one,
        fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0,
        fun _ => ⟨x₀, hx₀⟩, ?_⟩
      intro u _ y
      exact (hK₂ne ⟨y.1, y.2⟩).elim
  · rw [Set.not_nonempty_iff_eq_empty] at hVne
    refine ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one,
      fun _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0,
      fun _ => ⟨x₀, hx₀⟩, ?_⟩
    intro u huV
    rw [hVne] at huV
    exact huV.elim
