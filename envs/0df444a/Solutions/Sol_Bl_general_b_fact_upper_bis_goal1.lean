-- Prove2me | solution 1 for Bl.general_b_fact_upper_bis.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:20.579661+00:00
-- url     : https://prove2.me/submissions/4a7c41a1-5aea-4d8b-a0eb-c5848db0ea2b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperBis_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_bis
namespace Bl.general_b_fact_upper_bis
theorem _root_.solution :
  ∀ {A K : Type} [inst : CommRing.{0} A] [inst_1 : IsDedekindDomain.{0} A] [inst_2 : Field.{0} K]
  [inst_3 : Algebra.{0, 0} A K] [inst_4 : IsFractionRing.{0, 0} A K] (w : IsDedekindDomain.HeightOneSpectrum.{0} A)
  {V : Type} [inst_5 : AddCommGroup.{0} V] [inst_6 : Module.{0, 0} K V] [inst_7 : Module.{0, 0} A V]
  [IsScalarTower.{0, 0, 0} A K V] {ι : Type} [Fintype.{0} ι] (b : Module.Basis.{0, 0, 0} ι K V) {O Kf Fn : Type}
  [inst_10 : CommRing.{0} O] [inst_11 : Field.{0} Kf] [inst_12 : Algebra.{0, 0} O Kf] [inst_13 : AddCommGroup.{0} Fn]
  [inst_14 : Module.{0, 0} Kf Fn] [inst_15 : Module.{0, 0} O Fn] [IsScalarTower.{0, 0, 0} O Kf Fn]
  (φ : RingHom.{0, 0} K Kf) (cmp : AddMonoidHom.{0, 0} V Fn),
  (∀ (x : K),
      Iff (LE.le.{0} (DFunLike.coe.{1, 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{0, 0} K w) x) 1)
        (Membership.mem.{0, 0} (Set.range.{0, 1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} O Kf)))
          (DFunLike.coe.{1, 1, 1} φ x))) →
    (∀ (a : K) (x : V),
        Eq.{1} (DFunLike.coe.{1, 1, 1} cmp (HSMul.hSMul.{0, 0, 0} a x))
          (HSMul.hSMul.{0, 0, 0} (DFunLike.coe.{1, 1, 1} φ a) (DFunLike.coe.{1, 1, 1} cmp x))) →
      (LinearIndependent.{0, 0, 0} Kf fun (a : ι) ↦ DFunLike.coe.{1, 1, 1} cmp (DFunLike.coe.{1, 1, 1} b a)) →
        ∀ (Lat : Submodule.{0, 0} A V),
          Submodule.FG.{0, 0} Lat →
            ∀ (v : V),
              Membership.mem.{0, 0}
                  (Submodule.span.{0, 0} O (Set.image.{0, 0} (DFunLike.coe.{1, 1, 1} cmp) (SetLike.coe.{0, 0} Lat)))
                  (DFunLike.coe.{1, 1, 1} cmp v) →
                Exists.{1} fun (s : A) ↦
                  And (Not (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} w) s))
                    (Membership.mem.{0, 0} Lat (HSMul.hSMul.{0, 0, 0} s v)) := by
  intro A K _ _ _ _ _ w V _ _ _ _ ι _ b O Kf Fn _ _ _ _ _ _ _ φ cmp h1 h2 h3 Lat hLat v hv
  classical
  have T : ∀ f : V →ₗ[K] K, ∃ g : Fn →ₗ[Kf] Kf, ∀ y, g (cmp y) = φ (f y) := by
    intro f
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span h3).constr Kf (fun i => φ (f (b i))))
    refine ⟨g, fun y => ?_⟩
    have hb : ∀ i, g (cmp (b i)) = φ (f (b i)) := by
      intro i
      have := congrArg (fun F => F (Module.Basis.span h3 i)) hg
      simp only [Module.Basis.constr_basis] at this
      simpa using this
    rw [← b.sum_repr y]
    simp only [map_sum, h2, map_smul, smul_eq_mul, hb, map_mul]
  have hsm : ∀ c : K, w.valuation K c ≤ 1 → ∀ (Tt : Set Fn) (z : Fn),
      z ∈ Submodule.span O Tt → φ c • z ∈ Submodule.span O Tt := by
    intro c hc Tt z hz
    obtain ⟨o, ho⟩ := (h1 c).1 hc
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o hz
  have key : ∀ n : ℕ, ∀ S : Finset V, S.card = n → ∀ v : V,
      cmp v ∈ Submodule.span O (cmp '' (S : Set V)) →
      ∃ s : A, s ∉ w.asIdeal ∧ s • v ∈ Submodule.span A (S : Set V) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih S hSn v hv
    rcases S.eq_empty_or_nonempty with hE | ⟨x1, hx1⟩
    · subst hE
      refine ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
      have h0 : cmp v = 0 := by simpa using hv
      have hv0 : v = 0 := by
        by_contra hne
        have hnb : v ∉ (⊥ : Submodule K V) := by simpa using hne
        obtain ⟨f, hf, -⟩ := Submodule.exists_le_ker_of_notMem hnb
        obtain ⟨g, hg⟩ := T f
        have e := hg v
        rw [h0, map_zero] at e
        exact hf ((map_eq_zero φ).1 e.symm)
      simp [hv0]
    by_cases hx : x1 ∈ Submodule.span K (S.erase x1 : Set V)
    · obtain ⟨c, -, hcsum⟩ := Submodule.mem_span_finset.1 hx
      let lam : V → K := fun x => if x = x1 then -1 else c x
      have hlam : ∑ x ∈ S, lam x • x = 0 := by
        rw [← Finset.add_sum_erase S _ hx1]
        have hc : ∑ x ∈ S.erase x1, lam x • x = ∑ x ∈ S.erase x1, c x • x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp [lam, Finset.ne_of_mem_erase hx]
        rw [hc, hcsum]
        simp [lam]
      obtain ⟨x0, hx0, hmax⟩ := S.exists_max_image (fun x => w.valuation K (lam x)) ⟨x1, hx1⟩
      have hl0 : lam x0 ≠ 0 := by
        intro h0
        have h01 := hmax x1 hx1
        simp only [h0, map_zero] at h01
        simp [lam] at h01
      have hrel : x0 = ∑ x ∈ S.erase x0, (-(lam x0)⁻¹ * lam x) • x := by
        have e := hlam
        rw [← Finset.add_sum_erase S _ hx0] at e
        have e' : ∑ x ∈ S.erase x0, lam x • x = -(lam x0 • x0) := eq_neg_of_add_eq_zero_right e
        simp only [neg_mul, neg_smul, mul_smul, Finset.sum_neg_distrib, ← Finset.smul_sum, e',
          smul_neg, neg_neg, inv_smul_smul₀ hl0]
      have hx0mem : cmp x0 ∈ Submodule.span O (cmp '' (S.erase x0 : Set V)) := by
        rw [show cmp x0 = cmp (∑ x ∈ S.erase x0, (-(lam x0)⁻¹ * lam x) • x) from congrArg cmp hrel,
          map_sum]
        refine Submodule.sum_mem _ fun x hx => ?_
        rw [h2]
        refine hsm _ ?_ _ _ (Submodule.subset_span ⟨x, Finset.mem_coe.2 hx, rfl⟩)
        rw [map_mul, Valuation.map_neg, map_inv₀]
        have hpos : w.valuation K (lam x0) ≠ 0 := (Valuation.ne_zero_iff _).2 hl0
        rw [inv_mul_le_one₀ (zero_lt_iff.2 hpos)]
        exact hmax x (Finset.mem_of_mem_erase hx)
      have hv' : cmp v ∈ Submodule.span O (cmp '' (S.erase x0 : Set V)) := by
        refine (Submodule.span_le.2 ?_) hv
        rintro _ ⟨y, hy, rfl⟩
        by_cases hyx : y = x0
        · rw [hyx]; exact hx0mem
        · exact Submodule.subset_span ⟨y, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyx, hy⟩), rfl⟩
      obtain ⟨s, hs, hsv⟩ := ih _ (by rw [← hSn]; exact Finset.card_erase_lt_of_mem hx0)
        (S.erase x0) rfl v hv'
      exact ⟨s, hs, Submodule.span_mono (Finset.coe_subset.2 (Finset.erase_subset _ _)) hsv⟩
    · obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_notMem hx
      obtain ⟨g, hg⟩ := T f
      have hSins : (S : Set V) = insert x1 (S.erase x1 : Set V) := by
        rw [← Finset.coe_insert, Finset.insert_erase hx1]
      rw [hSins, Set.image_insert_eq, Submodule.mem_span_insert] at hv
      obtain ⟨o, z, hz, hvz⟩ := hv
      have hgz : g z = 0 := by
        have hk : Submodule.span O (cmp '' (S.erase x1 : Set V)) ≤
            LinearMap.ker (g.restrictScalars O) := by
          rw [Submodule.span_le]
          rintro _ ⟨y, hy, rfl⟩
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hg]
          rw [LinearMap.mem_ker.1 (hker (Submodule.subset_span hy)), map_zero]
        simpa using hk hz
      obtain ⟨t, ht⟩ : ∃ t, t = f v / f x1 := ⟨_, rfl⟩
      have hφt : φ t = algebraMap O Kf o := by
        have e := hg v
        rw [hvz, map_add, hgz, add_zero, ← algebraMap_smul Kf o (cmp x1), map_smul, hg,
          smul_eq_mul] at e
        rw [ht, map_div₀, ← e, mul_div_assoc, div_self ((map_ne_zero φ).2 hf0), mul_one]
      have htv : w.valuation K t ≤ 1 := (h1 t).2 ⟨o, hφt.symm⟩
      obtain ⟨nn, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer t htv
      have hrest : cmp (v - t • x1) ∈ Submodule.span O (cmp '' (S.erase x1 : Set V)) := by
        rw [map_sub, h2, hvz, hφt, algebraMap_smul Kf, add_sub_cancel_left]
        exact hz
      obtain ⟨s, hs, hsv⟩ := ih _ (by rw [← hSn]; exact Finset.card_erase_lt_of_mem hx1)
        (S.erase x1) rfl _ hrest
      have hdA : (d : A) ∉ w.asIdeal := d.2
      refine ⟨s * d, fun h => (w.isPrime.mem_or_mem h).elim hs hdA, ?_⟩
      have e2 : ((d : A) * s) • (t • x1) = (s * nn) • x1 := by
        rw [← algebraMap_smul K ((d : A) * s) (t • x1), smul_smul, ← algebraMap_smul K (s * nn) x1]
        congr 1
        rw [map_mul, map_mul, ← hnd]
        ring
      have hcomb : (d : A) • (s • (v - t • x1)) + (s * nn) • x1 = (s * d) • v := by
        simp only [smul_sub, smul_smul]
        rw [e2, sub_add_cancel, mul_comm]
      rw [← hcomb]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _
        (Submodule.span_mono (Finset.coe_subset.2 (Finset.erase_subset _ _)) hsv))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 hx1)))
  obtain ⟨S, hS⟩ := hLat
  have hle : Submodule.span O (cmp '' (Lat : Set V)) ≤ Submodule.span O (cmp '' (S : Set V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span A (S : Set V) := by rw [hS]; exact hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul K a x, h2]
      exact hsm _ (w.valuation_le_one (K := K) a) _ _ hx
  obtain ⟨s, hs, hsv⟩ := key _ S rfl v (hle hv)
  exact ⟨s, hs, hS ▸ hsv⟩
end Bl.general_b_fact_upper_bis
