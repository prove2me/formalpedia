-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1811d8ad-8f11-5fcd-987d-314f977ad002

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace P2mE2b

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

theorem isMaximal_pIdeal [IsAlgClosed k] : (pIdeal p (WittVector p k)).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)

theorem charP_quot : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
  CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)

theorem isAlgClosed_of_ringEquiv {F F' : Type} [Field F] [Field F'] [IsAlgClosed F] (e : F ≃+* F') :
    IsAlgClosed F' := by
  refine IsAlgClosed.of_exists_root F' fun q _ hqi => ?_
  set q' : Polynomial F := q.map e.symm.toRingHom with hq'def
  have hq' : q'.degree ≠ 0 := by
    rw [hq'def, Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q' hq'
  refine ⟨e x, ?_⟩
  have hqq : q = q'.map e.toRingHom := by
    rw [hq'def, Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
  rw [hqq, Polynomial.eval_map]
  show Polynomial.eval₂ e.toRingHom (e.toRingHom x) q' = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

end P2mE2b

end

namespace P2mCofull

variable {p : ℕ} [hp : Fact p.Prime]

local notation "M2[" R "]" => Matrix (Fin 2) (Fin 2) R

noncomputable def AQ (p : ℕ) [Fact p.Prime] : M2[ℤ_[p]] →+* M2[ℚ_[p]] := (PadicInt.Coe.ringHom (p := p)).mapMatrix

theorem AQ_apply (A : M2[ℤ_[p]]) : AQ p A = A.map ((↑) : ℤ_[p] → ℚ_[p]) := rfl

theorem AQ_entry (A : M2[ℤ_[p]]) (i j : Fin 2) : AQ p A i j = (A i j : ℚ_[p]) := rfl

theorem AQ_smul (c : ℤ_[p]) (A : M2[ℤ_[p]]) : AQ p (c • A) = (c : ℚ_[p]) • AQ p A := by
  ext i j; simp [AQ_entry, Matrix.smul_apply]

theorem AQ_single (i j : Fin 2) (c : ℤ_[p]) :
    AQ p (Matrix.single i j c) = Matrix.single i j (c : ℚ_[p]) := by
  ext a b
  rw [AQ_entry]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [Matrix.single_apply_of_ne (h := h), Matrix.single_apply_of_ne (h := h)]; rfl

theorem natCast_pow_smul (n : ℕ) (X : M2[ℚ_[p]]) : (p ^ n : ℕ) • X = (p : ℚ_[p]) ^ n • X := by
  rw [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow]

theorem exists_pow_mul_norm_le_one {ι : Type} [Fintype ι] (d : ι → ℚ_[p]) :
    ∃ N : ℕ, ∀ i, ‖(p : ℚ_[p]) ^ N * d i‖ ≤ 1 := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have one : ∀ i, ∃ n : ℕ, ∀ N, n ≤ N → ‖(p : ℚ_[p]) ^ N * d i‖ ≤ 1 := by
    intro i
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖d i‖ hp1
    refine ⟨n, fun N hN => ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p]
    have hpN : ((p : ℝ)⁻¹) ^ N * ‖d i‖ ≤ ((p : ℝ)⁻¹) ^ n * ‖d i‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp1.le) hN
    refine hpN.trans ?_
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    simpa using hn.le
  choose n hn using one
  refine ⟨∑ i, n i, fun i => hn i _ ?_⟩
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)

theorem cofull_transfer {R : Type} [Ring R]
    (E E' : R →+* M2[ℚ_[p]]) (hinj : Function.Injective E') (m : ℕ)
    (hcof : ∀ A : M2[ℤ_[p]], ∃ e, E' e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hbd : ∀ e, ∃ A : M2[ℤ_[p]], (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p])) :
    ∃ n : ℕ, ∀ A : M2[ℤ_[p]], ∃ e, E e = (p : ℚ_[p]) ^ n • A.map ((↑) : ℤ_[p] → ℚ_[p]) := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpm0 : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero _ hp0

  choose f hf using hcof
  simp_rw [← AQ_apply (p := p)] at hf
  have hf_add : ∀ A B, f (A + B) = f A + f B := fun A B =>
    hinj (by rw [map_add, hf, hf, hf, map_add, smul_add])
  have hf_zero : f 0 = 0 := hinj (by rw [hf, map_zero, map_zero, smul_zero])
  have hf_mul : ∀ A B, f A * f B = (p ^ m : ℕ) • f (A * B) := fun A B =>
    hinj (by rw [map_mul, hf, hf, map_nsmul, hf, natCast_pow_smul, map_mul, smul_mul_smul_comm, smul_smul])
  have hf_one : f 1 = (p ^ m : ℕ) • (1 : R) := hinj (by rw [hf, map_one, map_nsmul, map_one, natCast_pow_smul])

  let σ : M2[ℤ_[p]] →+ M2[ℚ_[p]] :=
    { toFun := fun A => E (f A)
      map_zero' := by simp only [hf_zero, map_zero]
      map_add' := fun A B => by simp only [hf_add, map_add] }
  have hσ : ∀ A, σ A = E (f A) := fun A => rfl
  have hσ_mul : ∀ A B, σ A * σ B = (p : ℚ_[p]) ^ m • σ (A * B) := fun A B => by
    rw [hσ, hσ, hσ, ← map_mul, hf_mul, map_nsmul, natCast_pow_smul]
  have hσ_one : σ 1 = (p : ℚ_[p]) ^ m • 1 := by rw [hσ, hf_one, map_nsmul, map_one, natCast_pow_smul]
  have hσ_bd : ∀ A i j, ‖σ A i j‖ ≤ p := by
    intro A i j
    obtain ⟨A', hA'⟩ := hbd (f A)
    have h := congr_fun (congr_fun hA' i) j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h
    have hn : ‖(p : ℚ_[p]) * E (f A) i j‖ ≤ 1 := by rw [h]; exact PadicInt.norm_le_one _
    rw [norm_mul, Padic.norm_p, inv_mul_le_iff₀ (by positivity), mul_one] at hn
    exact hn

  have hσ_nat : ∀ (n : ℕ) (A : M2[ℤ_[p]]), σ ((n : ℤ_[p]) • A) = (n : ℚ_[p]) • σ A := fun n A => by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  have hσ_smul : ∀ (c : ℤ_[p]) (A : M2[ℤ_[p]]), σ (c • A) = (c : ℚ_[p]) • σ A := by
    intro c A
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    by_contra hne
    have hDpos : 0 < ‖σ (c • A) i j - (c : ℚ_[p]) * σ A i j‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have key : ∀ N : ℕ, ‖σ (c • A) i j - (c : ℚ_[p]) * σ A i j‖ ≤ ((p : ℝ)⁻¹) ^ N * (p + p) := by
      intro N
      obtain ⟨c', hc'⟩ : ∃ c' : ℤ_[p], c = (c.appr N : ℤ_[p]) + (p : ℤ_[p]) ^ N * c' := by
        obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec N c)
        exact ⟨a, by linear_combination (-1 : ℤ_[p]) * ha⟩
      have h1 : σ (c • A) = (c.appr N : ℚ_[p]) • σ A + (p : ℚ_[p]) ^ N • σ (c' • A) := by
        conv_lhs => rw [hc']
        rw [add_smul, map_add, hσ_nat, mul_smul, ← Nat.cast_pow, hσ_nat, Nat.cast_pow]
      have h2 : (c : ℚ_[p]) = (c.appr N : ℚ_[p]) + (p : ℚ_[p]) ^ N * c' := by
        conv_lhs => rw [hc']
        push_cast; ring
      have h3 : σ (c • A) i j - (c : ℚ_[p]) * σ A i j =
          (p : ℚ_[p]) ^ N * (σ (c' • A) i j - (c' : ℚ_[p]) * σ A i j) := by
        rw [h1, h2, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
        ring
      rw [h3, norm_mul, norm_pow, Padic.norm_p]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (norm_sub_le _ _).trans (add_le_add (hσ_bd _ _ _) ?_)
      rw [norm_mul]
      calc ‖(c' : ℚ_[p])‖ * ‖σ A i j‖ ≤ 1 * p :=
            mul_le_mul (PadicInt.norm_le_one c') (hσ_bd _ _ _) (norm_nonneg _) zero_le_one
        _ = p := one_mul _
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (div_pos hDpos (by positivity : (0 : ℝ) < p + p)) (inv_lt_one_of_one_lt₀ hp1)
    have := (key N).trans_lt ((lt_div_iff₀ (by positivity)).1 hN)
    exact lt_irrefl _ this

  let u : Fin 2 × Fin 2 → M2[ℚ_[p]] := fun ij => σ (Matrix.single ij.1 ij.2 1)
  have hu : ∀ i j, u (i, j) = σ (Matrix.single i j 1) := fun i j => rfl
  have hu_mul_same : ∀ i j k, u (i, j) * u (j, k) = (p : ℚ_[p]) ^ m • u (i, k) := by
    intro i j k; rw [hu, hu, hu, hσ_mul, Matrix.single_mul_single_same, mul_one]
  have hu_mul_ne : ∀ i j j' k, j ≠ j' → u (i, j) * u (j', k) = 0 := by
    intro i j j' k h; rw [hu, hu, hσ_mul, Matrix.single_mul_single_of_ne (h := h), map_zero, smul_zero]
  have hu_sum : ∑ i, u (i, i) = (p : ℚ_[p]) ^ m • 1 := by
    rw [← hσ_one]
    have h1 : (1 : M2[ℤ_[p]]) = ∑ i, Matrix.single i i 1 := by
      rw [Matrix.matrix_eq_sum_single (1 : M2[ℤ_[p]])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq]
      · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), Matrix.single_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, map_sum]
  have hu_ne : ∀ a b, u (a, b) ≠ 0 := by
    intro a b hab
    have hcol : ∀ i, u (i, b) = 0 := fun i => by
      have := hu_mul_same i a b
      rw [hab, mul_zero] at this
      exact (smul_eq_zero.1 this.symm).resolve_left hpm0
    have hdiag : ∀ i, u (i, i) = 0 := fun i => by
      have := hu_mul_same i b i
      rw [hcol, zero_mul] at this
      exact (smul_eq_zero.1 this.symm).resolve_left hpm0
    have h0 : (p : ℚ_[p]) ^ m • (1 : M2[ℚ_[p]]) = 0 := by
      rw [← hu_sum]; exact Finset.sum_eq_zero fun i _ => hdiag i
    have := congr_fun (congr_fun h0 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at this
    exact hpm0 this
  have hli : LinearIndependent ℚ_[p] u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg ab
    obtain ⟨a, b⟩ := ab

    have key : u (a, a) * (∑ ij, g ij • u ij) * u (b, b) = ((p : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ m * g (a, b)) • u (a, b) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_eq_single (a, b)]
      · rw [mul_smul_comm, smul_mul_assoc, hu_mul_same, smul_mul_assoc, hu_mul_same, smul_smul, smul_smul]
        ring_nf
      · rintro ⟨i, j⟩ _ hij
        rw [mul_smul_comm, smul_mul_assoc]
        by_cases hia : a = i
        · subst hia
          have hjb : j ≠ b := fun h => hij (by rw [h])
          rw [hu_mul_same, smul_mul_assoc, hu_mul_ne _ _ _ _ hjb, smul_zero, smul_zero]
        · rw [hu_mul_ne _ _ _ _ hia, zero_mul, smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hg, mul_zero, zero_mul] at key
    have := (smul_eq_zero.1 key.symm).resolve_right (hu_ne a b)
    simpa [hpm0] using this
  have hspan : Submodule.span ℚ_[p] (Set.range u) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    simp [Module.finrank_matrix]

  have hcoord : ∀ ab : Fin 2 × Fin 2, ∃ c : Fin 2 × Fin 2 → ℚ_[p],
      ∑ ij, c ij • u ij = Matrix.single ab.1 ab.2 1 := fun ab =>
    (Submodule.mem_span_range_iff_exists_fun ℚ_[p]).1 (by rw [hspan]; exact Submodule.mem_top)
  choose c hc using hcoord
  obtain ⟨N, hN⟩ := exists_pow_mul_norm_le_one (p := p) (fun x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) => c x.1 x.2)

  let z : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℤ_[p] := fun ab ij => ⟨(p : ℚ_[p]) ^ N * c ab ij, hN (ab, ij)⟩
  have hz : ∀ ab ij, ((z ab ij : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ N * c ab ij := fun _ _ => rfl
  have hzsum : ∀ ab, σ (∑ ij, z ab ij • Matrix.single ij.1 ij.2 1) = (p : ℚ_[p]) ^ N • Matrix.single ab.1 ab.2 1 := by
    intro ab
    rw [map_sum, ← hc ab, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [hσ_smul, hz, ← smul_smul]
  refine ⟨N, fun A => ⟨f (∑ ab, A ab.1 ab.2 • ∑ ij, z ab ij • Matrix.single ij.1 ij.2 1), ?_⟩⟩
  rw [← hσ, map_sum]
  simp_rw [hσ_smul, hzsum, smul_comm _ ((p : ℚ_[p]) ^ N), ← Finset.smul_sum]
  congr 1
  rw [← AQ_apply (p := p)]
  conv_rhs => rw [Matrix.matrix_eq_sum_single A, map_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [AQ_single, Matrix.smul_single, smul_eq_mul, mul_one]

end P2mCofull

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hNe : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))))
    (hE : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) ∧
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w)) :
    ∃ m : ℕ, ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p]) := by
  classical
  haveI hmax : (pIdeal p (WittVector p k)).IsMaximal := P2mE2b.isMaximal_pIdeal p k
  letI instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := P2mE2b.charP_quot p k
  obtain ⟨eK⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  haveI hac : IsAlgClosed (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
    P2mE2b.isAlgClosed_of_ringEquiv eK

  let Φ' : SpecialFormalODModule p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) :=
    ⟨Φ, hΦ, hΦ4⟩

  obtain ⟨i, -, -, β, -, hinj, m, hcof, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed
      p ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) Φ'

  have hbd : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}),
      ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) :=
    fun e => (hE e).imp fun A h => h.1

  exact P2mCofull.cofull_transfer E _ hinj m hcof hbd

end S_CerednikDrinfeld_FormalODModule_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat (solution)
