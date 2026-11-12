-- Prove2me | solution 1 for DualCoppersmith.Recovery.root_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:30:07.740475+00:00
-- url     : https://prove2.me/submissions/1f2a13d2-b5eb-4cff-8986-da53e3670143

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Lattice
import Definitions.Def_DualCoppersmith_Recovery_Algorithm
import Definitions.Def_DualCoppersmith_Recovery_Geometry
import Definitions.Def_DualCoppersmith_Recovery_Instance
import Definitions.Def_LLLFactor_RedBasis_Setting
import Theorems.Thm_DualCoppersmith_Recovery_first_vector_bound
import Theorems.Thm_DualCoppersmith_Recovery_root_line

section
set_option autoImplicit false

namespace DualCoppersmith.Dev.KB

open LLLFactor.RedBasis DualCoppersmith.Recovery

theorem finrank_kernel (I : Instance) (P : Parameters I) :
    Module.finrank ℤ (integerKernel I P) = dimension I P := by
  have hle : Module.finrank ℤ (integerKernel I P) ≤ dimension I P := by
    have := Submodule.finrank_le (integerKernel I P)
    simpa using this
  have hp : ((I.p : ℤ) ^ P.m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast I.prime.ne_zero)
  let f : (Fin (dimension I P) → ℤ) →ₗ[ℤ] (Fin (dimension I P) → ℤ) :=
    ((I.p : ℤ) ^ P.m) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    simp only [f, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hp this
  have hrange : LinearMap.range f ≤ integerKernel I P := by
    rintro _ ⟨z, rfl⟩ q
    simp only [f, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ j, coefficientMatrix I P q j * ((I.p : ℤ) ^ P.m * z j)
        = (I.p : ℤ) ^ P.m * ∑ j, coefficientMatrix I P q j * z j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact dvd_mul_right _ _
  have hge := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hf] at hge
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hge
  omega

theorem exists_basis (I : Instance) (P : Parameters I) :
    ∃ b : Fin (dimension I P) → Vec (dimension I P), IsBasisFor b (kernelLattice I P) := by
  classical
  let B : Module.Basis (Fin (dimension I P)) ℤ (integerKernel I P) :=
    (Module.finBasis ℤ (integerKernel I P)).reindex (finCongr (finrank_kernel I P))
  let v : Fin (dimension I P) → Fin (dimension I P) → ℤ := fun j => (B j : Fin (dimension I P) → ℤ)
  refine ⟨fun j => integerEmbedding _ (v j), ?_, ?_⟩
  · have h1 : LinearIndependent ℤ v :=
      (B.linearIndependent).map' (integerKernel I P).subtype (Submodule.ker_subtype _)
    have h2 : LinearIndependent ℝ (fun i => algebraMap ℤ ℝ ∘ v i) :=
      (linearIndependent_algebraMap_comp_iff (S := ℝ)).2 h1
    have h3 := h2.map' (WithLp.linearEquiv 2 ℝ (Fin (dimension I P) → ℝ)).symm.toLinearMap
      (LinearEquiv.ker _)
    have heq : (fun j => (integerEmbedding (dimension I P)) (v j)) =
        ⇑(WithLp.linearEquiv 2 ℝ (Fin (dimension I P) → ℝ)).symm.toLinearMap ∘
          fun i => ⇑(algebraMap ℤ ℝ) ∘ v i := by
      funext j; ext i; simp [integerEmbedding]
    rw [heq]; exact h3
  · unfold latticeOf kernelLattice
    have hspan : Submodule.span ℤ (Set.range v) = integerKernel I P := by
      have h : Submodule.span ℤ (Set.range v) =
          Submodule.map (integerKernel I P).subtype (Submodule.span ℤ (Set.range B)) := by
        rw [Submodule.map_span, ← Set.range_comp]; rfl
      rw [h, B.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [← hspan, Submodule.map_span]
    congr 1
    ext x; simp

theorem diagonalFactor_pos (I : Instance) (P : Parameters I) (j : Fin (dimension I P)) :
    0 < diagonalFactor I P j := by
  have hb : 0 < boundMonomial I P j :=
    Finset.prod_pos fun i _ => pow_pos (I.X_pos i) _
  have hdvd : boundMonomial I P j ∣ rho I P := Finset.dvd_lcm (Finset.mem_univ j)
  have hr : 0 < rho I P := by
    unfold rho
    apply Nat.pos_of_ne_zero
    intro h
    rw [Finset.lcm_eq_zero_iff] at h
    obtain ⟨k, -, hk⟩ := h
    have : 0 < boundMonomial I P k := Finset.prod_pos fun i _ => pow_pos (I.X_pos i) _
    omega
  exact Nat.div_pos (Nat.le_of_dvd hr hdvd) hb

theorem diagonalMap_injective (I : Instance) (P : Parameters I) :
    Function.Injective (diagonalMap I P) := by
  intro v w h
  ext j
  have := congrArg (fun u : Vec (dimension I P) => u j) h
  change (diagonalFactor I P j : ℝ) * v j = (diagonalFactor I P j : ℝ) * w j at this
  have hp : (diagonalFactor I P j : ℝ) ≠ 0 := by
    exact_mod_cast (diagonalFactor_pos I P j).ne'
  exact mul_left_cancel₀ hp this

theorem scaled_isBasis (I : Instance) (P : Parameters I)
    (b : Fin (dimension I P) → Vec (dimension I P))
    (hb : IsBasisFor b (kernelLattice I P)) :
    IsBasisFor (fun j => diagonalMap I P (b j)) (scaledLattice I P) := by
  refine ⟨hb.1.map' (diagonalMap I P) (LinearMap.ker_eq_bot.2 (diagonalMap_injective I P)), ?_⟩
  have := hb.2
  unfold latticeOf at this ⊢
  unfold scaledLattice
  rw [← this, Submodule.map_span]
  congr 1
  ext x; simp

end DualCoppersmith.Dev.KB
end

section
set_option autoImplicit false

namespace DualCoppersmith.Dev.RootLine

open DualCoppersmith.Recovery LLLFactor.RedBasis

variable (I : Instance) (P : Parameters I)

theorem boundMonomial_pos (j : Fin (dimension I P)) : 0 < boundMonomial I P j := by
  unfold boundMonomial
  exact Finset.prod_pos fun i _ => pow_pos (I.X_pos i) _

theorem boundMonomial_dvd_rho (j : Fin (dimension I P)) : boundMonomial I P j ∣ rho I P :=
  Finset.dvd_lcm (Finset.mem_univ j)

theorem dimension_pos : 0 < dimension I P := by
  unfold dimension
  exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => ⟨0, by omega⟩, by simp⟩⟩

theorem rho_pos : 0 < rho I P := by
  have h : rho I P ≠ 0 := by
    intro h0
    obtain ⟨j, _, hj⟩ := (Finset.lcm_eq_zero_iff.mp h0)
    exact (boundMonomial_pos I P j).ne' hj
  omega

theorem exponent_constantIndex : exponent I P (constantIndex I P) = 0 := by
  ext i
  simp [exponent, constantIndex, multiIndex]

theorem exponent_linearIndex (i : Fin I.ell) :
    exponent I P (linearIndex I P i) = Finsupp.single i 1 := by
  ext k
  simp [exponent, linearIndex, multiIndex, Finsupp.single_apply, eq_comm]

theorem boundMonomial_constantIndex : boundMonomial I P (constantIndex I P) = 1 := by
  simp [boundMonomial, exponent_constantIndex]

theorem boundMonomial_linearIndex (i : Fin I.ell) :
    boundMonomial I P (linearIndex I P i) = I.X i := by
  simp [boundMonomial, exponent_linearIndex, Finsupp.single_apply]

theorem monomialRoot_constantIndex (r : Fin I.ell → ℤ) :
    monomialRoot I P r (constantIndex I P) = 1 := by
  simp [monomialRoot, exponent_constantIndex]

theorem monomialRoot_linearIndex (r : Fin I.ell → ℤ) (i : Fin I.ell) :
    monomialRoot I P r (linearIndex I P i) = r i := by
  simp [monomialRoot, exponent_linearIndex, Finsupp.single_apply]

theorem diagonalFactor_constantIndex : diagonalFactor I P (constantIndex I P) = rho I P := by
  simp [diagonalFactor, boundMonomial_constantIndex]

theorem rootVector_apply (r : Fin I.ell → ℤ) (j : Fin (dimension I P)) :
    rootVector I P r j = (diagonalFactor I P j : ℝ) * (monomialRoot I P r j : ℝ) := by
  rfl

theorem rootVector_constantIndex (r : Fin I.ell → ℤ) :
    rootVector I P r (constantIndex I P) = (rho I P : ℝ) := by
  rw [rootVector_apply, diagonalFactor_constantIndex, monomialRoot_constantIndex]
  simp

end DualCoppersmith.Dev.RootLine

namespace DualCoppersmith.Recovery

end DualCoppersmith.Recovery

end

section
set_option autoImplicit false

namespace DualCoppersmith.Dev.RR

open LLLFactor.RedBasis DualCoppersmith.Recovery DualCoppersmith.Dev.RootLine

theorem decode_eq (I : Instance) (P : Parameters I) (r : Fin I.ell → ℤ)
    (hr : IsBoundedRoot I r) (c : ℤ) (hc : c ≠ 0)
    (w : Vec (dimension I P)) (hw : w = c • rootVector I P r) :
    decode I P w = some r := by
  classical
  set z0 : Fin (dimension I P) → ℤ :=
    fun j => c * (diagonalFactor I P j : ℤ) * monomialRoot I P r j with hz0def
  have hz0 : ∀ j, (z0 j : ℝ) = w j := by
    intro j
    rw [hw]
    simp [hz0def, rootVector_apply]
    ring
  have hex : ∃ z : Fin (dimension I P) → ℤ, ∀ j, (z j : ℝ) = w j := ⟨z0, hz0⟩
  have hch : ∀ j, hex.choose j = z0 j := by
    intro j
    have h1 := hex.choose_spec j
    have h2 := hz0 j
    exact_mod_cast h1.trans h2.symm
  have hrat : rationalVector w = some (fun j => (z0 j : ℚ)) := by
    unfold rationalVector
    rw [dif_pos hex]
    congr 1
    funext j
    rw [hch j]
  have hρ : (rho I P : ℤ) ≠ 0 := by exact_mod_cast (rho_pos I P).ne'
  have hzc : z0 (constantIndex I P) = c * rho I P := by
    simp [hz0def, diagonalFactor_constantIndex, monomialRoot_constantIndex]
  have hzl : ∀ i, z0 (linearIndex I P i) = c * ((rho I P / I.X i : ℕ) : ℤ) * r i := by
    intro i
    simp only [hz0def, diagonalFactor, boundMonomial_linearIndex, monomialRoot_linearIndex]
  have hXpos : ∀ i, (0 : ℚ) < I.X i := fun i => by exact_mod_cast I.X_pos i
  have hdvd : ∀ i, ((rho I P / I.X i : ℕ) : ℚ) * (I.X i : ℚ) = (rho I P : ℚ) := by
    intro i
    have := boundMonomial_dvd_rho I P (linearIndex I P i)
    rw [boundMonomial_linearIndex] at this
    exact_mod_cast Nat.div_mul_cancel this
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hρq : (rho I P : ℚ) ≠ 0 := by exact_mod_cast (rho_pos I P).ne'
  have hci : ∀ i, (I.X i : ℚ) * (z0 (linearIndex I P i) : ℚ) / (z0 (constantIndex I P) : ℚ)
      = (r i : ℚ) := by
    intro i
    rw [hzc, hzl i]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hx := (hXpos i).ne'
    have hd : ((rho I P / I.X i : ℕ) : ℚ) ≠ 0 := by
      intro h0; apply hρq; rw [← hdvd i, h0, zero_mul]
    rw [← hdvd i]
    field_simp
  have hcex : ∃ r' : Fin I.ell → ℤ, ∀ i, (r' i : ℚ) =
      (I.X i : ℚ) * (z0 (linearIndex I P i) : ℚ) / (z0 (constantIndex I P) : ℚ) :=
    ⟨r, fun i => (hci i).symm⟩
  have hz0ne : z0 (constantIndex I P) ≠ 0 := by
    rw [hzc]; exact mul_ne_zero hc hρ
  have hchr : hcex.choose = r := by
    funext i
    have h1 := hcex.choose_spec i
    rw [hci i] at h1
    exact_mod_cast h1
  unfold decode
  rw [hrat]
  simp only [bind, Option.bind]
  have hz0neq : (z0 (constantIndex I P) : ℚ) ≠ 0 := by exact_mod_cast hz0ne
  rw [if_neg hz0neq, dif_pos hcex]
  simp only [hchr]
  rw [if_pos hr]

end DualCoppersmith.Dev.RR

namespace DualCoppersmith.Recovery

open LLLFactor.RedBasis DualCoppersmith.Dev.RootLine

theorem chk_root_recovery (I : Instance) (P : Parameters I)
    (delta : ℝ) (reduce : Reduction (dimension I P))
    (hreduce : ValidReduction I P delta reduce)
    (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r)
    (hgap : delta ^ (2 * (dimension I P - 1)) * (rho I P : ℝ) *
      Real.sqrt (dimension I P : ℝ) < secondMinimum (scaledLattice I P)) :
    algorithm2 I P reduce = some r := by
  classical
  have hn : 0 < dimension I P := dimension_pos I P
  have hex := DualCoppersmith.Dev.KB.exists_basis I P
  have hsel : selectBasis (kernelLattice I P) = some hex.choose := by
    unfold selectBasis; rw [dif_pos hex]
  set b := hex.choose with hbdef
  have hbb : IsBasisFor b (kernelLattice I P) := hex.choose_spec
  have hsb := DualCoppersmith.Dev.KB.scaled_isBasis I P b hbb
  have hcall := hreduce.2 b hsel
  have hdelta := hreduce.1
  set out := reduce (scaledBasis I P b) with houtdef
  have hsb' : IsBasisFor (scaledBasis I P b) (scaledLattice I P) := hsb
  have hout : IsBasisFor out (scaledLattice I P) := ⟨hcall.1.1, hcall.1.2.trans hsb'.2⟩
  have hfv := first_vector_bound hn (scaledLattice I P) (scaledBasis I P b) out hsb' delta hdelta hcall
  obtain ⟨hvr, hline, hnorm⟩ := root_line I P r hr
  set vr := rootVector I P r with hvrdef
  have hρ : (0 : ℝ) < rho I P := by exact_mod_cast rho_pos I P
  have hvr0 : vr ≠ 0 := by
    intro h0
    have := rootVector_constantIndex I P r
    rw [← hvrdef, h0] at this
    simp at this
    exact hρ.ne' this.symm
  have hlam : RegevLWE.SmoothingLB.lambda1 (scaledLattice I P) ≤ ‖vr‖ :=
    csInf_le ⟨0, by rintro _ ⟨v, _, _, rfl⟩; exact norm_nonneg _⟩ ⟨vr, hvr, hvr0, rfl⟩
  set B := delta ^ (2 * (dimension I P - 1)) * (rho I P : ℝ) *
      Real.sqrt (dimension I P : ℝ) with hB
  have hdp : (0 : ℝ) ≤ delta ^ (2 * (dimension I P - 1)) := by
    have : (0:ℝ) ≤ delta := by linarith
    positivity
  have hd1 : (1 : ℝ) ≤ delta ^ (2 * (dimension I P - 1)) := one_le_pow₀ hdelta
  have hw : ‖out ⟨0, hn⟩‖ ≤ B := by
    calc ‖out ⟨0, hn⟩‖ ≤ delta ^ (2 * (dimension I P - 1)) *
          RegevLWE.SmoothingLB.lambda1 (scaledLattice I P) := hfv
      _ ≤ delta ^ (2 * (dimension I P - 1)) * ‖vr‖ := mul_le_mul_of_nonneg_left hlam hdp
      _ ≤ delta ^ (2 * (dimension I P - 1)) * ((rho I P : ℝ) * Real.sqrt (dimension I P : ℝ)) :=
          mul_le_mul_of_nonneg_left hnorm hdp
      _ = B := by rw [hB]; ring
  have hvB : ‖vr‖ ≤ B := by
    calc ‖vr‖ ≤ (rho I P : ℝ) * Real.sqrt (dimension I P : ℝ) := hnorm
      _ ≤ delta ^ (2 * (dimension I P - 1)) * ((rho I P : ℝ) * Real.sqrt (dimension I P : ℝ)) :=
          le_mul_of_one_le_left (by positivity) hd1
      _ = B := by rw [hB]; ring
  set w := out ⟨0, hn⟩ with hwdef
  have hwL : w ∈ scaledLattice I P := by
    rw [← hout.2]; exact Submodule.subset_span ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    intro h0
    exact hout.1.ne_zero ⟨0, hn⟩ h0
  have hdep : ¬ LinearIndependent ℝ ![w, vr] := by
    intro hli
    have hBmem : B ∈ {R : ℝ | 0 ≤ R ∧ ∃ v : Fin 2 → Vec (dimension I P),
        LinearIndependent ℝ v ∧ ∀ j, v j ∈ scaledLattice I P ∧ ‖v j‖ ≤ R} := by
      refine ⟨le_trans (norm_nonneg _) hw, ![w, vr], hli, ?_⟩
      intro j
      fin_cases j
      · exact ⟨hwL, hw⟩
      · exact ⟨hvr, hvB⟩
    have : secondMinimum (scaledLattice I P) ≤ B :=
      csInf_le ⟨0, fun R hR => hR.1⟩ hBmem
    exact absurd hgap (not_lt.mpr this)
  obtain ⟨s, t, hst, hne⟩ : ∃ s t : ℝ, s • w + t • vr = 0 ∧ ¬ (s = 0 ∧ t = 0) := by
    by_contra hcon
    apply hdep
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_contra hne
    exact hcon ⟨s, t, hst, hne⟩
  have hs : s ≠ 0 := by
    intro hs0
    rw [hs0, zero_smul, zero_add] at hst
    have ht : t = 0 := by
      by_contra ht
      exact hvr0 ((smul_eq_zero.mp hst).resolve_left ht)
    exact hne ⟨hs0, ht⟩
  have hwc : w = (-t / s) • vr := by
    have h1 : s • w = -(t • vr) := eq_neg_of_add_eq_zero_left hst
    have h2 : w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [h2, h1, smul_neg, smul_smul, ← neg_smul]
    congr 1
    field_simp
  have hmem : w ∈ (scaledLattice I P : Set (Vec (dimension I P))) ∩
      Set.range (fun c : ℝ => c • vr) := ⟨hwL, _, hwc.symm⟩
  rw [hline] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hw0
    rw [← hk]; simp
  have hdec := DualCoppersmith.Dev.RR.decode_eq I P r hr k hk0 w hk.symm
  unfold algorithm2
  rw [hsel]
  simp only [bind, Option.bind]
  rw [dif_pos hn]
  exact hdec

end DualCoppersmith.Recovery
end

theorem solution : type_of% @DualCoppersmith.Recovery.chk_root_recovery := @DualCoppersmith.Recovery.chk_root_recovery
