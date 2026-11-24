-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_bidet_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:50.877429+00:00
-- url     : https://prove2.me/submissions/1d87adee-4506-4be4-9e7e-e52af3f3a085

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhM_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhM_full
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_initMinor
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_count_all
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhDet_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
private theorem lt_colH_iff_le_of_dominant {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Iio t := by
      intro m hm
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      linarith
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hsub : Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [mem_Iic] at hm
      simp only [mem_filter, mem_univ, true_and]
      exact le_trans h (hmu hm)
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
private theorem mapCoord_mvPolynomial_int (x : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ (GLCoord ℤ n) x) =
      algebraMap _ (GLCoord R n) (MvPolynomial.map (Int.castRingHom R) x) := by
  unfold mapCoord
  simp [IsLocalization.Away.lift]
private theorem exists_qhM_eq_smul_det {s : ℕ} (hs : s ≤ n) (J : ℕ → Fin n) :
    ∃ (S : Finset (Fin n)) (hS : S.card = s) (ε : R), qhM R s J =
      ε • algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)
        (Matrix.of fun a b : Fin s => genMat R n (Fin.castLE hs a) (S.orderEmbOfFin hS b)).det := by
  unfold qhM qhN
  rw [dif_pos hs]
  by_cases hJ : Function.Injective (fun q : Fin s => J q.val)
  · let S := univ.image (fun q : Fin s => J q.val)
    have hS : S.card = s := by
      rw [card_image_of_injective _ hJ]
      simp
    have hmem : ∀ b : Fin s, J b.val ∈ S := fun b => mem_image_of_mem _ (mem_univ b)
    let g : Fin s → Fin s := fun b => (S.orderIsoOfFin hS).symm ⟨J b.val, hmem b⟩
    have hg : ∀ b, S.orderEmbOfFin hS (g b) = J b.val := by
      intro b
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp only [g, OrderIso.apply_symm_apply]
    have ginj : Function.Injective g := by
      intro a b h
      apply hJ
      simp only
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin s) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)
    refine ⟨S, hS, ((Equiv.Perm.sign σ : ℤ) : R), ?_⟩
    have hM : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q.val)) =
        (Matrix.of fun a b : Fin s => genMat R n (Fin.castLE hs a) (S.orderEmbOfFin hS b)).submatrix id σ := by
      ext p q
      simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
      rw [show σ q = g q from rfl, hg q]
    rw [hM, Matrix.det_permute']
    simp [Algebra.smul_def, map_mul, map_intCast]
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hJ
    refine ⟨univ.map (Fin.castLEEmb hs), by simp, 0, ?_⟩
    have hz : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q.val)).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hab])
    simp only [hz, map_zero, zero_smul]
private theorem exists_equiv_comp_eq_of_card_filter_lt_eq {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ x, 0 < f x) (hg : ∀ y, 0 < g y)
    (h : ∀ t, (univ.filter fun x => t < f x).card = (univ.filter fun y => t < g y).card) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  have key : ∀ {γ : Type} [Fintype γ] (u : γ → ℕ) (v : ℕ), 0 < v →
      (univ.filter fun x => v - 1 < u x).card =
        (univ.filter fun x => u x = v).card + (univ.filter fun x => v < u x).card := by
    intro γ _ u v hv
    classical
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [disjoint_filter]
      intro x _ h1 h2
      omega
  have hfib : ∀ v, Fintype.card {x // f x = v} = Fintype.card {y // g y = v} := by
    intro v
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases Nat.eq_zero_or_pos v with hv | hv
    · subst hv
      rw [filter_false_of_mem (fun x _ => (hf x).ne'), filter_false_of_mem (fun y _ => (hg y).ne')]
      simp
    · have a := key f v hv
      have b := key g v hv
      rw [h (v - 1), h v] at a
      omega
  let e : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun v => Fintype.equivOfCardEq (hfib v)).trans (Equiv.sigmaFiberEquiv g))
  exact ⟨e, fun x => (Fintype.equivOfCardEq (hfib (f x)) ⟨x, rfl⟩).2⟩
private theorem mapCoord_card_eq_finsets {h : ℕ} (J S : Finset (Fin n)) (hJ : J.card = h) (hS : S.card = h) :
    mapCoord (n := n) R (minorC J S hJ hS) =
      algebraMap _ (GLCoord R n)
        (Matrix.of fun a b : Fin h => genMat R n (J.orderEmbOfFin hJ a) (S.orderEmbOfFin hS b)).det := by
  unfold minorC
  rw [mapCoord_mvPolynomial_int, RingHom.map_det]
  refine congrArg _ (congrArg Matrix.det ?_)
  ext a b
  simp [genMat]
private theorem orderEmbOfFin_canT_eq_castLE [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (canT mu c).2 (f := Fin.castLE (colH_le mu c))
    (fun x => by simp [canT]) (fun a b h => by rw [Fin.lt_def] at h ⊢; simpa using h)
  rw [← this]
private theorem mapCoord_intCast (m : ℤ) :
    mapCoord (n := n) R ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) =
      ((qhDet R n ^ m : (GLCoord R n)ˣ) : GLCoord R n) := by
  have hu : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [mapCoord_mvPolynomial_int, RingHom.map_det, genMat_map_coord]
  calc mapCoord (n := n) R ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)
      = ((Units.map (mapCoord (n := n) R).toMonoidHom (detU n ^ m) : (GLCoord R n)ˣ) : GLCoord R n) :=
        (Units.coe_map _ _).symm
    _ = ((qhDet R n ^ m : (GLCoord R n)ˣ) : GLCoord R n) := by rw [map_zpow, hu]
end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (k : ℕ) (hk : 0 ≤ mu (lastIdx n) + k)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ κ, sz κ ≤ n) (I : ∀ κ, Fin (sz κ) → Fin n)
    (hshape : ∀ t : Fin n, (Formalism.GradedWeylDivisibility.shapeDeg sz t : ℤ) = mu t + k) :
    ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) ∈
      Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) := by
  have h0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpos_c : ∀ c : ↥(TCols mu), 0 < colH mu c := by
    intro c
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have e0 : (⟨0, h0⟩ : Fin n) = 0 := Fin.ext (by simp)
    exact (lt_colH_iff_le_of_dominant hmu ⟨0, h0⟩ c.1).mpr (by rw [e0]; exact hc.2)
  obtain ⟨e, he⟩ := exists_equiv_comp_eq_of_card_filter_lt_eq (fun κ : {κ // 0 < sz κ} => sz κ.1)
    (Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c)) (fun κ => κ.2)
    (by
      intro y
      cases y with
      | inl _ => exact h0
      | inr c => exact hpos_c c)
    (qh_count_all hmu k hk sz hsz hshape)
  have hprod : algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) =
      ∏ κ, qhM R (sz κ) (fun q => if h : q < sz κ then I κ ⟨q, h⟩ else 0) := by
    unfold Formalism.GradedWeylDivisibility.bideterminant
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl (fun κ _ => qh_initMinor (I κ) (hsz κ))
  set F : Fin K → GLCoord R n := fun κ => qhM R (sz κ) (fun q => if h : q < sz κ then I κ ⟨q, h⟩ else 0)
    with hF
  have gen0 : ∀ s (J : ℕ → Fin n), s = 0 → qhM R s J = 1 := by
    intro s J hs
    rw [hs]
    exact qhM_zero J
  have hone : ∀ κ : {κ // ¬ 0 < sz κ}, F κ.1 = 1 := by
    intro κ
    have hz : sz κ.1 = 0 := by
      have := κ.2
      omega
    simp only [hF]
    exact gen0 _ _ hz
  have hsub : ∏ κ, F κ = ∏ κ : {κ // 0 < sz κ}, F κ.1 := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun κ => 0 < sz κ) F, Fintype.prod_eq_one _ hone, mul_one]
  have hre : ∏ κ : {κ // 0 < sz κ}, F κ.1 = ∏ y, F (e.symm y).1 :=
    Fintype.prod_equiv e _ _ (fun x => by simp)
  have hsz_l : ∀ i, sz (e.symm (Sum.inl i)).1 = n := by
    intro i
    have := he (e.symm (Sum.inl i))
    simp only [Equiv.apply_symm_apply, Sum.elim_inl] at this
    exact this.symm
  have hsz_r : ∀ c, sz (e.symm (Sum.inr c)).1 = colH mu c := by
    intro c
    have := he (e.symm (Sum.inr c))
    simp only [Equiv.apply_symm_apply, Sum.elim_inr] at this
    exact this.symm
  have hl : ∀ i, ∃ ε : R, F (e.symm (Sum.inl i)).1 = ε • (qhDet R n : GLCoord R n) := by
    intro i
    have gen : ∀ s (J : ℕ → Fin n), s = n → ∃ ε : R, qhM R s J = ε • (qhDet R n : GLCoord R n) := by
      intro s J hs
      rw [hs]
      exact qhM_full J
    simp only [hF]
    exact gen _ _ (hsz_l i)
  choose ε1 hε1 using hl
  have hr : ∀ c : ↥(TCols mu), ∃ (S : Finset (Fin n)) (hS : S.card = colH mu c) (ε : R),
      F (e.symm (Sum.inr c)).1 = ε • algebraMap _ (GLCoord R n)
        (Matrix.of fun a b : Fin (colH mu c) =>
          genMat R n (Fin.castLE (colH_le mu c) a) (S.orderEmbOfFin hS b)).det := by
    intro c
    have gen : ∀ s (J : ℕ → Fin n), s = colH mu c → ∃ (S : Finset (Fin n)) (hS : S.card = colH mu c) (ε : R),
        qhM R s J = ε • algebraMap _ (GLCoord R n)
          (Matrix.of fun a b : Fin (colH mu c) =>
            genMat R n (Fin.castLE (colH_le mu c) a) (S.orderEmbOfFin hS b)).det := by
      intro s J hs
      subst hs
      exact exists_qhM_eq_smul_det (colH_le mu c) J
    simp only [hF]
    exact gen _ _ (hsz_r c)
  choose S hS ε2 hε2 using hr
  let I' : TIdx mu := fun c => ⟨S c, hS c⟩
  have hbrk : mapCoord (n := n) R (brk mu I') =
      ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
        ∏ c : ↥(TCols mu), algebraMap _ (GLCoord R n)
          (Matrix.of fun a b : Fin (colH mu c) =>
            genMat R n (Fin.castLE (colH_le mu c) a) ((S c).orderEmbOfFin (hS c) b)).det := by
    unfold brk TMat
    rw [map_mul, map_prod, mapCoord_intCast]
    congr 1
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [mapCoord_card_eq_finsets]
    refine congrArg _ (congrArg Matrix.det ?_)
    ext a b
    simp only [Matrix.of_apply]
    rw [orderEmbOfFin_canT_eq_castLE]
  have hD : ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      (qhDet R n : GLCoord R n) ^ (mu (lastIdx n) + k).toNat =
      ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
    congr 2
    omega
  have hval : ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) =
      ((∏ i, ε1 i) * ∏ c, ε2 c) • mapCoord (n := n) R (brk mu I') := by
    rw [hprod, hsub, hre, Fintype.prod_sum_type, Finset.prod_congr rfl (fun i _ => hε1 i),
      Finset.prod_congr rfl (fun c _ => hε2 c), hbrk, ← hD]
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_mul, map_prod, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [hval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I', rfl⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
