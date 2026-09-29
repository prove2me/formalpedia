-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7c0d7aa7-1624-5af3-a8f9-276666dc3cb2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mOSEquiv

universe u

section General

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {g : ℕ} {τ : Type*}

theorem map_toPowerSeries (F : MvFormalGroup g R) (f : R →+* S) (i : Fin g) :
    (F.map f).toPowerSeries i = MvPowerSeries.map f (F.toPowerSeries i) := rfl

private theorem _root_.P2mOSEquiv.map_map (F : MvFormalGroup g R) (f : R →+* S) (f' : S →+* T) :
    (F.map f).map f' = F.map (f'.comp f) := by
  ext i d
  simp [map_toPowerSeries, MvPowerSeries.map_map]

p2m_export "P2mOSEquiv" "map_map"
private theorem _root_.P2mOSEquiv.map_id (F : MvFormalGroup g R) : F.map (RingHom.id R) = F := by
  ext i d
  simp [map_toPowerSeries]

p2m_export "P2mOSEquiv" "map_id"

theorem isComm_map (F : MvFormalGroup g R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm := by
  constructor
  intro i
  have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
    rintro (j | j) <;> simp [constantCoeff_X]
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  rw [map_subst (hasSubst_of_constantCoeff_zero hz)] at key
  have hfam : (fun s => MvPowerSeries.map f ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp
  rw [hfam] at key
  exact key

theorem map_subst_elim (F : MvFormalGroup g R) (f : R →+* S)
    {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin g) :
    MvPowerSeries.map f (subst (Sum.elim a b) (F.toPowerSeries i)) =
      subst (Sum.elim (fun j => MvPowerSeries.map f (a j)) fun j => MvPowerSeries.map f (b j))
        ((F.map f).toPowerSeries i) := by
  rw [map_subst (MvFormalGroup.hasSubst_elim ha hb), map_toPowerSeries]
  congr 1
  funext s
  rcases s with j | j <;> rfl

end General

section Dual

variable {k : Type u} [CommRing k] {τ : Type*}

local notation "𝔻" => DualNumber k
local notation "ιk" => TrivSqZeroExt.inlHom k k
set_option quotPrecheck false in
local notation "φk" => (TrivSqZeroExt.fstHom k k k).toRingHom

open DualNumber

theorem fst_comp_inl : (φk).comp (ιk) = RingHom.id k := by
  ext x
  rfl

def sndSeries (Ψ : MvPowerSeries τ (DualNumber k)) : MvPowerSeries τ k :=
  fun d => TrivSqZeroExt.snd (Ψ d)

theorem coeff_sndSeries (Ψ : MvPowerSeries τ 𝔻) (d : τ →₀ ℕ) :
    coeff d (sndSeries Ψ) = TrivSqZeroExt.snd (coeff d Ψ) := rfl

theorem map_fst_lift (q : MvPowerSeries τ k) :
    MvPowerSeries.map φk (MvPowerSeries.map ιk q) = q := by
  rw [MvPowerSeries.map_map, fst_comp_inl, MvPowerSeries.map_id]
  rfl

theorem coeff_eps_smul (Ψ : MvPowerSeries τ 𝔻) (d : τ →₀ ℕ) :
    coeff d ((ε : 𝔻) • Ψ) = ε * coeff d Ψ := rfl

theorem map_fst_eps_smul (Ψ : MvPowerSeries τ 𝔻) :
    MvPowerSeries.map φk ((ε : 𝔻) • Ψ) = 0 := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_map, coeff_eps_smul, map_mul]
  simp

theorem eps_smul_eps_smul (Ψ : MvPowerSeries τ 𝔻) : (ε : 𝔻) • (ε : 𝔻) • Ψ = 0 := by
  rw [smul_smul, eps_mul_eps, zero_smul]

theorem constantCoeff_lift (q : MvPowerSeries τ k) :
    (MvPowerSeries.map ιk q).constantCoeff = TrivSqZeroExt.inl q.constantCoeff :=
  constantCoeff_map _ _

theorem constantCoeff_eps_smul_lift {q : MvPowerSeries τ k} (hq : q.constantCoeff = 0) :
    ((ε : 𝔻) • MvPowerSeries.map ιk q).constantCoeff = 0 := by
  rw [constantCoeff_smul, constantCoeff_lift, hq]
  simp

theorem eq_lift_add_eps_smul (Ψ : MvPowerSeries τ 𝔻) :
    Ψ = MvPowerSeries.map ιk (MvPowerSeries.map φk Ψ) + (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries Ψ) := by
  refine MvPowerSeries.ext fun d => ?_
  rw [map_add, coeff_map, coeff_map, coeff_eps_smul, coeff_map, coeff_sndSeries]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem eq_eps_smul_of_map_fst_eq_zero {Ψ : MvPowerSeries τ 𝔻}
    (h : MvPowerSeries.map φk Ψ = 0) :
    Ψ = (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries Ψ) := by
  conv_lhs => rw [eq_lift_add_eps_smul Ψ, h, map_zero, zero_add]

theorem eq_of_eps_smul_lift_eq {a b : MvPowerSeries τ k}
    (h : (ε : 𝔻) • MvPowerSeries.map ιk a = (ε : 𝔻) • MvPowerSeries.map ιk b) : a = b := by
  refine MvPowerSeries.ext fun d => ?_
  have h' := congrArg (fun Ψ => TrivSqZeroExt.snd (coeff d Ψ)) h
  simpa [coeff_eps_smul, coeff_map] using h'

theorem eps_smul_subst_lift {σ : Type*} {a : σ → MvPowerSeries τ 𝔻} (ha : HasSubst a)
    {a₀ : σ → MvPowerSeries τ k} (h : ∀ s, MvPowerSeries.map φk (a s) = a₀ s)
    (q : MvPowerSeries σ k) :
    (ε : 𝔻) • subst a (MvPowerSeries.map ιk q) = (ε : 𝔻) • MvPowerSeries.map ιk (subst a₀ q) := by
  have hfst : MvPowerSeries.map φk (subst a (MvPowerSeries.map ιk q)) = subst a₀ q := by
    rw [map_subst ha, map_fst_lift]
    congr 1
    funext s
    exact h s
  conv_lhs => rw [eq_lift_add_eps_smul (subst a (MvPowerSeries.map ιk q)), hfst, smul_add,
    eps_smul_eps_smul, add_zero]

theorem map_lift_X {σ : Type*} (s : σ) :
    MvPowerSeries.map ιk (X s : MvPowerSeries σ k) = X s := map_X _ _

theorem lift_smul (a : k) (q : MvPowerSeries τ k) :
    MvPowerSeries.map ιk (a • q) = a • MvPowerSeries.map ιk q := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_map, coeff_smul]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

variable {n : ℕ} (F₀ : MvFormalGroup n k)

set_option quotPrecheck false in

local notation "L" => MvFormalGroup.map (TrivSqZeroExt.inlHom k k) F₀

scoped instance isComm_lift {F₀ : MvFormalGroup n k} [F₀.IsComm] :
    (MvFormalGroup.map (TrivSqZeroExt.inlHom k k) F₀).IsComm :=
  isComm_map F₀ _

theorem lift_toPowerSeries (i : Fin n) :
    (L).toPowerSeries i = MvPowerSeries.map ιk (F₀.toPowerSeries i) := rfl

theorem constantCoeff_L (j : Fin n) : ((L).toPowerSeries j).constantCoeff = 0 :=
  (L).constantCoeff_eq_zero j

theorem map_fst_L : (L).map φk = F₀ := by
  rw [map_map, fst_comp_inl, map_id]

def tr (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) :
    Fin n → MvPowerSeries (Fin n ⊕ Fin n) 𝔻 :=
  fun i => subst (Sum.elim (L).toPowerSeries
    fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) ((L).toPowerSeries i)

theorem tr_apply (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) (i : Fin n) :
    tr F₀ Γ i = subst (Sum.elim (L).toPowerSeries
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) ((L).toPowerSeries i) := rfl

theorem map_fst_subst_elim {w v : Fin n → MvPowerSeries τ 𝔻} {w₀ v₀ : Fin n → MvPowerSeries τ k}
    (hw : ∀ j, (w j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0)
    (hw₀ : ∀ j, MvPowerSeries.map φk (w j) = w₀ j) (hv₀ : ∀ j, MvPowerSeries.map φk (v j) = v₀ j)
    (i : Fin n) :
    MvPowerSeries.map φk (subst (Sum.elim w v) ((L).toPowerSeries i)) =
      subst (Sum.elim w₀ v₀) (F₀.toPowerSeries i) := by
  rw [map_subst_elim (L) φk hw hv i, map_fst_L]
  congr 1
  funext s
  rcases s with j | j
  · exact hw₀ j
  · exact hv₀ j

theorem map_fst_subst_elim_eps {w : Fin n → MvPowerSeries τ 𝔻} {w₀ : Fin n → MvPowerSeries τ k}
    (hw : ∀ j, (w j).constantCoeff = 0) (hw₀ : ∀ j, MvPowerSeries.map φk (w j) = w₀ j)
    (hw₀' : ∀ j, (w₀ j).constantCoeff = 0)
    {γ : Fin n → MvPowerSeries τ k} (hγ : ∀ l, (γ l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map φk (subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (γ l))
      ((L).toPowerSeries i)) = w₀ i := by
  rw [map_fst_subst_elim F₀ hw (fun l => constantCoeff_eps_smul_lift (hγ l)) hw₀
    (fun l => map_fst_eps_smul _) i]
  exact MvFormalGroup.subst_elim_zero_right F₀ hw₀' i

theorem map_fst_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map φk (tr F₀ Γ i) = F₀.toPowerSeries i :=
  map_fst_subst_elim_eps F₀ (constantCoeff_L F₀) (fun j => by rw [lift_toPowerSeries, map_fst_lift])
    F₀.constantCoeff_eq_zero hΓ i

theorem constantCoeff_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    (tr F₀ Γ i).constantCoeff = 0 :=
  MvFormalGroup.constantCoeff_subst_elim (L) (constantCoeff_L F₀)
    (fun l => constantCoeff_eps_smul_lift (hΓ l)) i

theorem eps_pow_eq_zero {m : ℕ} (hm : 2 ≤ m) : (ε : 𝔻) ^ m = 0 :=
  pow_eq_zero_of_le hm eps_pow_two

theorem finsuppProd_eps_smul_eq_zero {σ : Type*} (w : σ → MvPowerSeries τ 𝔻)
    {d : σ →₀ ℕ} (hd : 2 ≤ d.degree) :
    (d.prod fun s m => ((ε : 𝔻) • w s) ^ m) = 0 := by
  classical
  have h1 : (d.prod fun s m => ((ε : 𝔻) • w s) ^ m) =
      (d.prod fun s m => (MvPowerSeries.C (ε : 𝔻) : MvPowerSeries τ 𝔻) ^ m) *
        d.prod fun s m => (w s) ^ m := by
    unfold Finsupp.prod
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    show ((ε : 𝔻) • w s) ^ (d s) = (MvPowerSeries.C (ε : 𝔻)) ^ (d s) * (w s) ^ (d s)
    rw [smul_eq_C_mul, mul_pow]
  have h2 : (d.prod fun s m => (MvPowerSeries.C (ε : 𝔻) : MvPowerSeries τ 𝔻) ^ m) = 0 := by
    unfold Finsupp.prod
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, ← map_pow, eps_pow_eq_zero hd,
      map_zero]
  rw [h1, h2, zero_mul]

theorem subst_elim_eps_eps {u v : Fin n → MvPowerSeries τ k}
    (hu : ∀ j, (u j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0) (i : Fin n) :
    subst (Sum.elim (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j))
      fun j => (ε : 𝔻) • MvPowerSeries.map ιk (v j)) ((L).toPowerSeries i) =
      (ε : 𝔻) • MvPowerSeries.map ιk (u i + v i) := by
  classical
  set c : Fin n ⊕ Fin n → MvPowerSeries τ 𝔻 := Sum.elim
    (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j))
    fun j => (ε : 𝔻) • MvPowerSeries.map ιk (v j) with hc
  have hc0 : ∀ s, (c s).constantCoeff = 0 := by
    rintro (j | j)
    · exact constantCoeff_eps_smul_lift (hu j)
    · exact constantCoeff_eps_smul_lift (hv j)
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  set w : Fin n ⊕ Fin n → MvPowerSeries τ 𝔻 := Sum.elim
    (fun j => MvPowerSeries.map ιk (u j)) fun j => MvPowerSeries.map ιk (v j) with hw
  have hcw : ∀ s, c s = (ε : 𝔻) • w s := by
    rintro (j | j) <;> rfl
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_subst hsc,
    finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun s : Fin n ⊕ Fin n => Finsupp.single s 1) (fun d hd => ?_),
    Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective one_ne_zero hab)]
  · have hterm : ∀ s : Fin n ⊕ Fin n,
        coeff (Finsupp.single s 1) ((L).toPowerSeries i) •
          coeff e ((Finsupp.single s 1).prod fun s' m => (c s') ^ m) =
        coeff (Finsupp.single s 1) ((L).toPowerSeries i) * coeff e (c s) := by
      intro s
      rw [Finsupp.prod_single_index (h := fun s' m => (c s') ^ m) (pow_zero (c s)), pow_one,
        smul_eq_mul]
    simp only [hterm]
    rw [Fintype.sum_sum_type]
    simp only [lift_toPowerSeries, coeff_map, F₀.coeff_single_inl, F₀.coeff_single_inr]
    simp only [apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    show coeff e (c (Sum.inl i)) + coeff e (c (Sum.inr i)) = _
    rw [hc]
    simp only [Sum.elim_inl, Sum.elim_inr, map_add, smul_add]
  · by_contra hmem
    apply hd
    rcases Nat.lt_trichotomy d.degree 1 with hlt | heq | hgt
    · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      subst hd0
      rw [coeff_zero_eq_constantCoeff_apply, (L).constantCoeff_eq_zero i, zero_smul]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = d := by
        have hmem' : d ∈ {d' : Fin n ⊕ Fin n →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmem
    · have hz : (d.prod fun s' m => (c s') ^ m) = 0 := by
        have : (d.prod fun s' m => (c s') ^ m) = d.prod fun s' m => ((ε : 𝔻) • w s') ^ m :=
          Finsupp.prod_congr fun s' _ => by rw [hcw]
        rw [this]
        exact finsuppProd_eps_smul_eq_zero w (by omega)
      rw [hz, map_zero, smul_zero]

theorem subst_elim_eps_assoc [F₀.IsComm] {w : Fin n → MvPowerSeries τ 𝔻}
    (hw : ∀ j, (w j).constantCoeff = 0) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    (fun i => subst (Sum.elim (fun j => subst
        (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l)) ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries i)) =
    fun i => subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l + b l))
      ((L).toPowerSeries i) := by
  funext i
  rw [MvFormalGroup.subst_elim_assoc (L) hw (fun l => constantCoeff_eps_smul_lift (ha l))
    (fun l => constantCoeff_eps_smul_lift (hb l)) i]
  have hin : (fun j => subst (Sum.elim (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries j)) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l + b l) :=
    funext fun j => subst_elim_eps_eps F₀ ha hb j
  rw [hin]

theorem subst_translate {σ : Type*} {w : Fin n → MvPowerSeries τ 𝔻}
    (hw : ∀ j, (w j).constantCoeff = 0)
    {γ : Fin n → MvPowerSeries τ k} (hγ : ∀ l, (γ l).constantCoeff = 0)
    {s : τ → MvPowerSeries σ 𝔻} (hs : HasSubst s) {s₀ : τ → MvPowerSeries σ k}
    (hs₀ : ∀ t, MvPowerSeries.map φk (s t) = s₀ t) (i : Fin n) :
    subst s (subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (γ l))
      ((L).toPowerSeries i)) =
      subst (Sum.elim (fun j => subst s (w j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst s₀ (γ l))) ((L).toPowerSeries i) := by
  rw [MvFormalGroup.subst_subst_elim (L) hw (fun l => constantCoeff_eps_smul_lift (hγ l)) hs i]
  refine congrArg (fun c => subst (Sum.elim _ c) ((L).toPowerSeries i)) (funext fun l => ?_)
  rw [subst_smul hs, eps_smul_subst_lift hs hs₀]

theorem tr_zero (i : Fin n) :
    tr F₀ (fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) i = (L).toPowerSeries i := by
  rw [tr_apply]
  have hf : (fun _ : Fin n => (ε : 𝔻) • MvPowerSeries.map ιk (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) =
      fun _ => 0 := by
    funext l
    rw [map_zero, smul_zero]
  rw [hf]
  exact MvFormalGroup.subst_elim_zero_right (L) (constantCoeff_L F₀) i

set_option quotPrecheck false in
local notation "XL" => (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) (DualNumber k)))
set_option quotPrecheck false in
local notation "XR" => (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) (DualNumber k)))
set_option quotPrecheck false in
local notation "XLk" => (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
set_option quotPrecheck false in
local notation "XRk" => (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))

theorem subst_eps_smul_lift {m : ℕ} {u : Fin m → MvPowerSeries τ k}
    (hu : ∀ j, (u j).constantCoeff = 0) {q : MvPowerSeries (Fin m) k} (hq : q.constantCoeff = 0) :
    subst (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j)) (MvPowerSeries.map ιk q) =
      (ε : 𝔻) • MvPowerSeries.map ιk (∑ j, coeff (Finsupp.single j 1) q • u j) := by
  classical
  set c : Fin m → MvPowerSeries τ 𝔻 := fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j) with hc
  have hc0 : ∀ s, (c s).constantCoeff = 0 := fun j => constantCoeff_eps_smul_lift (hu j)
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  set w : Fin m → MvPowerSeries τ 𝔻 := fun j => MvPowerSeries.map ιk (u j) with hw
  have hcw : ∀ s, c s = (ε : 𝔻) • w s := fun _ => rfl
  have hce : ∀ s (e : τ →₀ ℕ), coeff e (c s) = (ε : 𝔻) * ιk (coeff e (u s)) := fun _ _ => rfl
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_subst hsc,
    finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun s : Fin m => Finsupp.single s 1) (fun d hd => ?_),
    Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective one_ne_zero hab)]
  · have hterm : ∀ s : Fin m,
        coeff (Finsupp.single s 1) (MvPowerSeries.map ιk q) •
          coeff e ((Finsupp.single s 1).prod fun s' m => (c s') ^ m) =
        (ε : 𝔻) * (ιk (coeff (Finsupp.single s 1) q) * ιk (coeff e (u s))) := by
      intro s
      rw [Finsupp.prod_single_index (h := fun s' m => (c s') ^ m) (pow_zero (c s)), pow_one,
        smul_eq_mul, hce, coeff_map]
      ring
    simp only [hterm]
    rw [← Finset.mul_sum]
    show _ = coeff e ((ε : 𝔻) • MvPowerSeries.map ιk (∑ j, coeff (Finsupp.single j 1) q • u j))
    rw [coeff_eps_smul, coeff_map]
    congr 1
    simp only [map_sum, coeff_smul, smul_eq_mul, map_mul]
  · by_contra hmem
    apply hd
    rcases Nat.lt_trichotomy d.degree 1 with hlt | heq | hgt
    · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      subst hd0
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_lift, hq, TrivSqZeroExt.inl_zero,
        zero_smul]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = d := by
        have hmem' : d ∈ {d' : Fin m →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmem
    · have hz : (d.prod fun s' m => (c s') ^ m) = 0 := by
        have : (d.prod fun s' m => (c s') ^ m) = d.prod fun s' m => ((ε : 𝔻) • w s') ^ m :=
          Finsupp.prod_congr fun s' _ => by rw [hcw]
        rw [this]
        exact finsuppProd_eps_smul_eq_zero w (by omega)
      rw [hz, map_zero, smul_zero]

theorem subst_hom_subst_elim {K : Type*} [CommRing K] {m : ℕ} (G : MvFormalGroup m K) {σ' : Type*}
    {ψ : Fin m → MvPowerSeries (Fin m) K} (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψG : ∀ i, subst G.toPowerSeries (ψ i) =
      subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin m ⊕ Fin m) K)) (ψ j))
        fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin m ⊕ Fin m) K)) (ψ j))
        (G.toPowerSeries i))
    {A B : Fin m → MvPowerSeries σ' K} (hA : ∀ j, (A j).constantCoeff = 0)
    (hB : ∀ j, (B j).constantCoeff = 0) (i : Fin m) :
    subst (fun s => subst (Sum.elim A B) (G.toPowerSeries s)) (ψ i) =
      subst (Sum.elim (fun j => subst A (ψ j)) fun j => subst B (ψ j)) (G.toPowerSeries i) := by
  have hAB : HasSubst (Sum.elim A B) := MvFormalGroup.hasSubst_elim hA hB
  have hXL : HasSubst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin m ⊕ Fin m) K)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin m ⊕ Fin m) K)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hin : HasSubst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin m ⊕ Fin m) K)) (ψ j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin m ⊕ Fin m) K)) (ψ j)) :=
    MvFormalGroup.hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXL (fun _ => constantCoeff_X _) (hψ0 j))
      (fun j => constantCoeff_subst_eq_zero hXR (fun _ => constantCoeff_X _) (hψ0 j))
  have key := congrArg (subst (Sum.elim A B)) (hψG i)
  rw [subst_comp_subst_apply G.hasSubst_toPowerSeries hAB, subst_comp_subst_apply hin hAB] at key
  rw [key]
  congr 1
  funext s
  rcases s with j | j
  · show subst (Sum.elim A B) (subst _ (ψ j)) = subst A (ψ j)
    rw [subst_comp_subst_apply hXL hAB]
    congr 1
    funext l
    exact subst_X hAB (Sum.inl l)
  · show subst (Sum.elim A B) (subst _ (ψ j)) = subst B (ψ j)
    rw [subst_comp_subst_apply hXR hAB]
    congr 1
    funext l
    exact subst_X hAB (Sum.inr l)

theorem lift_hom {φ₀ : Fin n → MvPowerSeries (Fin n) k} (hφ0 : ∀ i, (φ₀ i).constantCoeff = 0)
    (hφF : ∀ i, subst F₀.toPowerSeries (φ₀ i) =
      subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (F₀.toPowerSeries i))
    (i : Fin n) :
    subst (L).toPowerSeries (MvPowerSeries.map ιk (φ₀ i)) =
      subst (Sum.elim (fun j => subst XL (MvPowerSeries.map ιk (φ₀ j)))
        fun j => subst XR (MvPowerSeries.map ιk (φ₀ j))) ((L).toPowerSeries i) := by
  have hXL : HasSubst XLk := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst XRk := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hin : HasSubst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) :=
    MvFormalGroup.hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXL (fun _ => constantCoeff_X _) (hφ0 j))
      (fun j => constantCoeff_subst_eq_zero hXR (fun _ => constantCoeff_X _) (hφ0 j))
  have key := congrArg (MvPowerSeries.map ιk) (hφF i)
  rw [map_subst F₀.hasSubst_toPowerSeries, map_subst hin] at key
  have hl : (fun s => MvPowerSeries.map ιk (F₀.toPowerSeries s)) = (L).toPowerSeries := rfl
  rw [hl] at key
  rw [key, ← lift_toPowerSeries]
  congr 1
  funext s
  rcases s with j | j
  · show MvPowerSeries.map ιk (subst _ (φ₀ j)) = _
    rw [map_subst hXL]
    congr 1
    funext l
    exact map_X _ _
  · show MvPowerSeries.map ιk (subst _ (φ₀ j)) = _
    rw [map_subst hXR]
    congr 1
    funext l
    exact map_X _ _

theorem eq_of_translate_eq {w : Fin n → MvPowerSeries τ 𝔻} (hw : ∀ j, (w j).constantCoeff = 0)
    {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0)
    (h : ∀ i, subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l)) ((L).toPowerSeries i) =
      subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries i)) :
    a = b := by
  have hν : ∀ j, (MvFormalGroup.negSeries (L) w j).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_negSeries (L) _
  have key : ∀ (c : Fin n → MvPowerSeries τ k), (∀ l, (c l).constantCoeff = 0) → ∀ i,
      subst (Sum.elim (MvFormalGroup.negSeries (L) w) fun j =>
        subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (c l)) ((L).toPowerSeries j))
        ((L).toPowerSeries i) = (ε : 𝔻) • MvPowerSeries.map ιk (c i) := by
    intro c hc i
    have hεc : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (c l)).constantCoeff = 0 :=
      fun l => constantCoeff_eps_smul_lift (hc l)
    rw [← MvFormalGroup.subst_elim_assoc (L) hν hw hεc i]
    have hzero : (fun j => subst (Sum.elim (MvFormalGroup.negSeries (L) w) w)
        ((L).toPowerSeries j)) = fun _ => 0 :=
      funext fun j => MvFormalGroup.subst_elim_negSeries_left (L) hw j
    rw [hzero]
    exact MvFormalGroup.subst_elim_zero_left (L) hεc i
  funext i
  refine eq_of_eps_smul_lift_eq ?_
  rw [← key a ha i, ← key b hb i]
  congr 2
  exact funext h

theorem exists_eq_translate_lift {φ : Fin n → MvPowerSeries (Fin n) 𝔻}
    {φ₀ : Fin n → MvPowerSeries (Fin n) k}
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hφ₀0 : ∀ i, (φ₀ i).constantCoeff = 0)
    (hred : ∀ i, MvPowerSeries.map φk (φ i) = φ₀ i) :
    ∃ δ : Fin n → MvPowerSeries (Fin n) k, (∀ l, (δ l).constantCoeff = 0) ∧
      ∀ i, φ i = subst (Sum.elim (fun j => MvPowerSeries.map ιk (φ₀ j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (δ l)) ((L).toPowerSeries i) := by
  have hl0 : ∀ j, (MvPowerSeries.map ιk (φ₀ j)).constantCoeff = 0 := fun j => by
    rw [constantCoeff_lift, hφ₀0 j, TrivSqZeroExt.inl_zero]
  have hν0 : ∀ j, (MvFormalGroup.negSeries (L) (fun j => MvPowerSeries.map ιk (φ₀ j)) j).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_negSeries (L) _
  set t : Fin n → MvPowerSeries (Fin n) 𝔻 := fun j =>
    subst (Sum.elim (MvFormalGroup.negSeries (L) (fun j => MvPowerSeries.map ιk (φ₀ j))) φ)
      ((L).toPowerSeries j) with ht
  have ht0 : ∀ j, (t j).constantCoeff = 0 := MvFormalGroup.constantCoeff_subst_elim (L) hν0 hφ0

  have hνred : ∀ j, MvPowerSeries.map φk
      (MvFormalGroup.negSeries (L) (fun j => MvPowerSeries.map ιk (φ₀ j)) j) =
      MvFormalGroup.negSeries F₀ φ₀ j := by
    have h0 : ∀ j, (MvPowerSeries.map φk
        (MvFormalGroup.negSeries (L) (fun j => MvPowerSeries.map ιk (φ₀ j)) j)).constantCoeff = 0 :=
      fun j => by rw [constantCoeff_map, hν0 j, map_zero]
    have hrel : ∀ i, subst (Sum.elim φ₀ fun j => MvPowerSeries.map φk
        (MvFormalGroup.negSeries (L) (fun j => MvPowerSeries.map ιk (φ₀ j)) j))
        (F₀.toPowerSeries i) = 0 := by
      intro i
      have h := map_fst_subst_elim F₀ hl0 hν0 (fun j => map_fst_lift (φ₀ j)) (fun _ => rfl) i
      rw [MvFormalGroup.subst_elim_negSeries (L) hl0 i, map_zero] at h
      exact h.symm
    have huniq := MvFormalGroup.negSeries_unique F₀ hφ₀0 h0 hrel
    intro j
    exact congrFun huniq j
  have htred : ∀ j, MvPowerSeries.map φk (t j) = 0 := by
    intro j
    rw [ht, map_fst_subst_elim F₀ hν0 hφ0 hνred hred j]
    exact MvFormalGroup.subst_elim_negSeries_left F₀ hφ₀0 j
  refine ⟨fun j => sndSeries (t j), fun j => ?_, fun i => ?_⟩
  · have h := ht0 j
    rw [eq_eps_smul_of_map_fst_eq_zero (htred j)] at h
    rw [constantCoeff_smul, constantCoeff_lift] at h
    have h2 := congrArg TrivSqZeroExt.snd h
    simpa using h2
  · have hεg : (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries (t l))) = t :=
      funext fun l => (eq_eps_smul_of_map_fst_eq_zero (htred l)).symm
    rw [hεg, ht, ← MvFormalGroup.subst_elim_assoc (L) hl0 hν0 hφ0 i]
    have hzero : (fun j => subst (Sum.elim (fun j => MvPowerSeries.map ιk (φ₀ j))
        (MvFormalGroup.negSeries (L) (fun j => MvPowerSeries.map ιk (φ₀ j))))
        ((L).toPowerSeries j)) = fun _ => 0 :=
      funext fun j => MvFormalGroup.subst_elim_negSeries (L) hl0 j
    rw [hzero, MvFormalGroup.subst_elim_zero_left (L) hφ0 i]

theorem snd_coeff_translate_lift {φ₀ : Fin n → MvPowerSeries (Fin n) k}
    (hφ₀0 : ∀ i, (φ₀ i).constantCoeff = 0)
    {δ : Fin n → MvPowerSeries (Fin n) k} (hδ0 : ∀ l, (δ l).constantCoeff = 0) (l m : Fin n) :
    TrivSqZeroExt.snd (coeff (Finsupp.single m 1)
      (subst (Sum.elim (fun j => MvPowerSeries.map ιk (φ₀ j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (δ l)) ((L).toPowerSeries l))) =
      coeff (Finsupp.single m 1) (δ l) := by
  have hl0 : ∀ j, (MvPowerSeries.map ιk (φ₀ j)).constantCoeff = 0 := fun j => by
    rw [constantCoeff_lift, hφ₀0 j, TrivSqZeroExt.inl_zero]
  have hεδ : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (δ l)).constantCoeff = 0 :=
    fun l => constantCoeff_eps_smul_lift (hδ0 l)
  have hlin := MvFormalGroup.linearPart_subst_elim (L) hl0 hεδ
  have hl := congrFun (congrFun hlin l) m
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.add_apply] at hl
  rw [hl, coeff_map, coeff_eps_smul, coeff_map]
  simp

theorem engine_core [F₀.IsComm]
    {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : ∀ l, (Γ l).constantCoeff = 0)
    {φ₀ : Fin n → MvPowerSeries (Fin n) k} (hφ₀0 : ∀ i, (φ₀ i).constantCoeff = 0)
    (hφ₀F : ∀ i, subst F₀.toPowerSeries (φ₀ i) =
      subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (F₀.toPowerSeries i))
    {δ : Fin n → MvPowerSeries (Fin n) k} (hδ0 : ∀ l, (δ l).constantCoeff = 0)
    {φ : Fin n → MvPowerSeries (Fin n) 𝔻}
    (hφeq : ∀ i, φ i = subst (Sum.elim (fun j => MvPowerSeries.map ιk (φ₀ j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (δ l)) ((L).toPowerSeries i))
    (hφD : ∀ i, subst (tr F₀ Γ) (φ i) =
      subst (Sum.elim (fun j => subst XL (φ j)) fun j => subst XR (φ j)) (tr F₀ Γ i)) :
    ∀ l, (∑ i, coeff (Finsupp.single i 1) (φ₀ l) • Γ i) + subst F₀.toPowerSeries (δ l) =
        subst XLk (δ l) + subst XRk (δ l) +
        subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (Γ l) := by
  classical
  have hL0 := constantCoeff_L F₀
  have hl0 : ∀ j, (MvPowerSeries.map ιk (φ₀ j)).constantCoeff = 0 := fun j => by
    rw [constantCoeff_lift, hφ₀0 j, TrivSqZeroExt.inl_zero]
  have hφ0 : ∀ i, (φ i).constantCoeff = 0 := fun i => by
    rw [hφeq i]
    exact MvFormalGroup.constantCoeff_subst_elim (L) hl0
      (fun l => constantCoeff_eps_smul_lift (hδ0 l)) i
  have sXL : HasSubst XL := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have sXR : HasSubst XR := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have sXLk : HasSubst XLk := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have sXRk : HasSubst XRk := hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hεΓ : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (Γ l)).constantCoeff = 0 :=
    fun l => constantCoeff_eps_smul_lift (hΓ l)
  have hwL0 : ∀ m, (subst XL (MvPowerSeries.map ιk (φ₀ m))).constantCoeff = 0 :=
    fun m => constantCoeff_subst_eq_zero sXL (fun _ => constantCoeff_X _) (hl0 m)
  have hwR0 : ∀ m, (subst XR (MvPowerSeries.map ιk (φ₀ m))).constantCoeff = 0 :=
    fun m => constantCoeff_subst_eq_zero sXR (fun _ => constantCoeff_X _) (hl0 m)

  have hA20 : ∀ j, (subst (Sum.elim (fun m => subst XL (MvPowerSeries.map ιk (φ₀ m)))
      fun m => subst XR (MvPowerSeries.map ιk (φ₀ m))) ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hwL0 hwR0
  have hlamΓ0 : ∀ m, (∑ i, coeff (Finsupp.single i 1) (φ₀ m) • Γ i).constantCoeff = 0 := fun m => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [constantCoeff_smul, hΓ i, smul_zero]
  have hδF0 : ∀ l, (subst F₀.toPowerSeries (δ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero F₀.hasSubst_toPowerSeries F₀.constantCoeff_eq_zero (hδ0 l)
  have hδL0 : ∀ l, (subst XLk (δ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero sXLk (fun _ => constantCoeff_X _) (hδ0 l)
  have hδR0 : ∀ l, (subst XRk (δ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero sXRk (fun _ => constantCoeff_X _) (hδ0 l)
  have hφ₀L0 : ∀ j, (subst XLk (φ₀ j)).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero sXLk (fun _ => constantCoeff_X _) (hφ₀0 j)
  have hφ₀R0 : ∀ j, (subst XRk (φ₀ j)).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero sXRk (fun _ => constantCoeff_X _) (hφ₀0 j)
  have spΓ : HasSubst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) :=
    MvFormalGroup.hasSubst_elim hφ₀L0 hφ₀R0
  have hpΓ0 : ∀ l, (subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j))
      (Γ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero spΓ (by rintro (j | j); exacts [hφ₀L0 j, hφ₀R0 j]) (hΓ l)
  have hred' : ∀ i, MvPowerSeries.map φk (φ i) = φ₀ i := fun i => by
    rw [hφeq i]
    exact map_fst_subst_elim_eps F₀ hl0 (fun j => map_fst_lift (φ₀ j)) hφ₀0 hδ0 i
  have hD : HasSubst (tr F₀ Γ) := hasSubst_of_constantCoeff_zero (constantCoeff_tr F₀ hΓ)
  have hDred : ∀ i, MvPowerSeries.map φk (tr F₀ Γ i) = F₀.toPowerSeries i := map_fst_tr F₀ hΓ

  have hinnerL : ∀ j, subst (tr F₀ Γ) (MvPowerSeries.map ιk (φ₀ j)) =
      subst (Sum.elim
        (fun m => subst (Sum.elim (fun m => subst XL (MvPowerSeries.map ιk (φ₀ m)))
          fun m => subst XR (MvPowerSeries.map ιk (φ₀ m))) ((L).toPowerSeries m))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (∑ i, coeff (Finsupp.single i 1) (φ₀ l) • Γ i))
        ((L).toPowerSeries j) := by
    intro j
    have h1 := subst_hom_subst_elim (L) hl0 (lift_hom F₀ hφ₀0 hφ₀F)
      (A := (L).toPowerSeries) (B := fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) hL0 hεΓ j
    refine h1.trans ?_
    congr 1
    funext s
    rcases s with m | m
    · exact lift_hom F₀ hφ₀0 hφ₀F m
    · exact subst_eps_smul_lift hΓ (hφ₀0 m)
  have hLHS : ∀ i, subst (tr F₀ Γ) (φ i) =
      subst (Sum.elim
        (fun m => subst (Sum.elim (fun m => subst XL (MvPowerSeries.map ιk (φ₀ m)))
          fun m => subst XR (MvPowerSeries.map ιk (φ₀ m))) ((L).toPowerSeries m))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          ((∑ i, coeff (Finsupp.single i 1) (φ₀ l) • Γ i) + subst F₀.toPowerSeries (δ l)))
        ((L).toPowerSeries i) := by
    intro i
    rw [hφeq i]
    refine (subst_translate F₀ hl0 hδ0 hD hDred i).trans ?_
    refine (congrArg (fun a => subst (Sum.elim a fun l => (ε : 𝔻) • MvPowerSeries.map ιk
      (subst F₀.toPowerSeries (δ l))) ((L).toPowerSeries i)) (funext hinnerL)).trans ?_
    exact congrFun (subst_elim_eps_assoc F₀ hA20 hlamΓ0 hδF0) i

  have hPB0 : ∀ s, ((Sum.elim (fun j => subst XL (φ j)) fun j => subst XR (φ j)) s).constantCoeff = 0 := by
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero sXL (fun _ => constantCoeff_X _) (hφ0 j)
    · exact constantCoeff_subst_eq_zero sXR (fun _ => constantCoeff_X _) (hφ0 j)
  have sPB : HasSubst (Sum.elim (fun j => subst XL (φ j)) fun j => subst XR (φ j)) :=
    hasSubst_of_constantCoeff_zero hPB0
  have hPBred : ∀ s, MvPowerSeries.map φk ((Sum.elim (fun j => subst XL (φ j)) fun j => subst XR (φ j)) s) =
      (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) s := by
    rintro (j | j)
    · show MvPowerSeries.map φk (subst XL (φ j)) = subst XLk (φ₀ j)
      rw [map_subst sXL, hred' j]
      congr 1
      funext l
      exact map_X _ _
    · show MvPowerSeries.map φk (subst XR (φ j)) = subst XRk (φ₀ j)
      rw [map_subst sXR, hred' j]
      congr 1
      funext l
      exact map_X _ _
  have hXLred : ∀ l, MvPowerSeries.map φk ((XL) l) = (XLk) l := fun l => map_X _ _
  have hXRred : ∀ l, MvPowerSeries.map φk ((XR) l) = (XRk) l := fun l => map_X _ _
  have hεL : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (subst XLk (δ l))).constantCoeff = 0 :=
    fun l => constantCoeff_eps_smul_lift (hδL0 l)
  have hεR : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (subst XRk (δ l))).constantCoeff = 0 :=
    fun l => constantCoeff_eps_smul_lift (hδR0 l)
  have eL : (fun m => subst XL (φ m)) = fun m => subst (Sum.elim
      (fun j => subst XL (MvPowerSeries.map ιk (φ₀ j)))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst XLk (δ l))) ((L).toPowerSeries m) :=
    funext fun m => by
      rw [hφeq m]
      exact subst_translate F₀ hl0 hδ0 sXL hXLred m
  have eR : (fun m => subst XR (φ m)) = fun m => subst (Sum.elim
      (fun j => subst XR (MvPowerSeries.map ιk (φ₀ j)))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst XRk (δ l))) ((L).toPowerSeries m) :=
    funext fun m => by
      rw [hφeq m]
      exact subst_translate F₀ hl0 hδ0 sXR hXRred m
  have hinnerR : ∀ j, subst (Sum.elim (fun m => subst XL (φ m)) fun m => subst XR (φ m))
      ((L).toPowerSeries j) =
      subst (Sum.elim
        (fun m => subst (Sum.elim (fun m => subst XL (MvPowerSeries.map ιk (φ₀ m)))
          fun m => subst XR (MvPowerSeries.map ιk (φ₀ m))) ((L).toPowerSeries m))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst XLk (δ l) + subst XRk (δ l)))
        ((L).toPowerSeries j) := by
    intro j
    refine (congrArg₂ (fun a b => subst (Sum.elim a b) ((L).toPowerSeries j)) eL eR).trans ?_
    refine (MvFormalGroup.subst_elim_exchange (L) hwL0 hεL hwR0 hεR j).trans ?_
    exact congrArg (fun b => subst (Sum.elim _ b) ((L).toPowerSeries j))
      (funext fun m => subst_elim_eps_eps F₀ hδL0 hδR0 m)
  have hsum0 : ∀ l, (subst XLk (δ l) + subst XRk (δ l)).constantCoeff = 0 := fun l => by
    rw [map_add, hδL0 l, hδR0 l, add_zero]
  have hRHS : ∀ i, subst (Sum.elim (fun j => subst XL (φ j)) fun j => subst XR (φ j)) (tr F₀ Γ i) =
      subst (Sum.elim
        (fun m => subst (Sum.elim (fun m => subst XL (MvPowerSeries.map ιk (φ₀ m)))
          fun m => subst XR (MvPowerSeries.map ιk (φ₀ m))) ((L).toPowerSeries m))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst XLk (δ l) + subst XRk (δ l) +
            subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (Γ l)))
        ((L).toPowerSeries i) := by
    intro i
    refine (subst_translate F₀ hL0 hΓ sPB hPBred i).trans ?_
    refine (congrArg (fun a => subst (Sum.elim a fun l => (ε : 𝔻) • MvPowerSeries.map ιk
      (subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (Γ l)))
      ((L).toPowerSeries i)) (funext hinnerR)).trans ?_
    exact congrFun (subst_elim_eps_assoc F₀ hA20 hsum0 hpΓ0) i

  have hsumL : ∀ l, ((∑ i, coeff (Finsupp.single i 1) (φ₀ l) • Γ i) +
      subst F₀.toPowerSeries (δ l)).constantCoeff = 0 := fun l => by
    rw [map_add, hlamΓ0 l, hδF0 l, add_zero]
  have hsumR : ∀ l, (subst XLk (δ l) + subst XRk (δ l) +
      subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (Γ l)).constantCoeff = 0 :=
    fun l => by rw [map_add, hsum0 l, hpΓ0 l, add_zero]
  have hcmp := eq_of_translate_eq F₀ hA20 hsumL hsumR
    fun i => (hLHS i).symm.trans ((hφD i).trans (hRHS i))
  exact fun l => congrFun hcmp l

theorem engine [F₀.IsComm]
    {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : ∀ l, (Γ l).constantCoeff = 0)
    {φ₀ : Fin n → MvPowerSeries (Fin n) k} (hφ₀0 : ∀ i, (φ₀ i).constantCoeff = 0)
    (hφ₀F : ∀ i, subst F₀.toPowerSeries (φ₀ i) =
      subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (F₀.toPowerSeries i))
    {φ : Fin n → MvPowerSeries (Fin n) 𝔻} (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hred : ∀ i, MvPowerSeries.map φk (φ i) = φ₀ i)
    (hφD : ∀ i, subst (tr F₀ Γ) (φ i) =
      subst (Sum.elim (fun j => subst XL (φ j)) fun j => subst XR (φ j)) (tr F₀ Γ i)) :
    ∃ δ : Fin n → MvPowerSeries (Fin n) k, (∀ l, (δ l).constantCoeff = 0) ∧
      (∀ l m, coeff (Finsupp.single m 1) (δ l) =
        TrivSqZeroExt.snd (coeff (Finsupp.single m 1) (φ l))) ∧
      ∀ l, (∑ i, coeff (Finsupp.single i 1) (φ₀ l) • Γ i) + subst F₀.toPowerSeries (δ l) =
        subst XLk (δ l) + subst XRk (δ l) +
        subst (Sum.elim (fun j => subst XLk (φ₀ j)) fun j => subst XRk (φ₀ j)) (Γ l) := by
  obtain ⟨δ, hδ0, hφeq⟩ := exists_eq_translate_lift F₀ hφ0 hφ₀0 hred
  refine ⟨δ, hδ0, fun l m => ?_, engine_core F₀ hΓ hφ₀0 hφ₀F hδ0 hφeq hφD⟩
  rw [hφeq l]
  exact (snd_coeff_translate_lift F₀ hφ₀0 hδ0 l m).symm

end Dual

end P2mOSEquiv
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.P2mOSEquiv"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.P2mOSEquiv"

universe u

open MvPowerSeries

namespace P2mOSEquiv

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal"

theorem engine_OD {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i)))
    (φ₀ : Series k) (hφ₀ : IsLawHom X₀.F X₀.F φ₀)
    (φ : Series (DualNumber k)) (hφ : IsLawHom N.F N.F φ)
    (hred : ∀ i, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (φ i) = φ₀ i) :
    ∃ δ : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, (δ l).constantCoeff = 0) ∧
      (∀ l m, coeff (Finsupp.single m 1) (δ l) =
        TrivSqZeroExt.snd (coeff (Finsupp.single m 1) (φ l))) ∧
      ∀ l, (∑ i, coeff (Finsupp.single i 1) (φ₀ l) • Γ i) + subst X₀.F.toPowerSeries (δ l) =
        subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (δ l) +
        subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (δ l) +
        subst (Sum.elim
          (fun j => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ₀ j))
          fun j => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ₀ j))
          (Γ l) := by
  haveI := X₀.isComm
  have hNF : N.F.toPowerSeries = tr X₀.F Γ := funext fun i => hNΓ i
  have hφD : ∀ i, subst (tr X₀.F Γ) (φ i) =
      subst (Sum.elim
        (fun j => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) (DualNumber k))) (φ j))
        fun j => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) (DualNumber k))) (φ j))
        (tr X₀.F Γ i) := by
    intro i
    have h := hφ.2 i
    rw [hNF] at h
    exact h
  exact engine X₀.F (fun l => (hΓ l).constantCoeff_eq_zero) hφ₀.1 hφ₀.2 hφ.1 hred hφD

theorem map_varpi_of_map_eq {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule) (i : Fin 2) :
    MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (N.varpi i) = X₀.varpi i :=
  congrFun (congrArg FormalODModule.varpi hN) i

theorem map_act_of_map_eq {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule) (a : Zp2 q)
    (i : Fin 2) :
    MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (N.act a i) = X₀.act a i :=
  congrFun (congrFun (congrArg FormalODModule.act hN) a) i

theorem orient {k : Type u} [Field k] (F : MvFormalGroup 2 k)
    {lam pΓ : MvPowerSeries (Fin 2 ⊕ Fin 2) k} {δ : MvPowerSeries (Fin 2) k}
    (h : lam + subst F.toPowerSeries δ =
      subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) δ +
      subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) δ + pΓ) :
    lam = pΓ + F.addCoboundary (-δ) ∧ pΓ = lam + F.addCoboundary δ := by
  have hXL : HasSubst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hXR : HasSubst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have n1 : subst F.toPowerSeries (-δ) = - subst F.toPowerSeries δ := by
    rw [← coe_substAlgHom F.hasSubst_toPowerSeries, map_neg]
  have n2 : subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (-δ) =
      - subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) δ := by
    rw [← coe_substAlgHom hXL, map_neg]
  have n3 : subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (-δ) =
      - subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) δ := by
    rw [← coe_substAlgHom hXR, map_neg]
  unfold MvFormalGroup.addCoboundary
  rw [n1, n2, n3]
  constructor
  · linear_combination h
  · linear_combination (-1 : MvPowerSeries (Fin 2 ⊕ Fin 2) k) * h

end P2mOSEquiv
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.P2mOSEquiv"

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule FormalODModule.varpi FormalODModule.act" namespace FormalODModule p2m_export "CerednikDrinfeld.FormalODModule" "map map_id map_map F varpi isLawHom_act isComm act isLawHom_varpi" end CerednikDrinfeld.FormalODModule
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.exists_sum_linearPart_act_smul_eq_subst_act_add_addCoboundary
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∀ a : Zp2 q, ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
      ∀ l, ∑ i, MvFormalGroup.linearPart (X₀.act a) l i • Γ i =
        pull (X₀.act a) (Γ l) + X₀.F.addCoboundary (g l) := by
  intro pull a
  obtain ⟨δ, hδ0, -, heq⟩ := P2mOSEquiv.engine_OD X₀ N Γ hΓ hNΓ (X₀.act a) (X₀.isLawHom_act a)
    (N.act a) (N.isLawHom_act a) (P2mOSEquiv.map_act_of_map_eq X₀ N hN a)
  refine ⟨fun l => -δ l, fun l => by rw [map_neg, hδ0 l, neg_zero], fun l => ?_⟩
  exact (P2mOSEquiv.orient X₀.F (heq l)).1

p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
      ∀ l, ∑ i, MvFormalGroup.linearPart X₀.varpi l i • Γ i =
        pull X₀.varpi (Γ l) + X₀.F.addCoboundary (g l) := by
  intro pull
  obtain ⟨δ, hδ0, -, heq⟩ := P2mOSEquiv.engine_OD X₀ N Γ hΓ hNΓ X₀.varpi X₀.isLawHom_varpi
    N.varpi N.isLawHom_varpi (P2mOSEquiv.map_varpi_of_map_eq X₀ N hN)
  refine ⟨fun l => -δ l, fun l => by rw [map_neg, hδ0 l, neg_zero], fun l => ?_⟩
  exact (P2mOSEquiv.orient X₀.F (heq l)).1

p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in
open MvPowerSeries _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
      (∀ l, pull X₀.varpi (Γ l) =
        ∑ i, MvFormalGroup.linearPart X₀.varpi l i • Γ i + X₀.F.addCoboundary (g l)) ∧
      (∀ l m, MvPowerSeries.coeff (Finsupp.single m 1) (g l) =
        TrivSqZeroExt.snd (MvFormalGroup.linearPart N.varpi l m)) := by
  intro pull
  obtain ⟨δ, hδ0, hlin, heq⟩ := P2mOSEquiv.engine_OD X₀ N Γ hΓ hNΓ X₀.varpi X₀.isLawHom_varpi
    N.varpi N.isLawHom_varpi (P2mOSEquiv.map_varpi_of_map_eq X₀ N hN)
  refine ⟨δ, hδ0, fun l => ?_, fun l m => hlin l m⟩
  exact (P2mOSEquiv.orient X₀.F (heq l)).2

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
      ∀ l, ∑ i, MvFormalGroup.linearPart X₀.varpi l i • Γ i =
        pull X₀.varpi (Γ l) + X₀.F.addCoboundary (g l) := by
  exact CerednikDrinfeld.FormalODModule.exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary X₀ N hN Γ hΓ hNΓ

end S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary (solution)
