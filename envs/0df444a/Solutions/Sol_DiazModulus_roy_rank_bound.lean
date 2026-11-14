-- Prove2me | solution 1 for DiazModulus.roy_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T09:52:25.085237+00:00
-- url     : https://prove2.me/submissions/e1828c72-5716-435e-a223-2663a53d05a6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_theorem_four
import Theorems.Thm_DiazModulus_roy_rational_adapted_basis
import Theorems.Thm_DiazModulus_multiplicityEstimateElem

open Complex ComplexConjugate

/-! # Roy's Corollary 1 in block form

Let `U` be the column space of `M` (`dim U = rank M = n`) and `Z` the `Q̄`-span of the columns, with a `Q̄`-basis
`z` (`ℓ = dim_Q̄ Z`); `z` lies in `U` and has coordinates in `ℒ̃`. Among the rational `S ≠ ℂ^d` (`⊥` is one, as
`d > 0`) pick `S` minimising `(n − u_S)/(d − s)` (finitely many values). `roy_theorem_four`, with
`multiplicityEstimateElem`, gives `ℓ'd' ≤ n'(d' + ℓ')` and `n'd ≤ n d'` for `d' = d − s`, `n' = n − u_S`,
`ℓ' = ℓ − dim_Q̄(Z ⊓ S)`, hence `dℓ' ≤ n(d' + ℓ')`. `P` is the matrix of `g` (adapted basis of `S`) followed
by a rotation of coordinates putting the `d'` coordinates `≥ s` on top, so the first `d'` rows of `P v` vanish
for `v ∈ S`. Let `K ≤ ℂ^l` be spanned by the algebraic `x` with `Mx ∈ S` (rational, `k = dim K`, `Mx ∈ S` on all
of `K`); `Q` is `h⁻¹` (adapted basis of `K`) after a rotation, so its last `l − k` columns lie in `K`: the
block `(PMQ)_{ij}` with `i < d'`, `j ≥ l − k` vanishes. Counting over `Q̄`: `{x ∈ Q̄^l : Mx ∈ S}` has dimension
`(l − ℓ) + dim(Z ⊓ S)` and embeds (through `h`) in the `Q̄`-span of `k` unit vectors, so `l − k ≤ ℓ'`; since
`n ≤ d`, `d(l − k) ≤ n(d' + l − k)`. -/

namespace RC1_RB
open DiazModulus

/-- A rational subspace: spanned by its vectors with algebraic coordinates. -/
abbrev IsRat {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) : Prop :=
  Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S

theorem isRat_span {d : ℕ} (X : Set (Fin d → ℂ)) (hX : ∀ v ∈ X, ∀ i, v i ∈ Qbar) :
    IsRat (Submodule.span ℂ X) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Submodule.subset_span hv, hX v hv⟩)

theorem isRat_bot {d : ℕ} : IsRat (⊥ : Submodule ℂ (Fin d → ℂ)) := by
  rw [← Submodule.span_empty]; exact isRat_span _ (by simp)

theorem exists_min_ratio {α : Type*} (C : α → Prop) (x y : α → ℕ) (N : ℕ)
    (hx : ∀ a, C a → x a ≤ N) (hy : ∀ a, C a → y a ≤ N) (hpos : ∀ a, C a → 0 < y a)
    (hne : ∃ a, C a) : ∃ a₀, C a₀ ∧ ∀ a, C a → x a₀ * y a ≤ x a * y a₀ := by
  classical
  let F : Finset (ℕ × ℕ) := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => ∃ a, C a ∧ x a = p.1 ∧ y a = p.2)
  have hmem : ∀ a, C a → (x a, y a) ∈ F := fun a ha =>
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := hx a ha; omega),
      Finset.mem_range.mpr (by have := hy a ha; omega)⟩, a, ha, rfl, rfl⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨p, hpF, hpmin⟩ := F.exists_min_image (fun p => (p.1 : ℚ) / p.2) ⟨_, hmem a ha⟩
  obtain ⟨a₀, ha₀, hx₀, hy₀⟩ := (Finset.mem_filter.mp hpF).2
  refine ⟨a₀, ha₀, fun b hb => ?_⟩
  have h := hpmin _ (hmem b hb)
  simp only [← hx₀, ← hy₀] at h
  rw [div_le_div_iff₀ (by exact_mod_cast hpos a₀ ha₀) (by exact_mod_cast hpos b hb)] at h
  exact_mod_cast h

/-- The rotation of `Fin m` taking `i < m - k` to `k + i` and `i ≥ m - k` to `i - (m - k)`. -/
def rotFun (m k : ℕ) (i : Fin m) : Fin m :=
  if h : i.val < m - k then ⟨k + i.val, by omega⟩ else ⟨i.val - (m - k), by omega⟩

theorem rotFun_inj (m k : ℕ) (hk : k ≤ m) : Function.Injective (rotFun m k) := by
  intro i j hij
  apply Fin.ext
  simp only [rotFun] at hij
  split_ifs at hij <;> simp only [Fin.mk.injEq] at hij <;> omega

noncomputable def rot (m k : ℕ) (hk : k ≤ m) : Fin m ≃ Fin m :=
  Equiv.ofBijective (rotFun m k) (Finite.injective_iff_bijective.mp (rotFun_inj m k hk))

theorem rot_lt (m k : ℕ) (hk : k ≤ m) (i : Fin m) (hi : i.val < m - k) :
    (rot m k hk i).val = k + i.val := by
  simp [rot, rotFun, hi]

theorem rot_ge (m k : ℕ) (hk : k ≤ m) (i : Fin m) (hi : m - k ≤ i.val) :
    (rot m k hk i).val = i.val - (m - k) := by
  simp [rot, rotFun, not_lt.mpr hi]

theorem single_qbar {m : ℕ} (j i : Fin m) : (Pi.single j (1 : ℂ) : Fin m → ℂ) i ∈ Qbar := by
  rw [Pi.single_apply]; split_ifs
  · exact Qbar.one_mem
  · exact Qbar.zero_mem

theorem finrank_comap_eq {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (p : Submodule K W) :
    Module.finrank K ↥(p.comap f) = Module.finrank K ↥(LinearMap.ker f) +
      Module.finrank K ↥(LinearMap.range f ⊓ p) := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict (p.comap f))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq, LinearMap.ker_domRestrict] at h
  rw [← h, (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap f)).finrank_eq, add_comm]

theorem arith_final {d n s ℓ' l' n' : ℕ} (hs : s < d) (hn : n ≤ d) (hl : l' ≤ ℓ')
    (hA : ℓ' * (d - s) ≤ n' * ((d - s) + ℓ')) (hB : n' * d ≤ n * (d - s)) :
    d * l' ≤ n * ((d - s) + l') := by
  have h1 : d * ℓ' ≤ n * ((d - s) + ℓ') := by
    have key : (d - s) * (d * ℓ') ≤ (d - s) * (n * ((d - s) + ℓ')) := by
      nlinarith [Nat.mul_le_mul_left d hA, Nat.mul_le_mul_right ((d - s) + ℓ') hB]
    exact Nat.le_of_mul_le_mul_left key (by omega)
  zify [hs.le] at h1 ⊢
  have hn' : (n : ℤ) ≤ d := by exact_mod_cast hn
  have hl' : (l' : ℤ) ≤ ℓ' := by exact_mod_cast hl
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hl')]

end RC1_RB

open DiazModulus RC1_RB in
theorem solution {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hd : 0 < d) :
    ∃ (d' l' : ℕ) (P : Matrix (Fin d) (Fin d) ℂ) (Q : Matrix (Fin l) (Fin l) ℂ),
      0 < d' ∧ d' ≤ d ∧ l' ≤ l ∧ IsUnit P.det ∧ IsUnit Q.det ∧
      (∀ i j, P i j ∈ Qbar) ∧ (∀ i j, Q i j ∈ Qbar) ∧
      (∀ (i : Fin d) (j : Fin l), i.val < d' → l' ≤ j.val → (P * M * Q) i j = 0) ∧
      d * l' ≤ M.rank * (d' + l') := by
  classical
  have hfr : ∀ {e : ℕ} (T : Submodule ℂ (Fin e → ℂ)), Module.finrank ℂ ↥T ≤ e :=
    fun T => (Submodule.finrank_le T).trans_eq (Module.finrank_fin_fun ℂ)
  have hlt : ∀ {e : ℕ} (T : Submodule ℂ (Fin e → ℂ)), T ≠ ⊤ → Module.finrank ℂ ↥T < e := by
    intro e T hT
    by_contra h
    exact hT (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact (hfr T).antisymm (by omega)))
  -- the column space `U` and the `Q̄`-span `Z` of the columns
  set U := LinearMap.range M.mulVecLin with hU
  have hUcol : U = Submodule.span ℂ (Set.range M.col) := Matrix.range_mulVecLin M
  set Zq : Submodule (↥Qbar) (Fin d → ℂ) := Submodule.span (↥Qbar) (Set.range M.col) with hZq
  have : FiniteDimensional (↥Qbar) ↥Zq := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  set b := Module.finBasis (↥Qbar) ↥Zq
  set z : Fin (Module.finrank (↥Qbar) ↥Zq) → Fin d → ℂ := fun k => (b k : Fin d → ℂ) with hz_def
  have hspan : Submodule.span (↥Qbar) (Set.range z) = Zq := by
    have : Set.range z = Zq.subtype '' Set.range b := by rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hZU : ∀ x ∈ Zq, x ∈ U := by
    have : Zq ≤ U.restrictScalars (↥Qbar) := Submodule.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      show M.col j ∈ U
      rw [hUcol]; exact Submodule.subset_span ⟨j, rfl⟩)
    exact fun x hx => this hx
  have hZL : ∀ x ∈ Zq, ∀ j, x j ∈ LogAlgTilde := by
    have : Zq ≤ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact Submodule.mem_pi.mpr (fun i _ => by rw [Matrix.col_apply]; exact hM i j))
    exact fun x hx j => Submodule.mem_pi.mp (this hx) j (Set.mem_univ j)
  have hzind : LinearIndependent (↥Qbar) z := b.linearIndependent.map' Zq.subtype (Submodule.ker_subtype Zq)
  -- a minimiser `S` of `(n − u_S)/(d − s)` over rational `S ≠ ⊤`
  have hbot : (⊥ : Submodule ℂ (Fin d → ℂ)) ≠ ⊤ := by
    intro h
    have := congrArg (fun T : Submodule ℂ (Fin d → ℂ) => Module.finrank ℂ ↥T) h
    simp only [finrank_bot, finrank_top, Module.finrank_fin_fun] at this
    omega
  obtain ⟨S, ⟨hSr, hStop⟩, hmin⟩ := exists_min_ratio
    (fun T : Submodule ℂ (Fin d → ℂ) => IsRat T ∧ T ≠ ⊤)
    (fun T => Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) (fun T => d - Module.finrank ℂ ↥T) d
    (fun T _ => by have := hfr U; omega) (fun T _ => by omega) (fun T hT => by have := hlt T hT.2; omega)
    ⟨⊥, isRat_bot, hbot⟩
  obtain ⟨hA, hB⟩ := DiazModulus.roy_theorem_four DiazModulus.multiplicityEstimateElem U z
    (fun k => hZU _ (b k).2) (fun k j => hZL _ (b k).2 j) hzind S hSr hStop
    (fun T hT hTtop => hmin T ⟨hT, hTtop⟩)
  rw [hspan] at hA
  have hs : Module.finrank ℂ ↥S < d := hlt S hStop
  -- the adapted basis of `S` gives `P`
  obtain ⟨g, hgQ, -, hgS⟩ := DiazModulus.roy_rational_adapted_basis S hSr
  -- the rational subspace `K` of `ℂ^l` spanned by algebraic `x` with `M x ∈ S`, and its adapted basis
  set KC : Submodule ℂ (Fin l → ℂ) := Submodule.span ℂ {x : Fin l → ℂ | (∀ j, x j ∈ Qbar) ∧ M.mulVec x ∈ S}
    with hKC
  have hKCS : ∀ x ∈ KC, M.mulVec x ∈ S := by
    have : KC ≤ S.comap M.mulVecLin := Submodule.span_le.mpr (fun x hx => hx.2)
    exact fun x hx => this hx
  obtain ⟨h, hhQ, -, hhK⟩ := DiazModulus.roy_rational_adapted_basis KC (isRat_span _ (fun v hv => hv.1))
  have hk : Module.finrank ℂ ↥KC ≤ l := hfr KC
  -- the dimension count: `dim_Q̄ {x ∈ Q̄^l : M x ∈ S} ≤ dim KC`
  let ε : (Fin l → ↥Qbar) →ₗ[↥Qbar] (Fin l → ℂ) := LinearMap.compLeft (Algebra.linearMap (↥Qbar) ℂ) (Fin l)
  let φ : (Fin l → ↥Qbar) →ₗ[↥Qbar] (Fin d → ℂ) := (M.mulVecLin.restrictScalars (↥Qbar)) ∘ₗ ε
  have hεs : ∀ j, ε (Pi.single j 1) = Pi.single j 1 := by
    intro j; ext i
    simp only [ε, LinearMap.compLeft_apply, Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have hφ : LinearMap.range φ = Zq := by
    rw [LinearMap.range_eq_map, ← (Pi.basisFun (↥Qbar) (Fin l)).span_eq, Submodule.map_span,
      ← Set.range_comp]
    congr 2; funext j
    simp only [Function.comp_apply, Pi.basisFun_apply, φ, LinearMap.coe_comp,
      LinearMap.restrictScalars_apply, hεs, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  have h1 := finrank_comap_eq φ (S.restrictScalars (↥Qbar))
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  rw [Module.finrank_fin_fun] at h2
  rw [hφ] at h1 h2
  set KQ := (S.restrictScalars (↥Qbar)).comap φ
  have h3 : Module.finrank (↥Qbar) ↥KQ ≤ Module.finrank ℂ ↥KC := by
    let ψ : (Fin l → ↥Qbar) →ₗ[↥Qbar] (Fin l → ℂ) := (h.toLinearMap.restrictScalars (↥Qbar)) ∘ₗ ε
    have hψ : Function.Injective ψ := h.injective.comp
      (fun x y hxy => funext fun j => Subtype.ext (congrFun hxy j))
    let W : Submodule (↥Qbar) (Fin l → ℂ) := Submodule.span (↥Qbar)
      (Set.range (fun i : Fin (Module.finrank ℂ ↥KC) => (Pi.single (Fin.castLE hk i) 1 : Fin l → ℂ)))
    have : FiniteDimensional (↥Qbar) ↥W := FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have hle : KQ.map ψ ≤ W := by
      rintro _ ⟨x, hx, rfl⟩
      have hεQ : ∀ j, ε x j ∈ Qbar := fun j => (x j).2
      have hvan : ∀ i : Fin l, Module.finrank ℂ ↥KC ≤ i.val → h (ε x) i = 0 :=
        (hhK _).mp (Submodule.subset_span ⟨hεQ, hx⟩)
      have hyQ : ∀ i, h (ε x) i ∈ Qbar := (hhQ _ hεQ).1
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨h (ε x) (Fin.castLE hk i), hyQ _⟩, ?_⟩
      ext j
      show _ = h (ε x) j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
      by_cases hj : j.val < Module.finrank ℂ ↥KC
      · rw [Finset.sum_eq_single (⟨j.val, hj⟩ : Fin _)]
        · rw [if_pos (show j = Fin.castLE hk ⟨j.val, hj⟩ from Fin.ext rfl)]
          show (h (ε x) (Fin.castLE hk ⟨j.val, hj⟩) : ℂ) * 1 = h (ε x) j
          rw [mul_one]; rfl
        · intro i _ hij
          rw [if_neg]
          intro he; apply hij; ext
          have := congrArg Fin.val he
          rw [Fin.val_castLE] at this
          show i.val = j.val
          omega
        · intro hn; exact absurd (Finset.mem_univ _) hn
      · rw [Finset.sum_eq_zero, hvan j (not_lt.mp hj)]
        intro i _
        rw [if_neg]
        intro he; apply hj; rw [he, Fin.val_castLE]; exact i.isLt
    calc Module.finrank (↥Qbar) ↥KQ = Module.finrank (↥Qbar) ↥(KQ.map ψ) :=
          (Submodule.equivMapOfInjective ψ hψ KQ).finrank_eq
      _ ≤ Module.finrank (↥Qbar) ↥W := Submodule.finrank_mono hle
      _ ≤ Module.finrank ℂ ↥KC := (finrank_range_le_card _).trans_eq (Fintype.card_fin _)
  have hl : l - Module.finrank ℂ ↥KC ≤
      Module.finrank (↥Qbar) ↥Zq - Module.finrank (↥Qbar) ↥(Zq ⊓ S.restrictScalars (↥Qbar)) := by
    omega
  -- the two algebraic matrices
  refine ⟨d - Module.finrank ℂ ↥S, l - Module.finrank ℂ ↥KC,
    LinearMap.toMatrix' ((g.trans (LinearEquiv.funCongrLeft ℂ ℂ (rot d _ hs.le))).toLinearMap),
    LinearMap.toMatrix' (((LinearEquiv.funCongrLeft ℂ ℂ (rot l _ hk).symm).trans h.symm).toLinearMap),
    by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' _
  · rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' _
  · intro i j
    rw [LinearMap.toMatrix'_apply]
    exact (hgQ _ (single_qbar j)).1 _
  · intro i j
    rw [LinearMap.toMatrix'_apply]
    exact (hhQ _ (fun i' => single_qbar j _)).2 _
  · intro i j hi hj
    have hmem : ((LinearEquiv.funCongrLeft ℂ ℂ (rot l _ hk).symm).trans h.symm) (Pi.single j 1) ∈ KC := by
      rw [hhK]
      intro i' hi'
      rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, Pi.single_apply, if_neg]
      intro he
      have h1 : rot l _ hk j = i' := by rw [← he]; exact Equiv.apply_symm_apply _ _
      have h2 := rot_ge l _ hk j (by omega)
      rw [h1] at h2
      omega
    have key : ∀ A : Matrix (Fin d) (Fin l) ℂ, A i j = (A.mulVec (Pi.single j 1)) i := fun A => by
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    refine (key _).trans ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply]
    exact (hgS _).mp (hKCS _ hmem) _ (by rw [rot_lt d _ hs.le i hi]; omega)
  · rw [Matrix.rank]
    exact arith_final hs (Matrix.rank_le_height M) hl hA hB
