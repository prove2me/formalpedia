-- Prove2me | solution 1 for BernsteinSzego
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:44:53.171069+00:00
-- url     : https://prove2.me/submissions/09e56d6a-af81-46fc-a5bc-394ae13175bd

module
public import Definitions.Def_PHarmonicPoly_TrigPolyZeroCount
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_InteriorZeroOfSignChange
public import Definitions.Def_PHarmonicPoly_AngleOfUnitCirclePoint
public import Definitions.Def_PHarmonicPoly_BernsteinSzego
public import Theorems.Thm_AngleOfUnitCirclePoint
public import Theorems.Thm_InteriorZeroOfSignChange
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolySmooth
public import Theorems.Thm_TrigPolyZeroCount


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) :
    ∀ t : ℝ, (T t) ^ 2 + (deriv T t) ^ 2 / (m : ℝ) ^ 2 ≤ 1 := by
  -- basic facts about T and m
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hTC1 : ContDiff ℝ 1 T := (TrigPolySmooth hT).of_le le_top
  have hTd : Differentiable ℝ T := hTC1.differentiable (by norm_num)
  intro ts
  by_contra hcon
  rw [not_le] at hcon
  -- λ
  have hqnn : 0 ≤ T ts ^ 2 + deriv T ts ^ 2 / (m : ℝ) ^ 2 := by positivity
  set lam : ℝ := Real.sqrt (T ts ^ 2 + deriv T ts ^ 2 / (m : ℝ) ^ 2) with hlamdef
  have hlamsq : lam ^ 2 = T ts ^ 2 + deriv T ts ^ 2 / (m : ℝ) ^ 2 := Real.sq_sqrt hqnn
  have hlamnn : 0 ≤ lam := Real.sqrt_nonneg _
  have hlam1 : 1 < lam := by nlinarith [hlamsq, hcon, hlamnn]
  have hlampos : 0 < lam := by linarith
  -- phase α
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  have hlamsq' : lam ^ 2 * (m : ℝ) ^ 2 = T ts ^ 2 * (m : ℝ) ^ 2 + deriv T ts ^ 2 := by
    field_simp at hlamsq
    linarith [hlamsq]
  obtain ⟨α, hcosa, hsina⟩ := AngleOfUnitCirclePoint (T ts / lam) (-(deriv T ts) / (lam * (m : ℝ))) (by
    field_simp
    linarith [hlamsq'])
  have hTts : T ts = lam * Real.cos α := by
    rw [hcosa]; field_simp
  have hTdts : deriv T ts = -(lam * (m : ℝ) * Real.sin α) := by
    rw [hsina]; field_simp
  -- S and D
  set S : ℝ → ℝ := fun t => lam * Real.cos ((m : ℝ) * (t - ts) + α) with hSdef
  set D : ℝ → ℝ := fun t => S t - T t with hDdef
  -- Step 2a
  have hSTP : TrigPolyLe m S := by
    refine ⟨fun k => if k = m then lam * Real.cos (α - (m : ℝ) * ts) else 0,
      fun k => if k = m then -(lam * Real.sin (α - (m : ℝ) * ts)) else 0, ?_⟩
    intro t
    rw [Finset.sum_eq_single_of_mem m (Finset.self_mem_range_succ m)
      (fun k _ hk => by simp [hk])]
    simp only [hSdef]
    rw [show (m : ℝ) * (t - ts) + α = (m : ℝ) * t + (α - (m : ℝ) * ts) by ring, Real.cos_add]
    simp only [if_true]
    ring
  -- Step 2b
  have hDTP : TrigPolyLe m D := by
    have h := TrigPolyLinComb hSTP hT 1 (-1)
    have heq : (fun t => (1 : ℝ) * S t + (-1) * T t) = D := by
      funext t; rw [hDdef]; ring
    rwa [heq] at h
  -- Step 2c: derivatives of S and D
  have hSderiv : ∀ t : ℝ, HasDerivAt S (-(lam * (m : ℝ) * Real.sin ((m : ℝ) * (t - ts) + α))) t := by
    intro t
    have hg : HasDerivAt (fun r : ℝ => (m : ℝ) * (r - ts) + α) (m : ℝ) t := by
      have h0 : HasDerivAt (fun r : ℝ => (m : ℝ) * (r - ts) + α) ((m : ℝ) * 1) t :=
        (((hasDerivAt_id t).sub_const ts).const_mul (m : ℝ)).add_const α
      simpa using h0
    have h : HasDerivAt (fun r : ℝ => Real.cos ((m : ℝ) * (r - ts) + α))
        (-Real.sin ((m : ℝ) * (t - ts) + α) * (m : ℝ)) t :=
      hg.cos
    have h2 : HasDerivAt (fun r : ℝ => lam * Real.cos ((m : ℝ) * (r - ts) + α))
        (lam * (-Real.sin ((m : ℝ) * (t - ts) + α) * (m : ℝ))) t := h.const_mul lam
    have heq : lam * (-Real.sin ((m : ℝ) * (t - ts) + α) * (m : ℝ))
        = -(lam * (m : ℝ) * Real.sin ((m : ℝ) * (t - ts) + α)) := by ring
    rw [hSdef]
    exact heq ▸ h2
  have hDderiv : ∀ t : ℝ,
      deriv D t = -(lam * (m : ℝ) * Real.sin ((m : ℝ) * (t - ts) + α)) - deriv T t := by
    intro t
    rw [hDdef]
    exact (((hSderiv t).sub (hTd t).hasDerivAt).deriv)
  -- Step 2d
  have hD0 : D ts = 0 := by
    rw [hDdef, hSdef]
    simp only [sub_self, mul_zero, zero_add]
    rw [hTts]; ring
  have hD'0 : deriv D ts = 0 := by
    rw [hDderiv ts]
    simp only [sub_self, mul_zero, zero_add]
    rw [hTdts]
    ring
  -- continuity
  have hDcont : Continuous D := by
    simp only [hDdef, hSdef]
    refine Continuous.sub ?_ hTd.continuous
    refine continuous_const.mul (Real.continuous_cos.comp ?_)
    exact (continuous_const.mul (continuous_id.sub continuous_const)).add continuous_const
  -- Step 3: alternation points
  set τ : ℤ → ℝ := fun j => ts + ((j : ℝ) * Real.pi - α) / (m : ℝ) with hτdef
  have hdivlt : ∀ a b : ℝ, a < b → a / (m : ℝ) < b / (m : ℝ) := by
    intro a b hab
    have h := mul_lt_mul_of_pos_right hab (inv_pos.mpr hmR)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linarith [h]
  have hτmono : StrictMono τ := by
    intro i j hij
    have hiR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    simp only [hτdef]
    have hnum : (i : ℝ) * Real.pi - α < (j : ℝ) * Real.pi - α := by
      nlinarith [Real.pi_pos]
    linarith [hdivlt _ _ hnum]
  have hτper : ∀ j : ℤ, τ (j + 2 * (m : ℤ)) = τ j + 2 * Real.pi := by
    intro j
    simp only [hτdef]
    push_cast
    field_simp
    ring
  have hSτ : ∀ j : ℤ, S (τ j) = lam * (-1 : ℝ) ^ (j : ℤ) := by
    intro j
    simp only [hSdef, hτdef]
    rw [show (m : ℝ) * (ts + ((j : ℝ) * Real.pi - α) / (m : ℝ) - ts) + α = (j : ℝ) * Real.pi by
      field_simp; ring]
    rw [Real.cos_int_mul_pi]
  -- the sign ε j = (-1)^j
  have hepssq : ∀ j : ℤ, ((-1 : ℝ) ^ (j : ℤ)) * ((-1 : ℝ) ^ (j : ℤ)) = 1 := by
    intro j
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [← two_mul]
    rw [zpow_mul]
    norm_num
  have hepscases : ∀ j : ℤ, (-1 : ℝ) ^ (j : ℤ) = 1 ∨ (-1 : ℝ) ^ (j : ℤ) = -1 := by
    intro j
    have h := hepssq j
    rcases mul_self_eq_one_iff.mp (by linarith [h] : ((-1 : ℝ) ^ (j : ℤ)) * ((-1 : ℝ) ^ (j : ℤ)) = 1) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hepssucc : ∀ j : ℤ, (-1 : ℝ) ^ (j + 1 : ℤ) = -((-1 : ℝ) ^ (j : ℤ)) := by
    intro j
    rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    ring
  -- Step 3: the alternation bound, in the two sign cases
  have halt : ∀ j : ℤ, (((-1 : ℝ) ^ (j : ℤ) = 1) → lam - 1 ≤ D (τ j))
      ∧ (((-1 : ℝ) ^ (j : ℤ) = -1) → D (τ j) ≤ -(lam - 1)) := by
    intro j
    have hb := hbd (τ j)
    rw [abs_le] at hb
    constructor
    · intro h1
      simp only [hDdef]
      rw [hSτ j, h1]
      linarith [hb.2]
    · intro h1
      simp only [hDdef]
      rw [hSτ j, h1]
      linarith [hb.1]
  have hDτne : ∀ j : ℤ, D (τ j) ≠ 0 := by
    intro j
    rcases hepscases j with h1 | h1
    · have := (halt j).1 h1; intro h; rw [h] at this; linarith
    · have := (halt j).2 h1; intro h; rw [h] at this; linarith
  have hsignalt : ∀ j : ℤ, D (τ j) * D (τ (j + 1)) < 0 := by
    intro j
    rcases hepscases j with h1 | h1
    · have hA := (halt j).1 h1
      have hB := (halt (j + 1)).2 (by rw [hepssucc j, h1])
      nlinarith [hA, hB]
    · have hA := (halt j).2 h1
      have hB := (halt (j + 1)).1 (by rw [hepssucc j, h1]; norm_num)
      nlinarith [hA, hB]
  -- Step 4: locate ts
  set j0 : ℤ := ⌊α / Real.pi⌋ with hj0def
  have hpi := Real.pi_pos
  have hτj0le : τ j0 ≤ ts := by
    simp only [hτdef]
    have h := Int.floor_le (α / Real.pi)
    rw [hj0def]
    have h2 : (⌊α / Real.pi⌋ : ℝ) * Real.pi ≤ α := by
      have := mul_le_mul_of_nonneg_right h hpi.le
      rwa [div_mul_cancel₀ α (ne_of_gt hpi)] at this
    have h3 : ((⌊α / Real.pi⌋ : ℝ) * Real.pi - α) / (m : ℝ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hmR.le
    linarith
  have hτj0lt : ts < τ (j0 + 1) := by
    simp only [hτdef]
    have h := Int.lt_floor_add_one (α / Real.pi)
    rw [hj0def]
    have h2 : α < ((⌊α / Real.pi⌋ : ℝ) + 1) * Real.pi := by
      have := mul_lt_mul_of_pos_right h hpi
      rwa [div_mul_cancel₀ α (ne_of_gt hpi)] at this
    have h3 : 0 < (((j0 + 1 : ℤ) : ℝ) * Real.pi - α) / (m : ℝ) := by
      apply div_pos (by rw [hj0def]; push_cast; linarith) hmR
    linarith
  have hts1 : τ j0 < ts := by
    rcases lt_or_eq_of_le hτj0le with h | h
    · exact h
    · exact absurd (h ▸ hD0 : D (τ j0) = 0) (hDτne j0)
  -- Step 5: the zeros
  have hivtall : ∀ j : ℤ, ∃ z, τ j < z ∧ z < τ (j + 1) ∧ D z = 0 :=
    fun j => InteriorZeroOfSignChange D hDcont (τ j) (τ (j + 1)) (hτmono (lt_add_one j)) (hsignalt j)
  choose ζ hζ1 hζ2 hζ3 using hivtall
  have hζmono : StrictMono ζ := by
    intro i j hij
    calc ζ i < τ (i + 1) := hζ2 i
      _ ≤ τ j := (hτmono.monotone (by omega))
      _ < ζ j := hζ1 j
  set Z : Finset ℝ := (Finset.Icc (j0 + 1) (j0 + 2 * (m : ℤ) - 1)).image ζ with hZdef
  have hZcard : Z.card = 2 * m - 1 := by
    rw [hZdef, Finset.card_image_of_injective _ hζmono.injective]
    simp
    omega
  have hZmem : ∀ z ∈ Z, z ∈ Set.Ico (τ j0) (τ j0 + 2 * Real.pi) := by
    intro z hz
    rw [hZdef, Finset.mem_image] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    rw [Finset.mem_Icc] at hj
    refine Set.mem_Ico.mpr ⟨?_, ?_⟩
    · exact le_of_lt (lt_of_lt_of_le (hτmono (by omega : j0 < j)) (hζ1 j).le)
    · rw [← hτper j0]
      exact lt_of_lt_of_le (hζ2 j) (hτmono.monotone (by omega))
  have hZzero : ∀ z ∈ Z, D z = 0 := by
    intro z hz
    rw [hZdef, Finset.mem_image] at hz
    obtain ⟨j, _, rfl⟩ := hz
    exact hζ3 j
  have htsmem : ts ∈ Set.Ico (τ j0) (τ j0 + 2 * Real.pi) := by
    refine Set.mem_Ico.mpr ⟨hts1.le, ?_⟩
    rw [← hτper j0]
    exact lt_of_lt_of_le hτj0lt (hτmono.monotone (by omega))
  have htsnotZ : ts ∉ Z := by
    intro hz
    rw [hZdef, Finset.mem_image] at hz
    obtain ⟨j, hj, hje⟩ := hz
    rw [Finset.mem_Icc] at hj
    have : ts < ζ j := lt_of_lt_of_le hτj0lt (le_trans (hτmono.monotone (by omega)) (hζ1 j).le)
    rw [hje] at this
    exact absurd rfl (ne_of_lt this)
  have hDne : ∃ s : ℝ, D s ≠ 0 := ⟨τ j0, hDτne j0⟩
  have hfinal := TrigPolyZeroCount hDTP hDne hZmem hZzero htsmem htsnotZ hD0 hD'0
  rw [hZcard] at hfinal
  omega
